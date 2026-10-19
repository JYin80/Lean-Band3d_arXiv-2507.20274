/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltMoments1
import RBM3D.Gauss.Domination
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The probabilistic half of the CLT moment bound

Paper: arXiv:2507.20274, the proof of Lemma 5.1 `lem;CLT`: the decomposition of
`f^{far} - 𝔼 f^{far}` into the window fluctuation and the off-window part ((5.29)
`eq:boundEfar`), the `2p`-th moment `(eq:main_challenge3)`, its expansion `(eq:2p_product)` over
the regions `(eq:sumregionsforb)`, the pairing condition `(eq:pairingcond)`, the paired tuples
`(eq:2p_product_pair)` and the isolated tuples `(eq:bound_isolated)`.
Everything is at one size index `n` (no `Prec`, no `∀ n`): the union over the index set of
`STCltFarConcl` is the business of `Evolution/CltFar`, which also bounds `CltMom2.off`
by `(eq:propcalB)` and supplies `CltMom2.DomHyp` from `STGdecayW` at `u = s`.  Notation: `|x| =
zdistInf d L x`, `w = (log W)³ ℓ_s` (window), `ρ = (log W)⁴ ℓ_s` (far cutoff), `R = 10 w`
(pairing radius of `STCltIsoConcl`), cluster radius `2R = 20 w`.

**Contents** (namespace `RBM.Evol`; constants and powers of `log W` explicit):

1. The vocabulary `CltMom2.Z`, `fluc`, `off`, `BY`, `DomHyp`, `IsoHyp`, `rhs` and the six
   statements `CltMom2.BYStmt`, `DecompStmt`, `WeightStmt`, `HzuStmt`, `MomentStmt`, `TailStmt`.
   `CltMom2.IsoHyp` is the inner clause of `STCltIsoConcl` (`Induction/Step5Pins.lean`) at one
   `n`, `σ`, `p`.
2. The moment engine on two-label fields (a probability space `(Ω, P)`): `cltMom2_expand`
   (`(eq:2p_product)`), `cltMom2_moment_le` (the `2p`-th moment bound: isolated tuples by the
   hypothesis, paired tuples by the profile-normalised maximum and
   `cltMom1_paired_moment_le`), `cltMom2_markov` (Markov).
3. `cltMom2_decomp : CltMom2.DecompStmt d`.
4. `cltMom2_norm_stcltB_le : CltMom2.BYStmt d` (envelope of `𝗕`), `cltMom2_weight_le :
   CltMom2.WeightStmt d` (`(prop:ThfadC)`, `(prop:BD1)`: `M = C₅ (1 + 2^{d-1}) C₆ d`),
   `cltMom2_hzu : CltMom2.HzuStmt` (comparability at radius `20 w`, factor `4^d`).
5. `cltMom2_moment_fixed : CltMom2.MomentStmt d` (the fixed-`n` moment bound at `Y = STcltB`, `M
   = 4^d M_w`).
6. `cltMom2_tail_eventually : CltMom2.TailStmt d` (the eventual form from `STCltIsoConcl`; the
   input of `Evolution/CltFar`).

The engine follows the two-dimensional formalization, with the label replaced by the two-label
index `Fin 2 → Zd d L`; the maximum of that formalization is here the maximum of
`|Y_β| (|β₀-β₁|^{d-2}+1)` over the window labels, and the paired sum is bounded by
`cltMom1_paired_moment_le`.  Copies of private proofs: `meanFar_integrable_L` and
`meanFar_integral_fFar` (`Evolution/MeanFar.lean`) as `cltMom2_integrable_L`,
`cltMom2_integral_fFar`.

**Differences from the paper**: (i) the per-factor `≺` of the first line of
`(eq:2p_product_pair)` is the profile-normalised maximum with the tail `(Λ', q₁)` and the envelope
`CltMom2.BY`; (ii) the `O(W^{-D})` of `(eq:2p_product)` is the separate term `CltMom2.off`;
(iii) the factor `4^d` of the comparability at radius `2R` and the constant `M_w`; (iv) the moment
bound with `|𝔼 ∏ 𝕀𝔼𝗕|` and `∏ |weights|` at one `n` with explicit `Λ'`, `q₁`, `εf`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes


/-! ## 1. The vocabulary and statements -/

/-- **The weight of a two-label index `β = (β₀, β₁)` in `(eq:2p_product)`**:
`λ² Θ_t(a₁, β₀) · λ² (Θ_t(β₁, a₂) - Θ_t(β₀, a₂))` on the region `(eq:sumregionsforb)`:
`β₀` far from both `a_i` at `(log W)⁴ ℓ_s` in the orientation of `STfFar`, window `|β₀ - β₁| ≤ (log W)³ ℓ_s`;
`0` elsewhere.  The propagator is that of `STfFar`. -/
def CltMom2.Z {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (β : Fin 2 → Zd d (sz.L n)) : ℂ :=
  if Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 1) : ℕ) : ℝ) ∧
      ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s then
    (((sz.lam n ^ 2 : ℝ) : ℂ) *
        Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) (β 0)) *
      (((sz.lam n ^ 2 : ℝ) : ℂ) *
        (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 1) (a 1) -
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 0) (a 1)))
  else 0

/-- **The window fluctuation** `λ⁴ (1-s)^{-2} (λ² W^d)^{6/5} (𝕀𝔼 f^{far})_{window}` ((5.30) `eq:main_challenge3`):
`Σ_β Z_β (𝗕_β - 𝔼𝗕_β)`, with the centred factor `STcltX … false`. -/
def CltMom2.fluc {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  ∑ β : Fin 2 → Zd d (sz.L n), CltMom2.Z sz n E s t σ a β * STcltX sz n E s σ β false ω

open Classical in
/-- **The off-window part** of `f^{far} - 𝔼 f^{far}` (the `O(W^{-D})` of `(eq:2p_product)`): the sum of `STfFar` with
`𝓑` replaced by `𝓑 - 𝔼𝓑` over `|b₁ - b₂| > (log W)³ ℓ_s`.  `Evolution/CltFar` bounds it with `(eq:propcalB)`. -/
def CltMom2.off {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
    ∑ b₂ ∈ Finset.univ.filter (fun b₂ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ)),
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
        (STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] -
          ∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)) *
        (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1))

/-- **The deterministic envelope of `𝗕`**: `A^{6/5} (η_s^{-2} + Σ_β |𝒦^{(2)}_{s,σ,β}|)`, `A = λ² W^d`
(`|𝓛^{(2)}| ≤ η_s^{-2}`, `norm_Lloop_le`). -/
def CltMom2.BY {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) : ℝ :=
  (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) *
    ((etaT E s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β‖)

/-- **The per-label tail of the profile-normalised `𝗕` on the window** at one `n` (the `≺` of `(eq:propcalB)`, in the form used by `(eq:2p_product_pair)`): `P(Λ' < |𝗕_β| (|β₀-β₁|^{d-2}+1)) ≤ q₁` for every window
label `β`.  `Evolution/CltFar` supplies it from `STGdecayW` at `u = s`. -/
def CltMom2.DomHyp {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (Λ' q₁ : ℝ) : Prop :=
  ∀ β : Fin 2 → Zd d (sz.L n),
    ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s →
    sz.seqP {ω | Λ' < ‖STcltB sz n E s σ β ω‖ * (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} ≤
      ENNReal.ofReal q₁

/-- **The isolation bound at one `n`** (`(eq:bound_isolated)`): the inner clause of `STCltIsoConcl`
(`Step5Pins.lean`) with `(E n), (s n)` replaced by `E, s` and the error `W^{-D}` by `εf`. -/
def CltMom2.IsoHyp {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (p : ℕ) (εf : ℝ) : Prop :=
  ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
    (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) →
    (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s ≤
      ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
    ‖∫ ω, ∏ k : Fin (2 * p), STcltX sz n E s σ (b k) (decide (p ≤ k.val)) ω ∂(sz.seqP)‖ ≤ εf

/-- **The right side of the `2p`-th moment bound** (`(eq:main_challenge3)` at one `n`): the paired part
(centring `2^{2p}`, the profile-normalised maximum with tail `(Λ', q₁)` and envelope `BY (w^{d-2}+1)` over at most
`|Fin 2 → Zd d L|` window labels, times the cluster bound of `cltMom1_paired_moment_le` at `Mz = M`) plus the
isolated part `εf (Σ_β |Z_β|)^{2p}`. -/
def CltMom2.rhs {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (p : ℕ) (M Λ' q₁ εf : ℝ) : ℝ :=
  2 ^ (2 * p) * (Λ' ^ (2 * p) +
      (CltMom2.BY sz n E s σ *
          ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)) ^ (2 * p) *
        (Fintype.card (Fin 2 → Zd d (sz.L n)) : ℝ) * q₁) *
    (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
      ((CltMom1.Cd d * M * Real.log ((sz.W n : ℕ) : ℝ) ^ 12) ^ (2 * p) *
        (ellT (sz.L n) (sz.lam n) s ^ 4 /
          (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) +
  εf * (∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Z sz n E s t σ a β‖) ^ (2 * p)

/-- The envelope of `𝗕`. -/
def CltMom2.BYStmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool), |E| < 2 → s < 1 →
    ∀ (β : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ), ‖STcltB sz n E s σ β ω‖ ≤ CltMom2.BY sz n E s σ

/-- The decomposition `f^{far} - 𝔼 f^{far} = (1-s)²/(λ⁴ A^{6/5}) · fluc + off`. -/
def CltMom2.DecompStmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    |E| < 2 → s < 1 → 0 < sz.lam n → ∀ ω : sz.SeqΩ,
      STfFar sz n E s t σ a ω - ∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP) =
        (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
            CltMom2.fluc sz n E s t σ a ω + CltMom2.off sz n E s t σ a ω

/-- The weights of `(eq:2p_product_pair)` (`(prop:ThfadC)`, `(prop:BD1)`): `|Z_β| (|β₀-β₁|^{d-2}+1)^{-1}`
is at most `u(β₀) G_w(β₀ - β₁)` (`CltMom1.uw` with `λ = w`), with a constant `M = M(d, Λ, κ)`. -/
def CltMom2.WeightStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ M : ℝ, 0 < M ∧
    ∀ (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      |E| ≤ 2 → κ ≤ (mE E).im → 0 < sz.lam n → sz.lam n ≤ Λ → 0 ≤ t → t < 1 →
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t →
      2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) →
      ∀ β : Fin 2 → Zd d (sz.L n),
        ‖CltMom2.Z sz n E s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤
          CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s)
              (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) M (β 0) *
            CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1)

/-- The hypothesis `hzu` of `cltMom1_paired_moment_le` from the pointwise weight bound, at the cluster
radius `2R = 20 w` (comparability, `40 w ≤ ρ`), with the factor `4^d`. -/
def CltMom2.HzuStmt : Prop :=
  ∀ (d L : ℕ) [NeZero L] (a₁ a₂ : Zd d L) (w ρ M : ℝ) (z : (Fin 2 → Zd d L) → ℝ),
    2 ≤ d → 0 ≤ w → 40 * w ≤ ρ → 0 ≤ M → (∀ β, 0 ≤ z β) →
    (∀ β, z β ≤ CltMom1.uw a₁ a₂ ρ w M (β 0) * CltMom1.G d L w (β 0 - β 1)) →
    ∀ β β' : Fin 2 → Zd d L, 0 < z β → ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * w →
      z β' ≤ CltMom1.uw a₁ a₂ ρ w (4 ^ d * M) (β 0) * CltMom1.G d L w (β' 0 - β' 1)

/-- The `2p`-th moment bound `(eq:main_challenge3)` of the window fluctuation at one `n`, and Markov. -/
def CltMom2.MomentStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ M : ℝ, 0 < M ∧
    ∀ (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (p : ℕ)
      (Λ' q₁ εf : ℝ),
      1 ≤ p → |E| < 2 → κ ≤ (mE E).im → 0 < sz.lam n → sz.lam n ≤ Λ → s < 1 → 0 ≤ t → t < 1 →
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t →
      (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) →
      0 ≤ q₁ → 0 ≤ εf →
      CltMom2.DomHyp sz n E s σ Λ' q₁ → CltMom2.IsoHyp sz n E s σ p εf →
      ∫ ω, ‖CltMom2.fluc sz n E s t σ a ω‖ ^ (2 * p) ∂(sz.seqP) ≤ CltMom2.rhs sz n E s t σ a p M Λ' q₁ εf ∧
      ∀ θ : ℝ, 0 < θ → sz.seqP {ω | θ < ‖CltMom2.fluc sz n E s t σ a ω‖} ≤
        ENNReal.ofReal (CltMom2.rhs sz n E s t σ a p M Λ' q₁ εf / θ ^ (2 * p))

/-- The eventual form from `STCltIsoConcl` (`εf = W^{-D}`), for `σ₁ ≠ σ₂`; the input of `Evolution/CltFar`. -/
def CltMom2.TailStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ M : ℝ, 0 < M ∧
    ∀ (sz : Sizes d) (E s t : ℕ → ℝ), STCltIsoConcl sz E s t →
      ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ (a : Fin 2 → Zd d (sz.L n)) (Λ' q₁ θ : ℝ),
          |E n| < 2 → κ ≤ (mE (E n)).im → 0 < sz.lam n → sz.lam n ≤ Λ → s n < 1 → 0 ≤ t n → t n < 1 →
          sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n →
          (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) →
          0 ≤ q₁ → CltMom2.DomHyp sz n (E n) (s n) σ Λ' q₁ → 0 < θ →
          sz.seqP {ω | θ < ‖CltMom2.fluc sz n (E n) (s n) (t n) σ a ω‖} ≤
            ENNReal.ofReal (CltMom2.rhs sz n (E n) (s n) (t n) σ a p M Λ' q₁ (((sz.W n : ℕ) : ℝ) ^ (-D)) /
              θ ^ (2 * p))

/-! ## 2. The moment engine on two-label fields -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {d L : ℕ} [NeZero L]

/-- The centred factor `X_k(b)` of the tuple product of `(eq:2p_product)`: `Y_β - 𝔼Y_β` (`cj = false`) or its
complex conjugate (`cj = true`); the shape of `STcltX` (`Step5Pins.lean`) for an arbitrary field `Y`. -/
def CltMom2.X (P : Measure Ω) (Y : (Fin 2 → Zd d L) → Ω → ℂ) (β : Fin 2 → Zd d L) (cj : Bool) (ω : Ω) : ℂ :=
  if cj then (starRingEnd ℂ) (Y β ω - ∫ ω', Y β ω' ∂P) else Y β ω - ∫ ω', Y β ω' ∂P

/-- The tuple product `∏_{k<2p} X_k(b)`, conjugated from `k = p` on (`decide (p ≤ k.val)`, the convention of `STcltX`). -/
private abbrev cltMom2_tuple (P : Measure Ω) (Y : (Fin 2 → Zd d L) → Ω → ℂ) (p : ℕ)
    (b : Fin (2 * p) → (Fin 2 → Zd d L)) (ω : Ω) : ℂ :=
  ∏ k : Fin (2 * p), CltMom2.X P Y (b k) (decide (p ≤ k.val)) ω

/-- The product split, with the convention `p ≤ k`. -/
private theorem cltMom2_prod_split {M : Type*} [CommMonoid M] (p : ℕ) (A B : M) :
    ∏ k : Fin (2 * p), (if p ≤ k.val then B else A) = A ^ p * B ^ p := by
  have h : ∀ k : Fin (2 * p), (if p ≤ k.val then B else A) = (if k.val < p then A else B) := by
    intro k
    by_cases hk : p ≤ k.val
    · simp [hk, not_lt.2 hk]
    · simp [hk, not_le.1 hk]
  rw [Finset.prod_congr rfl fun k _ => h k]
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < p then A else B) (2 * p), two_mul,
    Finset.prod_range_add]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ => A) (fun i hi => by simp [Finset.mem_range.1 hi])]
    simp
  · rw [Finset.prod_congr rfl (g := fun _ => B) (fun i _ => by simp)]
    simp

variable {P : Measure Ω} {Y : (Fin 2 → Zd d L) → Ω → ℂ} {B : ℝ}

private theorem cltMom2_Yt_meas (hYm : ∀ β, Measurable (Y β)) (β : Fin 2 → Zd d L) :
    Measurable fun ω => Y β ω - ∫ ω', Y β ω' ∂P := (hYm β).sub measurable_const

private theorem cltMom2_int_norm_le [IsProbabilityMeasure P] (hYB : ∀ β ω, ‖Y β ω‖ ≤ B)
    (β : Fin 2 → Zd d L) : ‖∫ ω', Y β ω' ∂P‖ ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := Y β) (C := B)
    (Filter.Eventually.of_forall fun ω => hYB β ω)
  simpa using this

private theorem cltMom2_X_norm (β : Fin 2 → Zd d L) (cj : Bool) (ω : Ω) :
    ‖CltMom2.X P Y β cj ω‖ = ‖Y β ω - ∫ ω', Y β ω' ∂P‖ := by
  unfold CltMom2.X
  split_ifs
  · exact RCLike.norm_conj _
  · rfl

private theorem cltMom2_X_meas (hYm : ∀ β, Measurable (Y β)) (β : Fin 2 → Zd d L) (cj : Bool) :
    Measurable (CltMom2.X P Y β cj) := by
  cases cj
  · rw [show CltMom2.X P Y β false = fun ω => Y β ω - ∫ ω', Y β ω' ∂P from funext fun ω => by simp [CltMom2.X]]
    exact cltMom2_Yt_meas hYm β
  · rw [show CltMom2.X P Y β true = fun ω => (starRingEnd ℂ) (Y β ω - ∫ ω', Y β ω' ∂P) from
      funext fun ω => by simp [CltMom2.X]]
    exact Complex.continuous_conj.measurable.comp (cltMom2_Yt_meas hYm (P := P) β)

private theorem cltMom2_tuple_meas (hYm : ∀ β, Measurable (Y β)) (p : ℕ) (b : Fin (2 * p) → (Fin 2 → Zd d L)) :
    Measurable (cltMom2_tuple P Y p b) :=
  Finset.measurable_prod _ fun _ _ => cltMom2_X_meas hYm _ _

/-- The pointwise bound of the tuple product with a bound `c k` for each factor. -/
private theorem cltMom2_tuple_norm_le (p : ℕ) (b : Fin (2 * p) → (Fin 2 → Zd d L)) (ω : Ω)
    (c : Fin (2 * p) → ℝ) (hc : ∀ k, ‖Y (b k) ω - ∫ ω', Y (b k) ω' ∂P‖ ≤ c k) :
    ‖cltMom2_tuple P Y p b ω‖ ≤ ∏ k, c k := by
  unfold cltMom2_tuple
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => by
    rw [cltMom2_X_norm]; exact hc k

private theorem cltMom2_tuple_int [IsProbabilityMeasure P] (hYm : ∀ β, Measurable (Y β))
    (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (p : ℕ) (b : Fin (2 * p) → (Fin 2 → Zd d L)) :
    Integrable (cltMom2_tuple P Y p b) P := by
  refine Integrable.of_bound (cltMom2_tuple_meas hYm p b).aestronglyMeasurable (∏ _k : Fin (2 * p), (B + B))
    (Filter.Eventually.of_forall fun ω => cltMom2_tuple_norm_le p b ω (fun _ => B + B) fun k => ?_)
  calc ‖Y (b k) ω - ∫ ω', Y (b k) ω' ∂P‖ ≤ ‖Y (b k) ω‖ + ‖∫ ω', Y (b k) ω' ∂P‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hYB _ _) (cltMom2_int_norm_le hYB _)

/-- **`(eq:2p_product)`: the `2p`-th moment of the window fluctuation expands into the tuple
expectations** (the label is the two-label index `Fin 2 → Zd d L`): for a bounded measurable field `Y` on a
probability space and a row `Z`,
`𝔼 |Σ_β Z_β (Y_β - 𝔼Y_β)|^{2p} ≤ Σ_{b : Fin (2p) → (Fin 2 → Zd d L)} (∏_k |Z_{b_k}|) |𝔼 ∏_k X_k(b)|`,
where `X_k(b) = Y_{b_k} - 𝔼Y_{b_k}` for `k < p` and its conjugate for `p ≤ k`. -/
theorem cltMom2_expand [IsProbabilityMeasure P] (hYm : ∀ β, Measurable (Y β)) (hYB : ∀ β ω, ‖Y β ω‖ ≤ B)
    (Z : (Fin 2 → Zd d L) → ℂ) (p : ℕ) :
    ∫ ω, ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖ ^ (2 * p) ∂P ≤
      ∑ b : Fin (2 * p) → (Fin 2 → Zd d L), (∏ k, ‖Z (b k)‖) *
        ‖∫ ω, ∏ k : Fin (2 * p), CltMom2.X P Y (b k) (decide (p ≤ k.val)) ω ∂P‖ := by
  classical
  set S : Ω → ℂ := fun ω => ∑ x, Z x * (Y x ω - ∫ ω', Y x ω' ∂P) with hS
  have h1 : ∀ ω, (((‖S ω‖ ^ (2 * p) : ℝ)) : ℂ) = ∑ b : Fin (2 * p) → (Fin 2 → Zd d L),
      (∏ k : Fin (2 * p), (if p ≤ k.val then (starRingEnd ℂ) (Z (b k)) else Z (b k))) *
        cltMom2_tuple P Y p b ω := by
    intro ω
    have hA : (((‖S ω‖ ^ (2 * p) : ℝ)) : ℂ) = ∏ k : Fin (2 * p),
        (if p ≤ k.val then (starRingEnd ℂ) (S ω) else S ω) := by
      rw [cltMom2_prod_split, ← mul_pow, mul_comm, Complex.mul_conj', pow_mul]
      push_cast
      ring
    have hB : ∀ k : Fin (2 * p), (if p ≤ k.val then (starRingEnd ℂ) (S ω) else S ω) =
        ∑ x : Fin 2 → Zd d L, (if p ≤ k.val then (starRingEnd ℂ) (Z x) else Z x) *
          CltMom2.X P Y x (decide (p ≤ k.val)) ω := by
      intro k
      by_cases hk : p ≤ k.val
      · simp [hk, hS, map_sum, CltMom2.X]
      · simp [hk, hS, CltMom2.X]
    rw [hA, Finset.prod_congr rfl fun k _ => hB k]
    rw [Finset.prod_univ_sum (fun _ : Fin (2 * p) => (Finset.univ : Finset (Fin 2 → Zd d L)))
      (fun k x => (if p ≤ k.val then (starRingEnd ℂ) (Z x) else Z x) *
          CltMom2.X P Y x (decide (p ≤ k.val)) ω)]
    rw [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.prod_mul_distrib]
  have hint : ∀ b : Fin (2 * p) → (Fin 2 → Zd d L), Integrable (fun ω =>
      (∏ k : Fin (2 * p), (if p ≤ k.val then (starRingEnd ℂ) (Z (b k)) else Z (b k))) *
        cltMom2_tuple P Y p b ω) P :=
    fun b => (cltMom2_tuple_int hYm hYB p b).const_mul _
  have h2 : ((∫ ω, ‖S ω‖ ^ (2 * p) ∂P : ℝ) : ℂ) = ∑ b : Fin (2 * p) → (Fin 2 → Zd d L),
      (∏ k : Fin (2 * p), (if p ≤ k.val then (starRingEnd ℂ) (Z (b k)) else Z (b k))) *
        ∫ ω, cltMom2_tuple P Y p b ω ∂P := by
    rw [← integral_complex_ofReal]
    simp_rw [h1]
    rw [integral_finsetSum _ (fun b _ => hint b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
  have h3 : ∫ ω, ‖S ω‖ ^ (2 * p) ∂P = ‖((∫ ω, ‖S ω‖ ^ (2 * p) ∂P : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun ω => by positivity)]
  rw [h3, h2]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_prod]
  refine le_of_eq (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  split_ifs
  · exact RCLike.norm_conj _
  · rfl


/-! ### The profile-normalised maximum over the window -/

private theorem cltMom2_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  simp [zdistInf]

/-- The profile weight `q(β) = |β₀ - β₁|_∞^{d-2} + 1` of `(eq:2p_product_pair)`: its inverse is the profile `π(β)`. -/
private def cltMom2_q (β : Fin 2 → Zd d L) : ℝ := ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1

private theorem cltMom2_q_pos (β : Fin 2 → Zd d L) : 0 < cltMom2_q β := by
  unfold cltMom2_q; positivity

/-- The window predicate `|β₀ - β₁|_∞ ≤ w` of `(eq:sumregionsforb)`. -/
private def cltMom2_win (w : ℝ) (β : Fin 2 → Zd d L) : Prop := ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ≤ w

/-- The profile-normalised maximum `max_{β in the window} |Y_β| q(β)` (restricted to the window labels, with the weight `q`; `0` off the window). -/
private def cltMom2_ymax (w : ℝ) (Y : (Fin 2 → Zd d L) → Ω → ℂ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun β : Fin 2 → Zd d L =>
    open Classical in if cltMom2_win w β then ‖Y β ω‖ * cltMom2_q β else 0

private theorem cltMom2_term_nonneg (w : ℝ) (Y : (Fin 2 → Zd d L) → Ω → ℂ) (ω : Ω) (β : Fin 2 → Zd d L) :
    0 ≤ (open Classical in if cltMom2_win w β then ‖Y β ω‖ * cltMom2_q β else 0) := by
  classical
  split_ifs
  · exact mul_nonneg (norm_nonneg _) (cltMom2_q_pos β).le
  · exact le_rfl

private theorem cltMom2_ymax_meas {w : ℝ} (hYm : ∀ β, Measurable (Y β)) : Measurable (cltMom2_ymax w Y) := by
  classical
  have := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin 2 → Zd d L))) Finset.univ_nonempty
    (f := fun β ω => if cltMom2_win w β then ‖Y β ω‖ * cltMom2_q β else 0) fun β _ => by
      by_cases h : cltMom2_win w β
      · simp only [h, ite_true]; exact (hYm β).norm.mul_const _
      · simp only [h, ite_false]; exact measurable_const
  convert this using 1
  ext ω
  simp [cltMom2_ymax, Finset.sup'_apply]

private theorem cltMom2_ymax_nonneg (w : ℝ) (ω : Ω) : 0 ≤ cltMom2_ymax w Y ω :=
  (cltMom2_term_nonneg w Y ω 0).trans (Finset.le_sup' (f := fun β : Fin 2 → Zd d L =>
    open Classical in if cltMom2_win w β then ‖Y β ω‖ * cltMom2_q β else 0) (Finset.mem_univ _))

/-- On the window the profile-normalised norm is below the maximum. -/
private theorem cltMom2_le_ymax {w : ℝ} {β : Fin 2 → Zd d L} (h : cltMom2_win w β) (ω : Ω) :
    ‖Y β ω‖ * cltMom2_q β ≤ cltMom2_ymax w Y ω := by
  classical
  calc ‖Y β ω‖ * cltMom2_q β = (if cltMom2_win w β then ‖Y β ω‖ * cltMom2_q β else 0) := by simp [h]
    _ ≤ cltMom2_ymax w Y ω := Finset.le_sup' (f := fun β : Fin 2 → Zd d L =>
      open Classical in if cltMom2_win w β then ‖Y β ω‖ * cltMom2_q β else 0) (Finset.mem_univ β)

/-- `‖Y_β‖ ≤ π(β) · ymax` on the window, `π = 1 / q`. -/
private theorem cltMom2_norm_le_ymax {w : ℝ} {β : Fin 2 → Zd d L} (h : cltMom2_win w β) (ω : Ω) :
    ‖Y β ω‖ ≤ (1 / cltMom2_q β) * cltMom2_ymax w Y ω := by
  have hq := cltMom2_q_pos β
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hq]
  exact cltMom2_le_ymax h ω

/-- The a.s. bound `ymax ≤ B (w^{d-2} + 1)` (the profile weight `q ≤ w^{d-2}+1` on the window). -/
private theorem cltMom2_ymax_le {w : ℝ} (hw : 0 ≤ w) (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (ω : Ω) :
    cltMom2_ymax w Y ω ≤ B * (w ^ (d - 2) + 1) := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hYB 0 ω)
  refine Finset.sup'_le _ _ fun β _ => ?_
  split_ifs with h
  · have hq : cltMom2_q β ≤ w ^ (d - 2) + 1 := by
      unfold cltMom2_q
      have := pow_le_pow_left₀ (Nat.cast_nonneg (zdistInf d L (β 0 - β 1))) h (d - 2)
      linarith
    calc ‖Y β ω‖ * cltMom2_q β ≤ B * cltMom2_q β := mul_le_mul_of_nonneg_right (hYB β ω) (cltMom2_q_pos β).le
      _ ≤ B * (w ^ (d - 2) + 1) := mul_le_mul_of_nonneg_left hq hB
  · positivity

private theorem cltMom2_ymax_int_pow {w : ℝ} (hw : 0 ≤ w) [IsProbabilityMeasure P] (hYm : ∀ β, Measurable (Y β))
    (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (q : ℕ) :
    Integrable (fun ω => cltMom2_ymax w Y ω ^ q) P := by
  refine Integrable.of_bound ((cltMom2_ymax_meas hYm).pow_const q).aestronglyMeasurable ((B * (w ^ (d - 2) + 1)) ^ q)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (cltMom2_ymax_nonneg w ω) _)]
  exact pow_le_pow_left₀ (cltMom2_ymax_nonneg w ω) (cltMom2_ymax_le hw hYB ω) q

/-- `(x + m)^q ≤ 2^q (x^q + m^q) / 2`. -/
private theorem cltMom2_pow_add_le (x m : ℝ) (hx : 0 ≤ x) (hm : 0 ≤ m) (q : ℕ) :
    (x + m) ^ q ≤ 2 ^ q * (x ^ q + m ^ q) / 2 := by
  have h := (convexOn_pow (𝕜 := ℝ) q).2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hm)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have h2 : (x + m) ^ q = 2 ^ q * (1 / 2 * x + 1 / 2 * m) ^ q := by
    rw [← mul_pow]; congr 1; ring
  rw [h2]
  calc 2 ^ q * (1 / 2 * x + 1 / 2 * m) ^ q ≤ 2 ^ q * (1 / 2 * x ^ q + 1 / 2 * m ^ q) := by gcongr
    _ = 2 ^ q * (x ^ q + m ^ q) / 2 := by ring

/-- **The centred tuple, on the window** (centring `2^{2p}`, Jensen; with the profile): if all labels of `b` are in the window, then
`|𝔼 ∏_k X_k(b)| ≤ (∏_k π(b_k)) · 2^{2p} 𝔼 ymax^{2p}`, `π = 1/q`, `cltMom2_ymax` the profile-normalised
maximum. -/
private theorem cltMom2_tuple_le [IsProbabilityMeasure P] {w : ℝ} (hw : 0 ≤ w) (hYm : ∀ β, Measurable (Y β))
    (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (p : ℕ) (b : Fin (2 * p) → (Fin 2 → Zd d L)) (hb : ∀ k, cltMom2_win w (b k)) :
    ‖∫ ω, cltMom2_tuple P Y p b ω ∂P‖ ≤
      (∏ k, (1 / cltMom2_q (b k))) * (2 ^ (2 * p) * ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P) := by
  set m : ℝ := ∫ ω, cltMom2_ymax w Y ω ∂P with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ω => cltMom2_ymax_nonneg w ω
  have hMint : Integrable (cltMom2_ymax w Y) P := by
    simpa using cltMom2_ymax_int_pow (P := P) hw hYm hYB 1
  have hYint : ∀ x, Integrable (fun ω => ‖Y x ω‖) P := fun x =>
    Integrable.of_bound (hYm x).norm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hYB x ω)
  have hint_le : ∀ x, cltMom2_win w x → ‖∫ ω', Y x ω' ∂P‖ ≤ (1 / cltMom2_q x) * m := fun x hx =>
    (norm_integral_le_integral_norm _).trans (by
      calc ∫ ω, ‖Y x ω‖ ∂P ≤ ∫ ω, (1 / cltMom2_q x) * cltMom2_ymax w Y ω ∂P :=
            integral_mono (hYint x) (hMint.const_mul _) fun ω => cltMom2_norm_le_ymax hx ω
        _ = (1 / cltMom2_q x) * m := by rw [integral_const_mul])
  set c : ℝ := ∏ k, (1 / cltMom2_q (b k)) with hc
  have hc0 : 0 ≤ c := Finset.prod_nonneg fun k _ => (one_div_pos.2 (cltMom2_q_pos _)).le
  have hpt : ∀ ω, ‖cltMom2_tuple P Y p b ω‖ ≤ c * (cltMom2_ymax w Y ω + m) ^ (2 * p) := by
    intro ω
    refine (cltMom2_tuple_norm_le p b ω (fun k => (1 / cltMom2_q (b k)) * (cltMom2_ymax w Y ω + m)) fun k => ?_).trans
      (le_of_eq ?_)
    · calc ‖Y (b k) ω - ∫ ω', Y (b k) ω' ∂P‖ ≤ ‖Y (b k) ω‖ + ‖∫ ω', Y (b k) ω' ∂P‖ := norm_sub_le _ _
        _ ≤ (1 / cltMom2_q (b k)) * cltMom2_ymax w Y ω + (1 / cltMom2_q (b k)) * m :=
            add_le_add (cltMom2_norm_le_ymax (hb k) ω) (hint_le _ (hb k))
        _ = (1 / cltMom2_q (b k)) * (cltMom2_ymax w Y ω + m) := by ring
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsumint : Integrable (fun ω => (cltMom2_ymax w Y ω + m) ^ (2 * p)) P := by
    refine Integrable.of_bound (((cltMom2_ymax_meas hYm).add_const m).pow_const _).aestronglyMeasurable
      ((B * (w ^ (d - 2) + 1) + m) ^ (2 * p)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (add_nonneg (cltMom2_ymax_nonneg w ω) hm0) _)]
    exact pow_le_pow_left₀ (add_nonneg (cltMom2_ymax_nonneg w ω) hm0)
      (add_le_add_left (cltMom2_ymax_le hw hYB ω) m) _
  have hjensen : m ^ (2 * p) ≤ ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P := by
    have := (convexOn_pow (𝕜 := ℝ) (2 * p)).map_integral_le (μ := P) (f := cltMom2_ymax w Y)
      (continuousOn_pow _) isClosed_Ici
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (cltMom2_ymax_nonneg w ω)) hMint
      (cltMom2_ymax_int_pow hw hYm hYB _)
    simpa [hm] using this
  have hI : ∫ ω, (cltMom2_ymax w Y ω + m) ^ (2 * p) ∂P ≤ 2 ^ (2 * p) * ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P := by
    calc ∫ ω, (cltMom2_ymax w Y ω + m) ^ (2 * p) ∂P
        ≤ ∫ ω, 2 ^ (2 * p) * (cltMom2_ymax w Y ω ^ (2 * p) + m ^ (2 * p)) / 2 ∂P :=
          integral_mono hsumint (by
            exact ((cltMom2_ymax_int_pow hw hYm hYB _).add (integrable_const _)).const_mul _ |>.div_const _)
            fun ω => cltMom2_pow_add_le _ _ (cltMom2_ymax_nonneg w ω) hm0 _
      _ = 2 ^ (2 * p) * ((∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P) + m ^ (2 * p)) / 2 := by
          rw [integral_div, integral_const_mul, integral_add (cltMom2_ymax_int_pow hw hYm hYB _)
            (integrable_const _)]
          simp
      _ ≤ 2 ^ (2 * p) * ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P := by
          nlinarith [hjensen, pow_pos (two_pos : (0:ℝ) < 2) (2 * p)]
  calc ‖∫ ω, cltMom2_tuple P Y p b ω ∂P‖ ≤ ∫ ω, ‖cltMom2_tuple P Y p b ω‖ ∂P :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, c * (cltMom2_ymax w Y ω + m) ^ (2 * p) ∂P :=
        integral_mono ((cltMom2_tuple_int hYm hYB p b).norm) (hsumint.const_mul _) hpt
    _ = c * ∫ ω, (cltMom2_ymax w Y ω + m) ^ (2 * p) ∂P := by rw [integral_const_mul]
    _ ≤ c * (2 ^ (2 * p) * ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P) := mul_le_mul_of_nonneg_left hI hc0

private theorem cltMom2_even_pow_nonneg (x : ℝ) (p : ℕ) : 0 ≤ x ^ (2 * p) := by
  rw [pow_mul]; positivity

/-- **The expectation of the maximum** : from the per-label tail `P{Λ' < |Y_β| q(β)} ≤ q₁` on the window and the envelope `|Y_β| ≤ B`,
`𝔼 ymax^{2p} ≤ Λ'^{2p} + (B (w^{d-2}+1))^{2p} · |labels| · q₁`. -/
private theorem cltMom2_Emax_pow_le [IsProbabilityMeasure P] {w : ℝ} (hw : 0 ≤ w) (hYm : ∀ β, Measurable (Y β))
    (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (p : ℕ) (Λ' q₁ : ℝ) (hq₁ : 0 ≤ q₁)
    (hdom : ∀ β, cltMom2_win w β → P {ω | Λ' < ‖Y β ω‖ * cltMom2_q β} ≤ ENNReal.ofReal q₁) :
    ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P ≤
      Λ' ^ (2 * p) + (B * (w ^ (d - 2) + 1)) ^ (2 * p) * ((Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) := by
  classical
  set B' : ℝ := B * (w ^ (d - 2) + 1) with hB'
  have hΛ0 : 0 ≤ Λ' ^ (2 * p) := cltMom2_even_pow_nonneg _ _
  have hcard : (1 : ℝ) ≤ (Fintype.card (Fin 2 → Zd d L) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rcases le_or_gt 0 Λ' with hΛ | hΛ
  · set bad : Set Ω := {ω | Λ' < cltMom2_ymax w Y ω} with hbad
    have hbadm : MeasurableSet bad := measurableSet_lt measurable_const (cltMom2_ymax_meas hYm)
    have hpt : ∀ ω, cltMom2_ymax w Y ω ^ (2 * p) ≤ Λ' ^ (2 * p) + bad.indicator (fun _ => B' ^ (2 * p)) ω := by
      intro ω
      by_cases hω : ω ∈ bad
      · rw [Set.indicator_of_mem hω]
        have : cltMom2_ymax w Y ω ^ (2 * p) ≤ B' ^ (2 * p) :=
          pow_le_pow_left₀ (cltMom2_ymax_nonneg w ω) (cltMom2_ymax_le hw hYB ω) _
        linarith
      · rw [Set.indicator_of_notMem hω]
        have hle : cltMom2_ymax w Y ω ≤ Λ' := not_lt.1 hω
        have : cltMom2_ymax w Y ω ^ (2 * p) ≤ Λ' ^ (2 * p) :=
          pow_le_pow_left₀ (cltMom2_ymax_nonneg w ω) hle _
        linarith
    have hint2 : Integrable (fun ω => Λ' ^ (2 * p) + bad.indicator (fun _ => B' ^ (2 * p)) ω) P :=
      (integrable_const _).add ((integrable_const _).indicator hbadm)
    have hbadP : P.real bad ≤ (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁ := by
      have hsub : bad ⊆ ⋃ β : Fin 2 → Zd d L, {ω | cltMom2_win w β ∧ Λ' < ‖Y β ω‖ * cltMom2_q β} := by
        intro ω hω
        obtain ⟨b₀, _, hb₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (Fin 2 → Zd d L)).Nonempty)
          (fun β : Fin 2 → Zd d L => if cltMom2_win w β then ‖Y β ω‖ * cltMom2_q β else 0)
        have h1 : Λ' < cltMom2_ymax w Y ω := hω
        have h2 : cltMom2_ymax w Y ω = (if cltMom2_win w b₀ then ‖Y b₀ ω‖ * cltMom2_q b₀ else 0) := hb₀
        rw [h2] at h1
        refine Set.mem_iUnion.2 ⟨b₀, ?_⟩
        by_cases hwb : cltMom2_win w b₀
        · simp only [hwb, ↓reduceIte] at h1
          exact ⟨hwb, h1⟩
        · simp only [hwb, ↓reduceIte] at h1
          exact absurd h1 (not_lt.2 hΛ)
      have hone : ∀ β : Fin 2 → Zd d L, P.real {ω | cltMom2_win w β ∧ Λ' < ‖Y β ω‖ * cltMom2_q β} ≤ q₁ := by
        intro β
        by_cases hwb : cltMom2_win w β
        · have hset : {ω | cltMom2_win w β ∧ Λ' < ‖Y β ω‖ * cltMom2_q β} = {ω | Λ' < ‖Y β ω‖ * cltMom2_q β} := by
            ext ω; simp [hwb]
          rw [hset, measureReal_def]
          calc (P {ω | Λ' < ‖Y β ω‖ * cltMom2_q β}).toReal ≤ (ENNReal.ofReal q₁).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdom β hwb)
            _ = q₁ := ENNReal.toReal_ofReal hq₁
        · have hset : {ω | cltMom2_win w β ∧ Λ' < ‖Y β ω‖ * cltMom2_q β} = ∅ := by
            ext ω; simp [hwb]
          rw [hset]; simpa using hq₁
      calc P.real bad ≤ P.real (⋃ β : Fin 2 → Zd d L, {ω | cltMom2_win w β ∧ Λ' < ‖Y β ω‖ * cltMom2_q β}) :=
            measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ ∑ β : Fin 2 → Zd d L, P.real {ω | cltMom2_win w β ∧ Λ' < ‖Y β ω‖ * cltMom2_q β} :=
            measureReal_iUnion_fintype_le _
        _ ≤ ∑ _β : Fin 2 → Zd d L, q₁ := Finset.sum_le_sum fun β _ => hone β
        _ = (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁ := by simp
    calc ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P
        ≤ ∫ ω, (Λ' ^ (2 * p) + bad.indicator (fun _ => B' ^ (2 * p)) ω) ∂P :=
          integral_mono (cltMom2_ymax_int_pow hw hYm hYB _) hint2 hpt
      _ = Λ' ^ (2 * p) + P.real bad * B' ^ (2 * p) := by
          rw [integral_add (integrable_const _) ((integrable_const _).indicator hbadm),
            integral_const, integral_indicator_const _ hbadm]
          simp
      _ ≤ Λ' ^ (2 * p) + ((Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) * B' ^ (2 * p) := by
          gcongr
          exact cltMom2_even_pow_nonneg _ _
      _ = Λ' ^ (2 * p) + B' ^ (2 * p) * ((Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) := by ring
  · -- `Λ' < 0`: the event of the window label `0` is everything, so `q₁ ≥ 1`
    have hwin0 : cltMom2_win w (0 : Fin 2 → Zd d L) := by
      unfold cltMom2_win
      simp only [Pi.zero_apply, sub_self, cltMom2_zdistInf_zero, Nat.cast_zero]
      exact hw
    have hset : {ω | Λ' < ‖Y 0 ω‖ * cltMom2_q (0 : Fin 2 → Zd d L)} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hΛ (mul_nonneg (norm_nonneg _) (cltMom2_q_pos _).le)
    have h1 := hdom 0 hwin0
    rw [hset, measure_univ] at h1
    have hq1 : (1 : ℝ) ≤ q₁ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal hq₁, ENNReal.toReal_one] at this
    have hcq : (1 : ℝ) ≤ (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁ := by nlinarith
    calc ∫ ω, cltMom2_ymax w Y ω ^ (2 * p) ∂P ≤ ∫ ω, B' ^ (2 * p) ∂P :=
          integral_mono (cltMom2_ymax_int_pow hw hYm hYB _) (integrable_const _) fun ω =>
            pow_le_pow_left₀ (cltMom2_ymax_nonneg w ω) (cltMom2_ymax_le hw hYB ω) _
      _ = B' ^ (2 * p) := by simp
      _ ≤ B' ^ (2 * p) * ((Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) := by
          have : 0 ≤ B' ^ (2 * p) := cltMom2_even_pow_nonneg _ _
          nlinarith
      _ ≤ Λ' ^ (2 * p) + B' ^ (2 * p) * ((Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) := by linarith


/-- **The `2p`-th moment bound of the window fluctuation** (`(eq:main_challenge3)`, at one `n`; on two-label indices with the profile `π(β) = (|β₀-β₁|^{d-2}+1)⁻¹`, and
`cltMom1_paired_moment_le` for the paired tuples). Let `lw ≥ 1`, `ℓ ≥ 1`, `w = lw³ ℓ`, `Y` a bounded
(`|Y_β| ≤ B`) measurable field, `Z_β = 0` off the window `|β₀-β₁| ≤ w`, the weights
`z_β = |Z_β| π(β)` satisfy `hzu` (comparability at the cluster radius `20 w`), the tail
`P{Λ' < |Y_β| q(β)} ≤ q₁` holds on the window (`q = π⁻¹`), and `|𝔼 ∏ X_k(b)| ≤ εf` for every
isolated window tuple (`(eq:bound_isolated)`). Then
`𝔼|Σ_β Z_β (Y_β - 𝔼Y_β)|^{2p} ≤ 2^{2p} (Λ'^{2p} + (B (w^{d-2}+1))^{2p} |labels| q₁) · PB + εf (Σ_β |Z_β|)^{2p}`,
`PB` the right side of `cltMom1_paired_moment_le`. -/
theorem cltMom2_moment_le [IsProbabilityMeasure P] (hd : 3 ≤ d) (p : ℕ) {lw ℓ Mz Λ' q₁ εf : ℝ}
    (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ) (hMz : 0 ≤ Mz) (hq₁ : 0 ≤ q₁) (hεf : 0 ≤ εf) (a₁ a₂ : Zd d L)
    (hYm : ∀ β, Measurable (Y β)) (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (Z : (Fin 2 → Zd d L) → ℂ)
    (hZ : ∀ β : Fin 2 → Zd d L, lw ^ 3 * ℓ < ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) → Z β = 0)
    (hzu : ∀ β β' : Fin 2 → Zd d L,
      0 < ‖Z β‖ * (1 / (((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) →
      ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (lw ^ 3 * ℓ) →
      ‖Z β'‖ * (1 / (((zdistInf d L (β' 0 - β' 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤
        CltMom1.uw a₁ a₂ (lw ^ 4 * ℓ) (lw ^ 3 * ℓ) Mz (β 0) * CltMom1.G d L (lw ^ 3 * ℓ) (β' 0 - β' 1))
    (hdom : ∀ β : Fin 2 → Zd d L, ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ≤ lw ^ 3 * ℓ →
      P {ω | Λ' < ‖Y β ω‖ * (((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} ≤ ENNReal.ofReal q₁)
    (hiso : ∀ b : Fin (2 * p) → (Fin 2 → Zd d L),
      (∀ k, ((zdistInf d L ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤ lw ^ 3 * ℓ) →
      (∃ i, ∀ j, j ≠ i → 10 * lw ^ 3 * ℓ ≤ ((zdistInf d L ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
      ‖∫ ω, ∏ k : Fin (2 * p), CltMom2.X P Y (b k) (decide (p ≤ k.val)) ω ∂P‖ ≤ εf) :
    ∫ ω, ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖ ^ (2 * p) ∂P ≤
      2 ^ (2 * p) * (Λ' ^ (2 * p) + (B * ((lw ^ 3 * ℓ) ^ (d - 2) + 1)) ^ (2 * p) *
          (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) *
        (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
          ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
            (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) +
      εf * (∑ β, ‖Z β‖) ^ (2 * p) := by
  classical
  have hw1 : 1 ≤ lw ^ 3 * ℓ := cltMom1_scale_one_le hlw hℓ
  have hw0 : 0 ≤ lw ^ 3 * ℓ := by linarith
  set z : (Fin 2 → Zd d L) → ℝ := fun β => ‖Z β‖ * (1 / cltMom2_q β) with hzdef
  have hz0 : ∀ β, 0 ≤ z β := fun β => mul_nonneg (norm_nonneg _) (one_div_pos.2 (cltMom2_q_pos β)).le
  set Q : ℝ := 2 ^ (2 * p) * ∫ ω, cltMom2_ymax (lw ^ 3 * ℓ) Y ω ^ (2 * p) ∂P with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg (by positivity) (integral_nonneg fun ω => cltMom2_even_pow_nonneg _ _)
  set wt : (Fin (2 * p) → (Fin 2 → Zd d L)) → ℝ := fun b => ∏ k, ‖Z (b k)‖ with hwt
  have hwt0 : ∀ b, 0 ≤ wt b := fun b => Finset.prod_nonneg fun k _ => norm_nonneg _
  have hbd : ∀ b : Fin (2 * p) → (Fin 2 → Zd d L), wt b * ‖∫ ω, cltMom2_tuple P Y p b ω ∂P‖ ≤
      εf * wt b + Q * (if CltMom1.Paired (10 * (lw ^ 3 * ℓ)) b then ∏ k, z (b k) else 0) := by
    intro b
    have hP0 : 0 ≤ Q * (if CltMom1.Paired (10 * (lw ^ 3 * ℓ)) b then ∏ k, z (b k) else 0) := by
      refine mul_nonneg hQ0 ?_
      split_ifs
      · exact Finset.prod_nonneg fun k _ => hz0 _
      · exact le_rfl
    have hε0 : 0 ≤ εf * wt b := mul_nonneg hεf (hwt0 b)
    by_cases hwb : wt b = 0
    · rw [hwb]; linarith
    · have hbw : ∀ k, cltMom2_win (lw ^ 3 * ℓ) (b k) := by
        intro k
        by_contra hk
        have hZk : Z (b k) = 0 := hZ _ (not_le.1 hk)
        exact hwb (Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hZk]))
      by_cases hP : CltMom1.Paired (10 * (lw ^ 3 * ℓ)) b
      · simp only [hP, ↓reduceIte]
        have h1 := cltMom2_tuple_le (P := P) hw0 hYm hYB p b hbw
        calc wt b * ‖∫ ω, cltMom2_tuple P Y p b ω ∂P‖
            ≤ wt b * ((∏ k, (1 / cltMom2_q (b k))) * Q) := mul_le_mul_of_nonneg_left h1 (hwt0 b)
          _ = Q * ∏ k, z (b k) := by
              simp only [hwt, hzdef]
              rw [Finset.prod_mul_distrib]; ring
          _ ≤ εf * wt b + Q * ∏ k, z (b k) := by linarith
      · simp only [hP, ↓reduceIte]
        obtain ⟨i, hi⟩ := (cltMom1_not_paired_iff (10 * (lw ^ 3 * ℓ)) b).1 hP
        have hiso' := hiso b hbw ⟨i, fun j hj => by
          have := hi j hj
          rwa [← mul_assoc] at this⟩
        have : wt b * ‖∫ ω, cltMom2_tuple P Y p b ω ∂P‖ ≤ wt b * εf :=
          mul_le_mul_of_nonneg_left hiso' (hwt0 b)
        linarith
  have hsumw : ∑ b : Fin (2 * p) → (Fin 2 → Zd d L), wt b = (∑ x : Fin 2 → Zd d L, ‖Z x‖) ^ (2 * p) := by
    have := Finset.prod_univ_sum (fun _ : Fin (2 * p) => (Finset.univ : Finset (Fin 2 → Zd d L)))
      (fun _ x => ‖Z x‖)
    rw [Fintype.piFinset_univ] at this
    rw [hwt]; simp only
    rw [← this]
    simp
  have hPB := cltMom1_paired_moment_le hd p hlw hℓ hMz a₁ a₂ (z := z) hz0 hzu
  have hPB0 : 0 ≤ ((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
        ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
          (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p)) :=
    (Finset.sum_nonneg fun b _ => Finset.prod_nonneg fun k _ => hz0 _).trans hPB
  have hE := cltMom2_Emax_pow_le (P := P) hw0 hYm hYB p Λ' q₁ hq₁ (fun β hβ => hdom β hβ)
  calc ∫ ω, ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖ ^ (2 * p) ∂P
      ≤ ∑ b : Fin (2 * p) → (Fin 2 → Zd d L), wt b * ‖∫ ω, cltMom2_tuple P Y p b ω ∂P‖ :=
        cltMom2_expand hYm hYB Z p
    _ ≤ ∑ b : Fin (2 * p) → (Fin 2 → Zd d L), (εf * wt b + Q *
          (if CltMom1.Paired (10 * (lw ^ 3 * ℓ)) b then ∏ k, z (b k) else 0)) :=
        Finset.sum_le_sum fun b _ => hbd b
    _ = εf * ∑ b : Fin (2 * p) → (Fin 2 → Zd d L), wt b + Q *
          ∑ b ∈ Finset.univ.filter (fun b : Fin (2 * p) → (Fin 2 → Zd d L) =>
            CltMom1.Paired (10 * (lw ^ 3 * ℓ)) b), ∏ k, z (b k) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_filter]
    _ ≤ εf * (∑ x : Fin 2 → Zd d L, ‖Z x‖) ^ (2 * p) + Q * (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
          ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
            (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) := by
        rw [hsumw]
        gcongr
    _ ≤ _ := by
        have h2 : Q ≤ 2 ^ (2 * p) * (Λ' ^ (2 * p) + (B * ((lw ^ 3 * ℓ) ^ (d - 2) + 1)) ^ (2 * p) *
            (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) := by
          have h4 : (B * ((lw ^ 3 * ℓ) ^ (d - 2) + 1)) ^ (2 * p) * (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁ =
              (B * ((lw ^ 3 * ℓ) ^ (d - 2) + 1)) ^ (2 * p) * ((Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) := by ring
          rw [hQ, h4]
          exact mul_le_mul_of_nonneg_left hE (by positivity)
        have h3 := mul_le_mul_of_nonneg_right h2 hPB0
        linarith

private theorem cltMom2_S_meas (hYm : ∀ β, Measurable (Y β)) (Z : (Fin 2 → Zd d L) → ℂ) :
    Measurable fun ω => ∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P) :=
  Finset.measurable_sum _ fun β _ => (cltMom2_Yt_meas hYm β).const_mul _

private theorem cltMom2_S_norm_le [IsProbabilityMeasure P] (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (Z : (Fin 2 → Zd d L) → ℂ)
    (ω : Ω) : ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖ ≤ (∑ β, ‖Z β‖) * (B + B) := by
  calc ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖
      ≤ ∑ β, ‖Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖ := norm_sum_le _ _
    _ ≤ ∑ β, ‖Z β‖ * (B + B) := Finset.sum_le_sum fun β _ => by
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖Y β ω - ∫ ω', Y β ω' ∂P‖ ≤ ‖Y β ω‖ + ‖∫ ω', Y β ω' ∂P‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hYB _ _) (cltMom2_int_norm_le hYB _)
    _ = (∑ β, ‖Z β‖) * (B + B) := by rw [Finset.sum_mul]

/-- **Markov** (by `meas_gt_le_of_moment`): under the hypotheses of `cltMom2_moment_le`, for `θ > 0`,
`P{θ < |Σ_β Z_β (Y_β - 𝔼Y_β)|} ≤ (the right side of the moment bound) / θ^{2p}`. -/
theorem cltMom2_markov [IsProbabilityMeasure P] (hd : 3 ≤ d) (p : ℕ) {lw ℓ Mz Λ' q₁ εf : ℝ}
    (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ) (hMz : 0 ≤ Mz) (hq₁ : 0 ≤ q₁) (hεf : 0 ≤ εf) (a₁ a₂ : Zd d L)
    (hYm : ∀ β, Measurable (Y β)) (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (Z : (Fin 2 → Zd d L) → ℂ)
    (hZ : ∀ β : Fin 2 → Zd d L, lw ^ 3 * ℓ < ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) → Z β = 0)
    (hzu : ∀ β β' : Fin 2 → Zd d L,
      0 < ‖Z β‖ * (1 / (((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) →
      ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (lw ^ 3 * ℓ) →
      ‖Z β'‖ * (1 / (((zdistInf d L (β' 0 - β' 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤
        CltMom1.uw a₁ a₂ (lw ^ 4 * ℓ) (lw ^ 3 * ℓ) Mz (β 0) * CltMom1.G d L (lw ^ 3 * ℓ) (β' 0 - β' 1))
    (hdom : ∀ β : Fin 2 → Zd d L, ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ≤ lw ^ 3 * ℓ →
      P {ω | Λ' < ‖Y β ω‖ * (((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} ≤ ENNReal.ofReal q₁)
    (hiso : ∀ b : Fin (2 * p) → (Fin 2 → Zd d L),
      (∀ k, ((zdistInf d L ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤ lw ^ 3 * ℓ) →
      (∃ i, ∀ j, j ≠ i → 10 * lw ^ 3 * ℓ ≤ ((zdistInf d L ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
      ‖∫ ω, ∏ k : Fin (2 * p), CltMom2.X P Y (b k) (decide (p ≤ k.val)) ω ∂P‖ ≤ εf)
    (θ : ℝ) (hθ : 0 < θ) :
    P {ω | θ < ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖} ≤
      ENNReal.ofReal ((2 ^ (2 * p) * (Λ' ^ (2 * p) + (B * ((lw ^ 3 * ℓ) ^ (d - 2) + 1)) ^ (2 * p) *
          (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) *
        (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
          ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
            (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) +
      εf * (∑ β, ‖Z β‖) ^ (2 * p)) / θ ^ (2 * p)) := by
  have hmom := cltMom2_moment_le (P := P) hd p hlw hℓ hMz hq₁ hεf a₁ a₂ hYm hYB Z hZ hzu hdom hiso
  have hint : Integrable (fun ω => |‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖| ^ (2 * p)) P := by
    simp only [abs_norm]
    refine Integrable.of_bound (((cltMom2_S_meas hYm Z).norm).pow_const _).aestronglyMeasurable
      (((∑ β, ‖Z β‖) * (B + B)) ^ (2 * p)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (cltMom2_S_norm_le hYB Z ω) _
  refine RBM.Gauss.meas_gt_le_of_moment P hθ hint ?_
  simp only [abs_norm]
  exact hmom

end Engine

/-! ## 3. The decomposition of `f^{far} - 𝔼 f^{far}` -/

section Decomp

variable {d : ℕ} (sz : Sizes d)

/-- The loops `𝓛^{(2)}_{u,σ,a}` are integrable (measurable and bounded by `η_u^{-2}`); copy of the private
`meanFar_integrable_L` (`Evolution/MeanFar.lean`). -/
private theorem cltMom2_integrable_L (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Integrable (fun ω => Lloop sz n E u σ a ω) sz.seqP :=
  Integrable.of_bound (walk_measurable_Lloop sz n E u σ a).aestronglyMeasurable
    ((etaT E u)⁻¹ ^ 2) (Filter.Eventually.of_forall fun ω => norm_Lloop_le sz n hE hu σ a ω)

/-- The entries `STLKM` of the single-time flow are integrable. -/
private theorem cltMom2_integrable_LK (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs : s < 1)
    (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) :
    Integrable (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ b) sz.seqP := by
  have h : (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ b) =
      fun ω => Lloop sz n E s σ b ω - STKloop sz n E s σ b := rfl
  rw [h]
  exact (cltMom2_integrable_L sz n hE hs σ _).sub (integrable_const _)

open Classical in
/-- **The mean of `f^{far}`** with `∫ STLKM` in place of the mean kernel (copy of the private `meanFar_integral_fFar`, with `meanFar_B` unfolded): `𝔼 f^{far}` is `f^{far}` with `𝓑` replaced by `𝔼𝓑`
((5.28) `iksjuwjx3_far`). -/
private theorem cltMom2_integral_fFar (n : ℕ) {E s t : ℝ} (hE : |E| < 2) (hs : s < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∫ ω, STfFar sz n E s t σ a ω ∂(sz.seqP) =
      (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
        ∑ b₂ : Zd d (sz.L n),
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
            (∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)) *
            (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
              Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1)) := by
  unfold STfFar
  have hX : ∀ b₁ b₂ : Zd d (sz.L n), Integrable
      (fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂]) sz.seqP :=
    fun b₁ b₂ => cltMom2_integrable_LK sz n hE hs σ _
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun b₁ _ => integrable_finsetSum _
    (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _))]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [integral_finsetSum _ (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _)]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [integral_mul_const, integral_const_mul]

private theorem cltMom2_sum_pair {L : ℕ} [NeZero L] (F : Zd d L → Zd d L → ℂ) :
    ∑ v : Fin 2 → Zd d L, F (v 0) (v 1) = ∑ u₀ : Zd d L, ∑ u₁ : Zd d L, F u₀ u₁ := by
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Zd d L) (fun v => F (v 0) (v 1))
    (fun p => F p.1 p.2) (fun v => rfl), Fintype.sum_prod_type]

private theorem cltMom2_eta {L : ℕ} (β : Fin 2 → Zd d L) : β = ![β 0, β 1] := by
  ext i; fin_cases i <;> rfl

/-- `STcltX … false = A^{6/5} (𝓛 - 𝒦 - 𝔼(𝓛 - 𝒦))`: the scalar `A^{6/5}` of `STcltB` pulls out of the centring. -/
private theorem cltMom2_stcltX_false (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    STcltX sz n E s σ b false ω =
      (((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) : ℝ) : ℂ) *
        (STLKM sz n E s (sz.seqHflow n s ω) σ b - ∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ b ∂(sz.seqP)) := by
  unfold STcltX STcltB
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [integral_const_mul]
  ring

/-- The algebra of the weights: `(1-s)²/(g⁴ A') · (g² Θ₀) (g² ΔΘ) (A' D) = (1-s)² Θ₀ D ΔΘ`. -/
private theorem cltMom2_weight_algebra (g A' s : ℝ) (hg : g ≠ 0) (hA : A' ≠ 0) (Θ₀ ΔΘ D : ℂ) :
    (((1 - s) ^ 2 / (g ^ 4 * A') : ℝ) : ℂ) *
        ((((g ^ 2 : ℝ) : ℂ) * Θ₀) * (((g ^ 2 : ℝ) : ℂ) * ΔΘ) * (((A' : ℝ) : ℂ) * D)) =
      (((1 - s) ^ 2 : ℝ) : ℂ) * (Θ₀ * D * ΔΘ) := by
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  have hA' : (A' : ℂ) ≠ 0 := by exact_mod_cast hA
  push_cast
  field_simp

/-- The summand `Θ_{a₁b₁} (𝓑 - 𝔼𝓑)_{b₁b₂} (Θ_{b₂a₂} - Θ_{b₁a₂})` of `f^{far} - 𝔼 f^{far}` ((5.29) `eq:boundEfar`). -/
private def cltMom2_T (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (b₁ b₂ : Zd d (sz.L n)) : ℂ :=
  Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
    (STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] -
      ∫ ω', STLKM sz n E s (sz.seqHflow n s ω') σ ![b₁, b₂] ∂(sz.seqP)) *
    (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1))

open Classical in
/-- The termwise identity: the window part `c · Z_β (𝗕_β - 𝔼𝗕_β)` plus the off-window part is the full summand on the far set. -/
private theorem cltMom2_term (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hg : 0 < sz.lam n) (ω : sz.SeqΩ) (u₀ u₁ : Zd d (sz.L n)) :
    (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * (CltMom2.Z sz n E s t σ a ![u₀, u₁] * STcltX sz n E s σ ![u₀, u₁] false ω) +
      (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ)) then cltMom2_T sz n E s t σ a ω u₀ u₁ else 0) else 0) =
      (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then cltMom2_T sz n E s t σ a ω u₀ u₁ else 0) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA : (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) ≠ 0 := by positivity
  by_cases hf : (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ))
  · by_cases hw : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ))
    · have hZ : CltMom2.Z sz n E s t σ a ![u₀, u₁] = 0 := by
        unfold CltMom2.Z
        split_ifs with h
        · exact absurd hw (not_lt.2 h.2.2)
        · rfl
      simp only [hZ, hf, hw, and_self, ↓reduceIte, mul_zero, zero_mul, zero_add]
    · have hw' : ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ) ≤
          Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s := not_lt.1 hw
      have hZ : CltMom2.Z sz n E s t σ a ![u₀, u₁] =
          (((sz.lam n ^ 2 : ℝ) : ℂ) * Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) u₀) *
            (((sz.lam n ^ 2 : ℝ) : ℂ) * (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) u₁ (a 1) -
              Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) u₀ (a 1))) := by
        unfold CltMom2.Z
        split_ifs with h
        · rfl
        · exact absurd ⟨hf.1, hf.2, hw'⟩ h
      rw [hZ, cltMom2_stcltX_false]
      simp only [hf, hw, and_self, ↓reduceIte]
      rw [cltMom2_weight_algebra (sz.lam n) _ s hg.ne' hA, mul_zero, add_zero]
      unfold cltMom2_T
      rfl
  · have hZ : CltMom2.Z sz n E s t σ a ![u₀, u₁] = 0 := by
      unfold CltMom2.Z
      split_ifs with h
      · exact absurd ⟨h.1, h.2.1⟩ hf
      · rfl
    simp only [hZ, hf, ↓reduceIte, mul_zero, zero_mul, zero_add]

open Classical in
/-- `f^{far} - 𝔼 f^{far}` as a double sum over the far set (`cltMom2_integral_fFar`). -/
private theorem cltMom2_lhs (n : ℕ) {E s t : ℝ} (hE : |E| < 2) (hs : s < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STfFar sz n E s t σ a ω - ∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP) =
      ∑ u₀ : Zd d (sz.L n), ∑ u₁ : Zd d (sz.L n),
        (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then cltMom2_T sz n E s t σ a ω u₀ u₁ else 0) := by
  rw [cltMom2_integral_fFar sz n hE hs σ a]
  unfold STfFar
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  by_cases hf : (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ))
  · simp only [hf]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    simp only [and_self, ↓reduceIte]
    unfold cltMom2_T
    ring
  · simp [hf]

open Classical in
/-- `c · fluc` as a double sum: the reindexing `β = ![u₀, u₁]`. -/
private theorem cltMom2_fluc_eq (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * CltMom2.fluc sz n E s t σ a ω =
      ∑ u₀ : Zd d (sz.L n), ∑ u₁ : Zd d (sz.L n),
        (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * (CltMom2.Z sz n E s t σ a ![u₀, u₁] * STcltX sz n E s σ ![u₀, u₁] false ω) := by
  unfold CltMom2.fluc
  have hβ : ∀ β : Fin 2 → Zd d (sz.L n), CltMom2.Z sz n E s t σ a β * STcltX sz n E s σ β false ω =
      (fun u₀ u₁ : Zd d (sz.L n) => CltMom2.Z sz n E s t σ a ![u₀, u₁] * STcltX sz n E s σ ![u₀, u₁] false ω)
        (β 0) (β 1) := fun β => by
    simp only []
    rw [← cltMom2_eta β]
  rw [Finset.sum_congr rfl fun β _ => hβ β, cltMom2_sum_pair
    (fun u₀ u₁ : Zd d (sz.L n) => CltMom2.Z sz n E s t σ a ![u₀, u₁] * STcltX sz n E s σ ![u₀, u₁] false ω),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  rw [Finset.mul_sum]

open Classical in
/-- `CltMom2.off` as a double sum. -/
private theorem cltMom2_off_eq (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    CltMom2.off sz n E s t σ a ω =
      ∑ u₀ : Zd d (sz.L n), ∑ u₁ : Zd d (sz.L n),
        (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ)) then cltMom2_T sz n E s t σ a ω u₀ u₁ else 0) else 0) := by
  unfold CltMom2.off
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  by_cases hf : (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ))
  · simp only [hf]
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    by_cases hw : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ))
    · simp only [hw, and_self, ↓reduceIte, cltMom2_T]
    · simp [hw]
  · simp [hf]

open Classical in
/-- **The decomposition** `f^{far} - 𝔼 f^{far} = (1-s)²/(λ⁴ A^{6/5}) · fluc + off` ((5.29) `eq:boundEfar`):
`𝔼 f^{far}` is `f^{far}` with `𝓑` replaced by `𝔼𝓑` (`cltMom2_integral_fFar`), the difference is the sum of
`Θ_{a₁b₁} (𝓑 - 𝔼𝓑)_{b₁b₂} (Θ_{b₂a₂} - Θ_{b₁a₂})` over the far set, the window `|b₁-b₂| ≤ (log W)³ ℓ_s` gives
`λ⁻⁴ A^{-6/5} Σ_β Z_β (𝗕_β - 𝔼𝗕_β)` (`𝗕 = A^{6/5} 𝓑`, `Z_β = λ² Θ λ² ΔΘ`, the reindexing
`(b₁, b₂) ↔ β = ![b₁, b₂]`), the complement is `CltMom2.off`. -/
theorem cltMom2_decomp (d : ℕ) : CltMom2.DecompStmt d := by
  intro sz n E s t σ a hE hs hg ω
  rw [cltMom2_lhs sz n hE hs σ a ω, cltMom2_off_eq sz n E s t σ a ω, cltMom2_fluc_eq sz n E s t σ a ω,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u₁ _ => ?_
  exact (cltMom2_term sz n E s t σ a hg ω u₀ u₁).symm

end Decomp

/-! ## 4. The deterministic inputs -/

section Deterministic

/-- **The envelope of `𝗕`** (`norm_Lloop_le` at `k + 1 = 2`, `STLM_seqHflow`): `|𝗕_β| ≤ A^{6/5} (η_s^{-2} + Σ_β |𝒦^{(2)}_{s,σ,β}|)`
for `|E| < 2`, `s < 1`, every sample point. -/
theorem cltMom2_norm_stcltB_le (d : ℕ) : CltMom2.BYStmt d := by
  intro sz n E s σ hE hs β ω
  have hA : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) := by positivity
  unfold STcltB CltMom2.BY
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hA]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have h1 : ‖STLKM sz n E s (sz.seqHflow n s ω) σ β‖ ≤ (etaT E s)⁻¹ ^ 2 + ‖STKloop sz n E s σ β‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_Lloop_le sz n hE hs σ β ω) le_rfl)
  have h2 : ‖STKloop sz n E s σ β‖ ≤ ∑ β' : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β'‖ :=
    Finset.single_le_sum (f := fun β' : Fin 2 → Zd d (sz.L n) => ‖STKloop sz n E s σ β'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ β)
  linarith

/-- **The weights of `(eq:2p_product_pair)`** (`(prop:ThfadC)`, `(prop:BD1)`; `cltMom1_weight_a1` with the regime
`g²/L² ≤ 1 - t`, `cltMom1_weight_a2` with `2d (log W)³ ℓ_s ≤ (log W)⁴ ℓ_s`, `cltMom1_scale_bd1`; `|mE E| = 1`,
`STmsig E σ = PropSpin (mE E) σ`, the orientation `b - a` of `STfFar` against `a - b` of `CltMom1.uw` by
`cltMom1_zdistInf_sub_comm`): `M = C₅ (1 + 2^{d-1}) C₆ d`. -/
theorem cltMom2_weight_le (d : ℕ) : CltMom2.WeightStmt d := by
  intro hd Λ κ hΛ hκ
  obtain ⟨C₅, hC₅, H₅⟩ := cltMom1_weight_a1 d Λ hd hΛ
  obtain ⟨C₆, hC₆, H₆⟩ := cltMom1_weight_a2 d Λ κ hd hΛ hκ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hMpos : 0 < C₅ * (1 + 2 ^ (d - 1)) * C₆ * d := by positivity
  refine ⟨C₅ * (1 + 2 ^ (d - 1)) * C₆ * d, hMpos, ?_⟩
  intro sz n E s t σ a hE hκE hg hgΛ ht0 ht1 hreg hlw β
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hm : ‖mE E‖ = 1 := norm_mE hE
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hd1 : (1 : ℝ) ≤ 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    linarith
  have hlw1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := hd1.trans hlw
  have hw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s := by
    have : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
    positivity
  have hbd1 := cltMom1_scale_bd1 (d := d) hlw (show 0 ≤ ellT (sz.L n) (sz.lam n) s by linarith)
  have hnn : 0 ≤ CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s)
        (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (C₅ * (1 + 2 ^ (d - 1)) * C₆ * d) (β 0) *
      CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1) :=
    mul_nonneg (CltMom1.uw_nonneg hw0 hMpos.le _) (CltMom1.G_nonneg _ _)
  by_cases hc : Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 1) : ℕ) : ℝ) ∧
      ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s
  · obtain ⟨hc1, hc2, hc3⟩ := hc
    have hZ : CltMom2.Z sz n E s t σ a β =
        (((sz.lam n ^ 2 : ℝ) : ℂ) * Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) (β 0)) *
          (((sz.lam n ^ 2 : ℝ) : ℂ) * (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 1) (a 1) -
            Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (β 0) (a 1))) := by
      unfold CltMom2.Z
      split_ifs with h
      · rfl
      · exact absurd ⟨hc1, hc2, hc3⟩ h
    have h1 := H₅ (sz.L n) hL3 (sz.lam n) hg hgΛ t ht0 ht1 hreg (mE E) hm (σ 0) (σ 1) (a 0) (β 0)
    have hfar2 : Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (a 1 - β 0) : ℕ) : ℝ) := by
      rw [cltMom1_zdistInf_sub_comm]; exact hc2
    have h2 := H₆ (sz.L n) hL3 (sz.lam n) hg hgΛ t ht0 ht1 (mE E) hm hκE (σ 0) (σ 1) (a 1) (β 0) (β 1)
      (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s)
      (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s) hbd1 hfar2 hc3
    have hnorm : ‖CltMom2.Z sz n E s t σ a β‖ =
        (sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (PropSpin (mE E) (σ 0) * PropSpin (mE E) (σ 1))) (a 0) (β 0)‖) *
          (sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (PropSpin (mE E) (σ 0) * PropSpin (mE E) (σ 1))) (β 1) (a 1) -
            Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (PropSpin (mE E) (σ 0) * PropSpin (mE E) (σ 1))) (β 0) (a 1)‖) := by
      rw [hZ, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ sz.lam n ^ 2)]
      rfl
    have hfar1 : Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (a 0 - β 0) : ℕ) : ℝ) := by
      rw [cltMom1_zdistInf_sub_comm]; exact hc1
    have hq : 0 < ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
    have hA1 : 0 < ((zdistInf d (sz.L n) (a 0 - β 0) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
    have hA2 : 0 < ((zdistInf d (sz.L n) (a 1 - β 0) : ℕ) : ℝ) ^ (d - 1) + 1 := by positivity
    have hg2 : 0 ≤ sz.lam n ^ 2 := by positivity
    simp only [CltMom1.uw, CltMom1.G, hfar1, hfar2, hc3, and_self, ↓reduceIte]
    rw [hnorm]
    calc (sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (PropSpin (mE E) (σ 0) * PropSpin (mE E) (σ 1))) (a 0) (β 0)‖) *
          (sz.lam n ^ 2 * ‖Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (PropSpin (mE E) (σ 0) * PropSpin (mE E) (σ 1))) (β 1) (a 1) -
            Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (PropSpin (mE E) (σ 0) * PropSpin (mE E) (σ 1))) (β 0) (a 1)‖) *
          (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1))
        ≤ (C₅ * (1 + 2 ^ (d - 1)) / (((zdistInf d (sz.L n) (a 0 - β 0) : ℕ) : ℝ) ^ (d - 2) + 1)) *
          (C₆ * d * (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) /
            (((zdistInf d (sz.L n) (a 1 - β 0) : ℕ) : ℝ) ^ (d - 1) + 1)) *
          (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)
      _ = _ := by ring
  · have hZ0 : CltMom2.Z sz n E s t σ a β = 0 := by
      unfold CltMom2.Z
      split_ifs with h
      · exact absurd h hc
      · rfl
    rw [hZ0, norm_zero, zero_mul]
    exact hnn

/-- **`hzu` of `cltMom1_paired_moment_le` from the pointwise weight bound** (the comparability at the cluster radius
`2R = 20 w`, `40 w ≤ ρ`): at a label `β` with `z β > 0` the first label is far, the far labels `β'` within `20 w` have each profile
within `2^d` (`cltMom1_comparable_weights` at `r = 20 w`), so `4^d` for the product; a `β'` that is not far has `z β' ≤ uw(β'₀) = 0`. -/
theorem cltMom2_hzu : CltMom2.HzuStmt := by
  intro d L _ a₁ a₂ w ρ M z hd hw h40 hM hz0 hzu β β' hβ hdist
  have hGnn : ∀ x : Zd d L, 0 ≤ CltMom1.G d L w x := fun x => CltMom1.G_nonneg w x
  have hM4 : 0 ≤ (4 : ℝ) ^ d * M := by positivity
  have hR : 0 ≤ CltMom1.uw a₁ a₂ ρ w ((4 : ℝ) ^ d * M) (β 0) * CltMom1.G d L w (β' 0 - β' 1) :=
    mul_nonneg (CltMom1.uw_nonneg hw hM4 _) (hGnn _)
  have hfarβ : ρ < ((zdistInf d L (a₁ - β 0) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - β 0) : ℕ) : ℝ) := by
    by_contra hnf
    have h0 : CltMom1.uw a₁ a₂ ρ w M (β 0) = 0 := by
      unfold CltMom1.uw
      simp only [hnf, ↓reduceIte, mul_zero]
    have h1 := hzu β
    rw [h0, zero_mul] at h1
    linarith
  by_cases hfarβ' : ρ < ((zdistInf d L (a₁ - β' 0) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (a₂ - β' 0) : ℕ) : ℝ)
  · obtain ⟨⟨c1, -⟩, ⟨c2, -⟩⟩ := cltMom1_comparable_weights (r := 20 * w) (ρ := ρ) (lam := w)
      (by linarith) (by linarith) hw a₁ a₂ (β 0) (β' 0) hfarβ.1 hfarβ.2 hdist hd
    have hp1 : 0 ≤ 1 / (((zdistInf d L (a₁ - β' 0) : ℕ) : ℝ) ^ (d - 2) + 1) := by positivity
    have hp2 : 0 ≤ w / (((zdistInf d L (a₂ - β' 0) : ℕ) : ℝ) ^ (d - 1) + 1) := by positivity
    have h4 : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
    calc z β' ≤ CltMom1.uw a₁ a₂ ρ w M (β' 0) * CltMom1.G d L w (β' 0 - β' 1) := hzu β'
      _ ≤ CltMom1.uw a₁ a₂ ρ w ((4 : ℝ) ^ d * M) (β 0) * CltMom1.G d L w (β' 0 - β' 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (hGnn _)
          unfold CltMom1.uw
          simp only [hfarβ', hfarβ, and_self, ↓reduceIte]
          calc M * (1 / (((zdistInf d L (a₁ - β' 0) : ℕ) : ℝ) ^ (d - 2) + 1) *
                (w / (((zdistInf d L (a₂ - β' 0) : ℕ) : ℝ) ^ (d - 1) + 1)))
              ≤ M * ((2 ^ d * (1 / (((zdistInf d L (a₁ - β 0) : ℕ) : ℝ) ^ (d - 2) + 1))) *
                (2 ^ d * (w / (((zdistInf d L (a₂ - β 0) : ℕ) : ℝ) ^ (d - 1) + 1)))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul c1 c2 hp2 (by positivity)) hM
            _ = (4 : ℝ) ^ d * M * (1 / (((zdistInf d L (a₁ - β 0) : ℕ) : ℝ) ^ (d - 2) + 1) *
                (w / (((zdistInf d L (a₂ - β 0) : ℕ) : ℝ) ^ (d - 1) + 1))) := by
                rw [h4]; ring
  · have h0 : CltMom1.uw a₁ a₂ ρ w M (β' 0) = 0 := by
      unfold CltMom1.uw
      simp only [hfarβ', ↓reduceIte, mul_zero]
    have h1 := hzu β'
    rw [h0, zero_mul] at h1
    linarith

end Deterministic

/-! ## 5. The fixed-`n` moment bound -/

section Fixed

/-- **The `2p`-th moment bound `(eq:main_challenge3)` of the window fluctuation at one `n`, and Markov.**
`cltMom2_moment_le`, `cltMom2_markov` at `Y = STcltB sz n E s σ` (measurable by `walk_measurable_Lloop`), `B = CltMom2.BY`
(the envelope), `Z = CltMom2.Z`, `w = (log W)³ ℓ_s`, `ρ = (log W)⁴ ℓ_s`; `40 w ≤ ρ` from `40 ≤ log W`
(`cltMom1_scale_comparable`, `p = 1`); `hzu` from the weight bound and the comparability bound with `M = 4^d M_w`; the tuple of the field is literally
`∏_k STcltX … (b k) (decide (p ≤ k.val))`, and the isolation clause `10 * lw ^ 3 * ℓ` is that of `STCltIsoConcl`
(`cltMom1_not_paired_iff`, `mul_assoc`). -/
theorem cltMom2_moment_fixed (d : ℕ) : CltMom2.MomentStmt d := by
  intro hd Λ κ hΛ hκ
  obtain ⟨M₀, hM₀, HW⟩ := cltMom2_weight_le d hd Λ κ hΛ hκ
  have hM : 0 < (4 : ℝ) ^ d * M₀ := by positivity
  refine ⟨(4 : ℝ) ^ d * M₀, hM, ?_⟩
  intro sz n E s t σ a p Λ' q₁ εf hp hE hκE hg hgΛ hs ht0 ht1 hreg h40 h2d hq₁ hεf hdom hiso
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hlw1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s := by
    have : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
    positivity
  have hscale : 40 * (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s := by
    have := cltMom1_scale_comparable (lw := Real.log ((sz.W n : ℕ) : ℝ)) (ℓ := ellT (sz.L n) (sz.lam n) s) (p := 1)
      (by simpa using h40) (by linarith)
    push_cast at this
    linarith
  have hz0 : ∀ β : Fin 2 → Zd d (sz.L n), 0 ≤ ‖CltMom2.Z sz n E s t σ a β‖ *
      (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := fun β => by positivity
  have hzu := cltMom2_hzu d (sz.L n) (a 0) (a 1)
    (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s)
    (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s) M₀
    (fun β => ‖CltMom2.Z sz n E s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)))
    (by omega) hw0 hscale hM₀.le hz0
    (fun β => HW sz n E s t σ a hE.le hκE hg hgΛ ht0 ht1 hreg h2d β)
  have hYm : ∀ β : Fin 2 → Zd d (sz.L n), Measurable (STcltB sz n E s σ β) := by
    intro β
    have h1 : Measurable fun ω => STLKM sz n E s (sz.seqHflow n s ω) σ β :=
      (walk_measurable_Lloop sz n E s σ β).sub measurable_const
    exact measurable_const.mul h1
  have hYB : ∀ β ω, ‖STcltB sz n E s σ β ω‖ ≤ CltMom2.BY sz n E s σ :=
    fun β ω => cltMom2_norm_stcltB_le d sz n E s σ hE hs β ω
  have hZ : ∀ β : Fin 2 → Zd d (sz.L n),
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) → CltMom2.Z sz n E s t σ a β = 0 := by
    intro β hβ
    unfold CltMom2.Z
    split_ifs with h
    · exact absurd hβ (not_lt.2 h.2.2)
    · rfl
  have hiso' := hiso
  refine ⟨?_, fun θ hθ => ?_⟩
  · exact cltMom2_moment_le (P := sz.seqP) (Y := STcltB sz n E s σ) hd p hlw1 hℓ1 (by positivity) hq₁ hεf (a 0) (a 1)
      hYm hYB (CltMom2.Z sz n E s t σ a) hZ hzu hdom hiso'
  · exact cltMom2_markov (P := sz.seqP) (Y := STcltB sz n E s σ) hd p hlw1 hℓ1 (by positivity) hq₁ hεf (a 0) (a 1)
      hYm hYB (CltMom2.Z sz n E s t σ a) hZ hzu hdom hiso' θ hθ

/-- **The eventual form from `STCltIsoConcl`** (`εf = W^{-D}`; the clause of `STCltIsoConcl` at `n`, `σ` is
`CltMom2.IsoHyp … (W^{-D})`): `cltMom2_moment_fixed` with the same `M` and the Markov half; the only `∀ᶠ n` is that of
`STCltIsoConcl`.  The input of `Evolution/CltFar` (`STCltFar`). -/
theorem cltMom2_tail_eventually (d : ℕ) : CltMom2.TailStmt d := by
  intro hd Λ κ hΛ hκ
  obtain ⟨M, hM, H⟩ := cltMom2_moment_fixed d hd Λ κ hΛ hκ
  refine ⟨M, hM, ?_⟩
  intro sz E s t hiso p hp D hD
  filter_upwards [hiso p hp D hD] with n hn σ hσ a Λ' q₁ θ hE hκE hg hgΛ hs ht0 ht1 hreg h40 h2d hq₁ hdom hθ
  exact (H sz n (E n) (s n) (t n) σ a p Λ' q₁ (((sz.W n : ℕ) : ℝ) ^ (-D)) hp hE hκE hg hgΛ hs ht0 ht1 hreg h40 h2d hq₁
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hdom (hn σ hσ)).2 θ hθ

end Fixed

end RBM.Evol

end

