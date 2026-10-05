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
# S5-24 (ST-4): the probabilistic half of the CLT moment bound (ticket T2169)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`), proof of `lem;CLT`
(`3_5:2173-2249`): the decomposition of `f^{far} - 𝔼 f^{far}` into the window fluctuation and
the off-window part (`3_5:2213-2220`), the `2p`-th moment `(eq:main_challenge3)` (`3_5:2213`),
its expansion `(eq:2p_product)` (`3_5:2218`) over the regions `(eq:sumregionsforb)`
(`3_5:2220`), the pairing condition `(eq:pairingcond)` (`3_5:2223`), the paired tuples
`(eq:2p_product_pair)` (`3_5:2226`) and the isolated tuples `(eq:bound_isolated)` (`3_5:2245`).
Everything is at one size index `n` (no `Prec`, no `∀ n`): the union over the index set of
`STCltFarConcl` is the business of `S5-25` (`Evolution/CltFar`), which also bounds `CltMom2.off`
by `(eq:propcalB)` and supplies `CltMom2.DomHyp` from `STGdecayW` at `u = s`.  Notation: `|x| =
zdistInf d L x`, `w = (log W)³ ℓ_s` (window), `ρ = (log W)⁴ ℓ_s` (far cutoff), `R = 10 w`
(pairing radius of `STCltIsoConcl`), cluster radius `2R = 20 w`.

**Targets** (namespace `RBM.Evol`; constants and powers of `log W` explicit):

1. The vocabulary `CltMom2.Z`, `fluc`, `off`, `BY`, `DomHyp`, `IsoHyp`, `rhs` and the six
   statements `CltMom2.BYStmt`, `DecompStmt`, `WeightStmt`, `HzuStmt`, `MomentStmt`, `TailStmt`:
   verbatim as pinned in `docs/tickets/checks/T2169-check.lean`.  `CltMom2.IsoHyp` is the inner
   clause of `STCltIsoConcl` (`Step5Pins.lean:417-423`) at one `n`, `σ`, `p`.
2. The moment engine on two-label fields (a probability space `(Ω, P)`): `cltMom2_expand`
   (`(eq:2p_product)`), `cltMom2_moment_le` (the `2p`-th moment bound: isolated tuples by the
   hypothesis, paired tuples by the profile-normalised maximum and the merged
   `cltMom1_paired_moment_le`), `cltMom2_markov` (Markov).
3. `cltMom2_decomp : CltMom2.DecompStmt d`.
4. `cltMom2_norm_stcltB_le : CltMom2.BYStmt d` (envelope of `𝗕`), `cltMom2_weight_le :
   CltMom2.WeightStmt d` (`(prop:ThfadC)`, `(prop:BD1)`: `M = C₅ (1 + 2^{d-1}) C₆ d`),
   `cltMom2_hzu : CltMom2.HzuStmt` (comparability at radius `20 w`, factor `4^d`).
5. `cltMom2_moment_fixed : CltMom2.MomentStmt d` (the fixed-`n` moment bound at `Y = STcltB`, `M
   = 4^d M_w`).
6. `cltMom2_tail_eventually : CltMom2.TailStmt d` (the eventual form from `STCltIsoConcl`; the
   input of `S5-25`).

**Ports** (read-only source: RBM2D `RBM2D/Evolution/CltMoments.lean` at `c9a24cf`, with the
label `Z2 L` replaced by the two-label index `Fin 2 → Zd d L`): `CltMoments.tuple` `:700`,
`cltm_prod_split` `:714`, `cltm_Yt_meas` `:727`, `cltm_int_norm_le` `:730`, `cltm_tuple_meas`
`:736`, `cltm_factor_norm` `:745`, `cltm_tuple_norm_le` `:753`, `cltm_tuple_int` `:765`,
`cltm_expand` `:772`, `cltMax_*` `:826-844` (`CltMoments.ymax` `:706`; here the maximum of
`|Y_β| (|β₀-β₁|^{d-2}+1)` over the window labels), `cltm_pow_add_le` `:846`, `cltm_tuple_le`
`:857`, `cltMomentBound` `:914` (the paired sum by `cltMom1_paired_moment_le` instead of
`cltm_nonfar_sum_le`), `cltm_Emax_pow_le` `:970`, `cltm_S_meas`, `cltm_S_norm_le` `:1019-1032`,
`cltm_engine` `:1034`; toy field `unifBool` `:2212`, `signY` `:2219`.  Copies of private merged
proofs: `meanFar_integrable_L` (`Evolution/MeanFar.lean:874`) and `meanFar_integral_fFar`
(`:999`) as `cltMom2_integrable_L`, `cltMom2_integral_fFar`; the point-mass data of the merged
assembly instance (`CltMoments1.lean:2081-2127`, private there) is re-created.

**Differences from the paper** (paper-delta candidates, see the prove report): `T2169a` the
per-factor `≺` of the first line of `(eq:2p_product_pair)` is the profile-normalised maximum
with the tail `(Λ', q₁)` and the envelope `CltMom2.BY`; `T2169b` the `O(W^{-D})` of
`(eq:2p_product)` is the separate term `CltMom2.off`; `T2169c` the factor `4^d` of the
comparability at radius `2R` and the constant `M_w`; `T2169d` the moment bound with `|𝔼 ∏ 𝕀𝔼𝗕|`
and `∏ |weights|` at one `n` with explicit `Λ'`, `q₁`, `εf`.

-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes


/-! ## 1. The pinned vocabulary and statements (target 1) -/

/-- **The weight of a two-label index `β = (β₀, β₁)` in `(eq:2p_product)`** (`3_5:2218`):
`ilambda² Θ_t(a₁, β₀) · ilambda² (Θ_t(β₁, a₂) - Θ_t(β₀, a₂))` on the region `(eq:sumregionsforb)` (`3_5:2220`):
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

/-- **The window fluctuation** `ilambda⁴ (1-s)^{-2} (ilambda² W^d)^{6/5} (𝕀𝔼 f^{far})_{window}` (`3_5:2214-2218`):
`Σ_β Z_β (𝗕_β - 𝔼𝗕_β)`, with the centred factor `STcltX … false` of the pin. -/
def CltMom2.fluc {d : ℕ} (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  ∑ β : Fin 2 → Zd d (sz.L n), CltMom2.Z sz n E s t σ a β * STcltX sz n E s σ β false ω

open Classical in
/-- **The off-window part** of `f^{far} - 𝔼 f^{far}` (the `O(W^{-D})` of `(eq:2p_product)`): the sum of `STfFar` with
`𝓑` replaced by `𝓑 - 𝔼𝓑` over `|b₁ - b₂| > (log W)³ ℓ_s`.  S5-25 bounds it with `(eq:propcalB)` (`3_5:2155`). -/
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

/-- **The deterministic envelope of `𝗕`**: `A^{6/5} (η_s^{-2} + Σ_β |𝒦^{(2)}_{s,σ,β}|)`, `A = ilambda² W^d`
(`|𝓛^{(2)}| ≤ η_s^{-2}`, `norm_Lloop_le`). -/
def CltMom2.BY {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) : ℝ :=
  (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) *
    ((etaT E s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖STKloop sz n E s σ β‖)

/-- **The per-label tail of the profile-normalised `𝗕` on the window** at one `n` (the `≺` of `(eq:propcalB)`,
`3_5:2155`, in the form used by `(eq:2p_product_pair)`): `P(Λ' < |𝗕_β| (|β₀-β₁|^{d-2}+1)) ≤ q₁` for every window
label `β`.  S5-25 supplies it from `STGdecayW` at `u = s`. -/
def CltMom2.DomHyp {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (Λ' q₁ : ℝ) : Prop :=
  ∀ β : Fin 2 → Zd d (sz.L n),
    ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s →
    sz.seqP {ω | Λ' < ‖STcltB sz n E s σ β ω‖ * (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} ≤
      ENNReal.ofReal q₁

/-- **The isolation bound at one `n`** (`(eq:bound_isolated)`, `3_5:2245`): the inner clause of `STCltIsoConcl`
(`Step5Pins.lean:417-423`) with `(E n), (s n)` replaced by `E, s` and the error `W^{-D}` by `εf`. -/
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

/-- Target 4a: the envelope of `𝗕`. -/
def CltMom2.BYStmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool), |E| < 2 → s < 1 →
    ∀ (β : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ), ‖STcltB sz n E s σ β ω‖ ≤ CltMom2.BY sz n E s σ

/-- Target 3: the decomposition `f^{far} - 𝔼 f^{far} = (1-s)²/(ilambda⁴ A^{6/5}) · fluc + off`. -/
def CltMom2.DecompStmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    |E| < 2 → s < 1 → 0 < sz.lam n → ∀ ω : sz.SeqΩ,
      STfFar sz n E s t σ a ω - ∫ ω', STfFar sz n E s t σ a ω' ∂(sz.seqP) =
        (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
            CltMom2.fluc sz n E s t σ a ω + CltMom2.off sz n E s t σ a ω

/-- Target 4b: the weights of `(eq:2p_product_pair)` (`(prop:ThfadC)`, `(prop:BD1)`): `|Z_β| (|β₀-β₁|^{d-2}+1)^{-1}`
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

/-- Target 4c: the hypothesis `hzu` of `cltMom1_paired_moment_le` from the pointwise weight bound, at the cluster
radius `2R = 20 w` (comparability, `40 w ≤ ρ`), with the factor `4^d`. -/
def CltMom2.HzuStmt : Prop :=
  ∀ (d L : ℕ) [NeZero L] (a₁ a₂ : Zd d L) (w ρ M : ℝ) (z : (Fin 2 → Zd d L) → ℝ),
    2 ≤ d → 0 ≤ w → 40 * w ≤ ρ → 0 ≤ M → (∀ β, 0 ≤ z β) →
    (∀ β, z β ≤ CltMom1.uw a₁ a₂ ρ w M (β 0) * CltMom1.G d L w (β 0 - β 1)) →
    ∀ β β' : Fin 2 → Zd d L, 0 < z β → ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * w →
      z β' ≤ CltMom1.uw a₁ a₂ ρ w (4 ^ d * M) (β 0) * CltMom1.G d L w (β' 0 - β' 1)

/-- Target 5: the `2p`-th moment bound `(eq:main_challenge3)` of the window fluctuation at one `n`, and Markov. -/
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

/-- Target 6: the eventual form from `STCltIsoConcl` (`εf = W^{-D}`), for `σ₁ ≠ σ₂`; the input of S5-25. -/
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

/-! ## 2. The moment engine on two-label fields (target 2) -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {d L : ℕ} [NeZero L]

/-- The centred factor `X_k(b)` of the tuple product of `(eq:2p_product)`: `Y_β - 𝔼Y_β` (`cj = false`) or its
complex conjugate (`cj = true`); the shape of `STcltX` (`Step5Pins.lean:404`) for an arbitrary field `Y`. -/
def CltMom2.X (P : Measure Ω) (Y : (Fin 2 → Zd d L) → Ω → ℂ) (β : Fin 2 → Zd d L) (cj : Bool) (ω : Ω) : ℂ :=
  if cj then (starRingEnd ℂ) (Y β ω - ∫ ω', Y β ω' ∂P) else Y β ω - ∫ ω', Y β ω' ∂P

/-- The tuple product `∏_{k<2p} X_k(b)`, conjugated from `k = p` on (`decide (p ≤ k.val)`, the convention of `STcltX`). -/
private abbrev cltMom2_tuple (P : Measure Ω) (Y : (Fin 2 → Zd d L) → Ω → ℂ) (p : ℕ)
    (b : Fin (2 * p) → (Fin 2 → Zd d L)) (ω : Ω) : ℂ :=
  ∏ k : Fin (2 * p), CltMom2.X P Y (b k) (decide (p ≤ k.val)) ω

/-- Port of RBM2D `cltm_prod_split` (`CltMoments.lean:714`, commit `c9a24cf`), with the convention `p ≤ k`. -/
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

/-- **`(eq:2p_product)`: the `2p`-th moment of the window fluctuation expands into the tuple expectations**
(port of RBM2D `cltm_expand`, `CltMoments.lean:772`, commit `c9a24cf`, with the label `Z2 L` replaced by the two-label index
`Fin 2 → Zd d L`): for a bounded measurable field `Y` on a probability space and a row `Z`,
`𝔼 |Σ_β Z_β (Y_β - 𝔼Y_β)|^{2p} ≤ Σ_{b : Fin (2p) → (Fin 2 → Zd d L)} (∏_k |Z_{b_k}|) |𝔼 ∏_k X_k(b)|`, where `X_k(b) =
Y_{b_k} - 𝔼Y_{b_k}` for `k < p` and its conjugate for `p ≤ k`. -/
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

/-- The profile weight `q(β) = |β₀ - β₁|_∞^{d-2} + 1` of `(eq:2p_product_pair)` (`3_5:2226`): its inverse is the profile `π(β)`. -/
private def cltMom2_q (β : Fin 2 → Zd d L) : ℝ := ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1

private theorem cltMom2_q_pos (β : Fin 2 → Zd d L) : 0 < cltMom2_q β := by
  unfold cltMom2_q; positivity

/-- The window predicate `|β₀ - β₁|_∞ ≤ w` of `(eq:sumregionsforb)`. -/
private def cltMom2_win (w : ℝ) (β : Fin 2 → Zd d L) : Prop := ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ≤ w

/-- The profile-normalised maximum `max_{β in the window} |Y_β| q(β)` (the maximum `ymax` of RBM2D
`CltMoments.ymax`, `CltMoments.lean:706`, restricted to the window labels, with the weight `q`; `0` off the window). -/
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

/-- Port of RBM2D `cltm_pow_add_le` (`CltMoments.lean:846`): `(x + m)^q ≤ 2^q (x^q + m^q) / 2`. -/
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

/-- **The centred tuple, on the window** (port of RBM2D `cltm_tuple_le`, `CltMoments.lean:857`: centring `2^{2p}`, Jensen;
with the profile): if all labels of `b` are in the window, then
`|𝔼 ∏_k X_k(b)| ≤ (∏_k π(b_k)) · 2^{2p} 𝔼 ymax^{2p}`, `π = 1/q`, `ymax` the profile-normalised maximum. -/
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

/-- **The expectation of the maximum** (port of RBM2D `cltm_Emax_pow_le`, `CltMoments.lean:970`): from the per-label tail
`P{Λ' < |Y_β| q(β)} ≤ q₁` on the window and the envelope `|Y_β| ≤ B`,
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


/-- **The `2p`-th moment bound of the window fluctuation** (`(eq:main_challenge3)`, `3_5:2213-2249`, at one `n`; port of RBM2D
`cltMomentBound` `CltMoments.lean:914` and `cltm_Emax_pow_le` `:970`, commit `c9a24cf`, on two-label indices with the profile
`π(β) = (|β₀-β₁|^{d-2}+1)⁻¹`, and the merged `cltMom1_paired_moment_le` for the paired tuples).  Let `lw ≥ 1`, `ℓ ≥ 1`,
`w = lw³ ℓ`, `Y` a bounded (`|Y_β| ≤ B`) measurable field, `Z_β = 0` off the window `|β₀-β₁| ≤ w`, the weights
`z_β = |Z_β| π(β)` satisfy `hzu` (comparability at the cluster radius `20 w`), the tail `P{Λ' < |Y_β| q(β)} ≤ q₁` holds on the window
(`q = π⁻¹`), and `|𝔼 ∏ X_k(b)| ≤ εf` for every isolated window tuple (`(eq:bound_isolated)`).  Then
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

/-- **Markov** (port of RBM2D `cltm_engine`, `CltMoments.lean:1034`, by `RBM.Gauss.meas_gt_le_of_moment`): under the hypotheses of
`cltMom2_moment_le`, for `θ > 0`, `P{θ < |Σ_β Z_β (Y_β - 𝔼Y_β)|} ≤ (the right side of the moment bound) / θ^{2p}`. -/
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

/-! ## 3. The decomposition of `f^{far} - 𝔼 f^{far}` (target 3) -/

section Decomp

variable {d : ℕ} (sz : Sizes d)

/-- The loops `𝓛^{(2)}_{u,σ,a}` are integrable (measurable and bounded by `η_u^{-2}`); copy of the private
`meanFar_integrable_L` (`Evolution/MeanFar.lean:874`). -/
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
/-- **The mean of `f^{far}`** with `∫ STLKM` in place of the mean kernel (copy of the private `meanFar_integral_fFar`,
`Evolution/MeanFar.lean:999`, with `meanFar_B` unfolded): `𝔼 f^{far}` is `f^{far}` with `𝓑` replaced by `𝔼𝓑`
(`3_5:2192`). -/
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

/-- The summand `Θ_{a₁b₁} (𝓑 - 𝔼𝓑)_{b₁b₂} (Θ_{b₂a₂} - Θ_{b₁a₂})` of `f^{far} - 𝔼 f^{far}` (`3_5:2213-2220`). -/
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
/-- **Target 3: the decomposition** `f^{far} - 𝔼 f^{far} = (1-s)²/(ilambda⁴ A^{6/5}) · fluc + off` (`3_5:2213-2220`):
`𝔼 f^{far}` is `f^{far}` with `𝓑` replaced by `𝔼𝓑` (`cltMom2_integral_fFar`), the difference is the sum of
`Θ_{a₁b₁} (𝓑 - 𝔼𝓑)_{b₁b₂} (Θ_{b₂a₂} - Θ_{b₁a₂})` over the far set, the window `|b₁-b₂| ≤ (log W)³ ℓ_s` gives
`ilambda⁻⁴ A^{-6/5} Σ_β Z_β (𝗕_β - 𝔼𝗕_β)` (`𝗕 = A^{6/5} 𝓑`, `Z_β = ilambda² Θ ilambda² ΔΘ`, the reindexing
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

/-! ## 4. The deterministic inputs (target 4) -/

section Deterministic

/-- **Target 4a: the envelope of `𝗕`** (`norm_Lloop_le` at `k + 1 = 2`, `STLM_seqHflow`): `|𝗕_β| ≤ A^{6/5} (η_s^{-2} + Σ_β |𝒦^{(2)}_{s,σ,β}|)`
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

/-- **Target 4b: the weights of `(eq:2p_product_pair)`** (`(prop:ThfadC)`, `(prop:BD1)`; `cltMom1_weight_a1` with the regime
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

/-- **Target 4c: `hzu` of `cltMom1_paired_moment_le` from the pointwise weight bound** (the comparability at the cluster radius
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

/-! ## 5. The fixed-`n` moment bound (target 5) -/

section Fixed

/-- `STcltX … false` is the centred `STcltB`. -/
private theorem cltMom2_stcltX_false' {d : ℕ} (sz : Sizes d) (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool)
    (b : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STcltX sz n E s σ b false ω = STcltB sz n E s σ b ω - ∫ ω', STcltB sz n E s σ b ω' ∂(sz.seqP) := rfl

/-- **Target 5: the `2p`-th moment bound `(eq:main_challenge3)` of the window fluctuation at one `n`, and Markov.**
`cltMom2_moment_le`, `cltMom2_markov` at `Y = STcltB sz n E s σ` (measurable by `walk_measurable_Lloop`), `B = CltMom2.BY`
(target 4a), `Z = CltMom2.Z`, `w = (log W)³ ℓ_s`, `ρ = (log W)⁴ ℓ_s`; `40 w ≤ ρ` from `40 ≤ log W`
(`cltMom1_scale_comparable`, `p = 1`); `hzu` from targets 4b and 4c with `M = 4^d M_w`; the tuple of the field is literally
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

/-- **Target 6: the eventual form from `STCltIsoConcl`** (`εf = W^{-D}`; the clause of `STCltIsoConcl` at `n`, `σ` is
`CltMom2.IsoHyp … (W^{-D})`): `cltMom2_moment_fixed` with the same `M` and the Markov half; the only `∀ᶠ n` is that of
`STCltIsoConcl`.  The input of S5-25 (`STCltFar`). -/
theorem cltMom2_tail_eventually (d : ℕ) : CltMom2.TailStmt d := by
  intro hd Λ κ hΛ hκ
  obtain ⟨M, hM, H⟩ := cltMom2_moment_fixed d hd Λ κ hΛ hκ
  refine ⟨M, hM, ?_⟩
  intro sz E s t hiso p hp D hD
  filter_upwards [hiso p hp D hD] with n hn σ hσ a Λ' q₁ θ hE hκE hg hgΛ hs ht0 ht1 hreg h40 h2d hq₁ hdom hθ
  exact (H sz n (E n) (s n) (t n) σ a p Λ' q₁ (((sz.W n : ℕ) : ℝ) ^ (-D)) hp hE hκE hg hgΛ hs ht0 ht1 hreg h40 h2d hq₁
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hdom (hn σ hσ)).2 θ hθ

end Fixed

/-! ## 6. Compiled nonempty instances (`d = 3`) -/

section Instances

/-! ### Target 2: `cltMom2_expand`, `cltMom2_moment_le`, `cltMom2_markov` on a nondegenerate toy field -/

/-- The uniform probability measure on `Bool` (port of RBM2D `unifBool`, `CltMoments.lean:2212`, commit `c9a24cf`). -/
private def cltMom2_unifBool : Measure Bool :=
  (2 : ENNReal)⁻¹ • Measure.dirac true + (2 : ENNReal)⁻¹ • Measure.dirac false

private instance : IsProbabilityMeasure cltMom2_unifBool :=
  ⟨by simp [cltMom2_unifBool, ENNReal.inv_two_add_inv_two]⟩

/-- A random sign `ξ ∈ {±1}`, the same for every two-label index (port of RBM2D `signY`, `CltMoments.lean:2219`). -/
private def cltMom2_signY (_β : Fin 2 → Zd 3 83) (ω : Bool) : ℂ := if ω then 1 else -1

private theorem cltMom2_signY_norm (β : Fin 2 → Zd 3 83) (ω : Bool) : ‖cltMom2_signY β ω‖ = 1 := by
  cases ω <;> simp [cltMom2_signY]

private theorem cltMom2_signY_int (β : Fin 2 → Zd 3 83) : ∫ ω, cltMom2_signY β ω ∂cltMom2_unifBool = 0 := by
  have h1 : Integrable (cltMom2_signY β) cltMom2_unifBool := Integrable.of_finite
  have ht : cltMom2_unifBool {true} = 2⁻¹ := by simp [cltMom2_unifBool]
  have hf : cltMom2_unifBool {false} = 2⁻¹ := by simp [cltMom2_unifBool]
  rw [integral_fintype h1]
  simp [Measure.real, ht, hf, cltMom2_signY]

/-- The data: `a₁ = 0`, `a₂ = (0,0,1)`, the index `β⁰ = ((41,41,41),(41,41,42))` (window `|β₀-β₁|_∞ = 1`), `L = 83`. -/
private def cltMom2_a₂ : Zd 3 83 := ![0, 0, 1]

private def cltMom2_β0 : Fin 2 → Zd 3 83 := ![![41, 41, 41], ![41, 41, 42]]

private theorem cltMom2_β0_win : zdistInf 3 83 (cltMom2_β0 0 - cltMom2_β0 1) = 1 := by decide

/-- The value `c = u(β⁰₀) G_w(β⁰₀ - β⁰₁)` of the merged S5-23 assembly instance (`CltMoments1.lean:2081`, re-created: the
private `cltMom1_c`), at `lw = ℓ = 1`, `M = 1`. -/
private noncomputable def cltMom2_c : ℝ :=
  CltMom1.uw (0 : Zd 3 83) cltMom2_a₂ (1 ^ 4 * 1) (1 ^ 3 * 1) 1 (cltMom2_β0 0) *
    CltMom1.G 3 83 (1 ^ 3 * 1) (cltMom2_β0 0 - cltMom2_β0 1)

private theorem cltMom2_c_pos : 0 < cltMom2_c := by
  have hA : zdistInf 3 83 ((0 : Zd 3 83) - cltMom2_β0 0) = 41 := by decide
  have hB : zdistInf 3 83 (cltMom2_a₂ - cltMom2_β0 0) = 41 := by decide
  unfold cltMom2_c CltMom1.uw CltMom1.G
  rw [hA, hB, cltMom2_β0_win]
  norm_num

open Classical in
/-- The row `Z`: the point mass at `β⁰` with `‖Z_{β⁰}‖ π(β⁰) = c`, `π(β⁰) = 1/2`. -/
private noncomputable def cltMom2_Z0 : (Fin 2 → Zd 3 83) → ℂ :=
  fun β => if β = cltMom2_β0 then ((2 * cltMom2_c : ℝ) : ℂ) else 0

open Classical in
private theorem cltMom2_Z0_prof (β : Fin 2 → Zd 3 83) :
    ‖cltMom2_Z0 β‖ * (1 / (((zdistInf 3 83 (β 0 - β 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) =
      if β = cltMom2_β0 then cltMom2_c else 0 := by
  by_cases h : β = cltMom2_β0
  · subst h
    have := cltMom2_c_pos
    simp only [cltMom2_Z0, ↓reduceIte, Complex.norm_real, cltMom2_β0_win]
    rw [Real.norm_of_nonneg (by positivity)]
    norm_num
    ring
  · simp [cltMom2_Z0, h]

private theorem cltMom2_toy_hZ (β : Fin 2 → Zd 3 83)
    (h : (1 : ℝ) ^ 3 * 1 < ((zdistInf 3 83 (β 0 - β 1) : ℕ) : ℝ)) : cltMom2_Z0 β = 0 := by
  classical
  by_cases hβ : β = cltMom2_β0
  · subst hβ
    rw [cltMom2_β0_win] at h
    norm_num at h
  · simp [cltMom2_Z0, hβ]

private theorem cltMom2_toy_hzu (β β' : Fin 2 → Zd 3 83)
    (hβ : 0 < ‖cltMom2_Z0 β‖ * (1 / (((zdistInf 3 83 (β 0 - β 1) : ℕ) : ℝ) ^ (3 - 2) + 1)))
    (_ : ((zdistInf 3 83 (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (1 ^ 3 * 1)) :
    ‖cltMom2_Z0 β'‖ * (1 / (((zdistInf 3 83 (β' 0 - β' 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) ≤
      CltMom1.uw (0 : Zd 3 83) cltMom2_a₂ (1 ^ 4 * 1) (1 ^ 3 * 1) 1 (β 0) *
        CltMom1.G 3 83 (1 ^ 3 * 1) (β' 0 - β' 1) := by
  classical
  rw [cltMom2_Z0_prof] at hβ ⊢
  have hβb : β = cltMom2_β0 := by
    by_contra h
    simp [h] at hβ
  have hnn : 0 ≤ CltMom1.uw (0 : Zd 3 83) cltMom2_a₂ (1 ^ 4 * 1) (1 ^ 3 * 1) 1 (β 0) *
      CltMom1.G 3 83 (1 ^ 3 * 1) (β' 0 - β' 1) :=
    mul_nonneg (CltMom1.uw_nonneg (by norm_num) (by norm_num) _) (CltMom1.G_nonneg _ _)
  by_cases hβ' : β' = cltMom2_β0
  · subst hβb
    simp only [hβ', ↓reduceIte, cltMom2_c]
    exact le_rfl
  · simp only [hβ', ↓reduceIte]
    exact hnn

private theorem cltMom2_toy_hdom (β : Fin 2 → Zd 3 83)
    (h : ((zdistInf 3 83 (β 0 - β 1) : ℕ) : ℝ) ≤ 1 ^ 3 * 1) :
    cltMom2_unifBool {ω | (2 : ℝ) < ‖cltMom2_signY β ω‖ * (((zdistInf 3 83 (β 0 - β 1) : ℕ) : ℝ) ^ (3 - 2) + 1)} ≤
      ENNReal.ofReal 0 := by
  have hset : {ω | (2 : ℝ) < ‖cltMom2_signY β ω‖ * (((zdistInf 3 83 (β 0 - β 1) : ℕ) : ℝ) ^ (3 - 2) + 1)} = ∅ := by
    ext ω
    have h' : ((zdistInf 3 83 (β 0 - β 1) : ℕ) : ℝ) ≤ 1 := by simpa using h
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, cltMom2_signY_norm, one_mul]
    rw [show (3 - 2 : ℕ) = 1 from rfl, pow_one]
    linarith
  rw [hset]
  simp

private theorem cltMom2_toy_hiso (p : ℕ) (b : Fin (2 * p) → (Fin 2 → Zd 3 83)) :
    ‖∫ ω, ∏ k : Fin (2 * p), CltMom2.X cltMom2_unifBool cltMom2_signY (b k) (decide (p ≤ k.val)) ω
      ∂cltMom2_unifBool‖ ≤ 1 := by
  have hX : ∀ (β : Fin 2 → Zd 3 83) (cj : Bool) (ω : Bool),
      ‖CltMom2.X cltMom2_unifBool cltMom2_signY β cj ω‖ = 1 := by
    intro β cj ω
    rw [cltMom2_X_norm, cltMom2_signY_int, sub_zero, cltMom2_signY_norm]
  have h := norm_integral_le_of_norm_le_const (μ := cltMom2_unifBool)
    (f := fun ω => ∏ k : Fin (2 * p), CltMom2.X cltMom2_unifBool cltMom2_signY (b k) (decide (p ≤ k.val)) ω)
    (C := 1) (Filter.Eventually.of_forall fun ω => by
      rw [norm_prod]
      exact (Finset.prod_eq_one fun k _ => hX _ _ _).le)
  rw [probReal_univ, mul_one] at h
  exact h

/-- **Instance of `cltMom2_expand`** (`d = 3`, `L = 83`, `p = 1`): `Ω = Bool` with the uniform measure, `Y_β = ±1`
(`𝔼 Y = 0`, a non-constant field), `Z` the point mass at `β⁰`. -/
example := cltMom2_expand (P := cltMom2_unifBool) (Y := cltMom2_signY) (B := 1)
  (fun _ => measurable_of_finite _) (fun β ω => (cltMom2_signY_norm β ω).le) cltMom2_Z0 1

/-- **Instance of `cltMom2_moment_le`** (`d = 3`, `L = 83`, `p = 1`, `lw = ℓ = 1`, `w = ρ = 1`, `a₁ = 0`, `a₂ = (0,0,1)`,
`Λ' = 2`, `q₁ = 0`, `εf = 1`, `Mz = 1`): every hypothesis is discharged (the window tail event is empty, `hzu` holds with
equality at `β⁰`, the isolated tuples have `|𝔼 ∏ X| ≤ 1`). -/
example := cltMom2_moment_le (P := cltMom2_unifBool) (Y := cltMom2_signY) (d := 3) (L := 83) (by norm_num) 1
  (lw := 1) (ℓ := 1) (Mz := 1) (B := 1) (Λ' := 2) (q₁ := 0) (εf := 1) le_rfl le_rfl zero_le_one le_rfl zero_le_one
  (0 : Zd 3 83) cltMom2_a₂ (fun _ => measurable_of_finite _) (fun β ω => (cltMom2_signY_norm β ω).le)
  cltMom2_Z0 cltMom2_toy_hZ cltMom2_toy_hzu cltMom2_toy_hdom
  (fun b _ _ => cltMom2_toy_hiso 1 b)

/-- **Instance of `cltMom2_markov`** (the same data, `θ = 1`). -/
example := cltMom2_markov (P := cltMom2_unifBool) (Y := cltMom2_signY) (d := 3) (L := 83) (by norm_num) 1
  (lw := 1) (ℓ := 1) (Mz := 1) (B := 1) (Λ' := 2) (q₁ := 0) (εf := 1) le_rfl le_rfl zero_le_one le_rfl zero_le_one
  (0 : Zd 3 83) cltMom2_a₂ (fun _ => measurable_of_finite _) (fun β ω => (cltMom2_signY_norm β ω).le)
  cltMom2_Z0 cltMom2_toy_hZ cltMom2_toy_hzu cltMom2_toy_hdom
  (fun b _ _ => cltMom2_toy_hiso 1 b) 1 one_pos

/-! ### Target 4c: `cltMom2_hzu` at `d = 3`, `L = 83`, `w = 1`, `ρ = 40`, `M = 1` -/

/-- The second index `β' = ((36,41,41),(36,41,40))`: first label at distance `5 ≤ 20 w` from `β⁰`'s, far (`|β'₀ - a_i| = 41 > 40`). -/
private def cltMom2_β1 : Fin 2 → Zd 3 83 := ![![36, 41, 41], ![36, 41, 40]]

/-- The value `u(β⁰₀) G_w(β⁰₀ - β⁰₁)` at `ρ = 40`, `w = 1`, `M = 1`. -/
private noncomputable def cltMom2_c40 : ℝ :=
  CltMom1.uw (0 : Zd 3 83) cltMom2_a₂ 40 1 1 (cltMom2_β0 0) * CltMom1.G 3 83 1 (cltMom2_β0 0 - cltMom2_β0 1)

private theorem cltMom2_c40_pos : 0 < cltMom2_c40 := by
  have hA : zdistInf 3 83 ((0 : Zd 3 83) - cltMom2_β0 0) = 41 := by decide
  have hB : zdistInf 3 83 (cltMom2_a₂ - cltMom2_β0 0) = 41 := by decide
  unfold cltMom2_c40 CltMom1.uw CltMom1.G
  rw [hA, hB, cltMom2_β0_win]
  norm_num

open Classical in
/-- The two-point row `z`: the value `c₄₀` at `β⁰` and at `β'` (equal weights: both first labels are at `|·|_∞`-distance
`41` from `a₁` and from `a₂`), `0` elsewhere. -/
private noncomputable def cltMom2_z40 : (Fin 2 → Zd 3 83) → ℝ :=
  fun β => if β = cltMom2_β0 ∨ β = cltMom2_β1 then cltMom2_c40 else 0

private theorem cltMom2_z40_nonneg (β : Fin 2 → Zd 3 83) : 0 ≤ cltMom2_z40 β := by
  classical
  unfold cltMom2_z40
  split_ifs
  · exact cltMom2_c40_pos.le
  · exact le_rfl

private theorem cltMom2_z40_bound (β : Fin 2 → Zd 3 83) :
    cltMom2_z40 β ≤ CltMom1.uw (0 : Zd 3 83) cltMom2_a₂ 40 1 1 (β 0) * CltMom1.G 3 83 1 (β 0 - β 1) := by
  classical
  have hnn : 0 ≤ CltMom1.uw (0 : Zd 3 83) cltMom2_a₂ 40 1 1 (β 0) * CltMom1.G 3 83 1 (β 0 - β 1) :=
    mul_nonneg (CltMom1.uw_nonneg (by norm_num) (by norm_num) _) (CltMom1.G_nonneg _ _)
  by_cases h0 : β = cltMom2_β0
  · subst h0
    simp only [cltMom2_z40, true_or, ↓reduceIte, cltMom2_c40]
    exact le_rfl
  · by_cases h1 : β = cltMom2_β1
    · subst h1
      have hA : zdistInf 3 83 ((0 : Zd 3 83) - cltMom2_β1 0) = 41 := by decide
      have hB : zdistInf 3 83 (cltMom2_a₂ - cltMom2_β1 0) = 41 := by decide
      have hG : zdistInf 3 83 (cltMom2_β1 0 - cltMom2_β1 1) = 1 := by decide
      have hA' : zdistInf 3 83 ((0 : Zd 3 83) - cltMom2_β0 0) = 41 := by decide
      have hB' : zdistInf 3 83 (cltMom2_a₂ - cltMom2_β0 0) = 41 := by decide
      simp only [cltMom2_z40, or_true, ↓reduceIte, cltMom2_c40, CltMom1.uw, CltMom1.G, hA, hB, hG, hA', hB',
        cltMom2_β0_win]
      exact le_rfl
    · simp only [cltMom2_z40, h0, h1, or_self, ↓reduceIte]
      exact hnn

/-- **Instance of `cltMom2_hzu`** (`d = 3`, `L = 83`, `w = 1`, `ρ = 40`, `M = 1`, `a₁ = 0`, `a₂ = (0,0,1)`): `z` has the value
`c₄₀ > 0` at `β⁰` and at `β'` (first labels at distance `5 ≤ 20 w = 20`, both far at `41 > 40`); the conclusion at `β'` holds
with the factor `4^d = 64`. -/
example : cltMom2_z40 cltMom2_β1 ≤
    CltMom1.uw (0 : Zd 3 83) cltMom2_a₂ 40 1 ((4 : ℝ) ^ 3 * 1) (cltMom2_β0 0) *
      CltMom1.G 3 83 1 (cltMom2_β1 0 - cltMom2_β1 1) :=
  cltMom2_hzu 3 83 (0 : Zd 3 83) cltMom2_a₂ 1 40 1 cltMom2_z40 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) cltMom2_z40_nonneg cltMom2_z40_bound cltMom2_β0 cltMom2_β1
    (by classical simpa [cltMom2_z40] using cltMom2_c40_pos)
    (by
      have : zdistInf 3 83 (cltMom2_β0 0 - cltMom2_β1 0) = 5 := by decide
      rw [this]; norm_num)

/-! ### Targets 3-6 at the merged sequence `szCL` (`L_n = 2 (n+24)^5`, `W_n = 2^{n+24}`, `ilambda ≡ 1`, `s ≡ 0`, `1 - t_n = L_n^{-2}`) -/

section SzCL

open RBM.Gauss.Step5Inst

/-- The event of `CltMom2.DomHyp` is empty at the envelope: with `Λ' = BY (w^{d-2}+1)` and `q₁ = 0`, `DomHyp` holds for
`|E| < 2`, `s < 1` (`cltMom2_norm_stcltB_le`: `|𝗕_β| ≤ BY`, and `|β₀-β₁|^{d-2} ≤ w^{d-2}` on the window). -/
private theorem cltMom2_domHyp_zero {d : ℕ} (sz : Sizes d) (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs : s < 1)
    (σ : Fin 2 → Bool) :
    CltMom2.DomHyp sz n E s σ (CltMom2.BY sz n E s σ *
      ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)) 0 := by
  intro β hβ
  have hBY0 : 0 ≤ CltMom2.BY sz n E s σ := (norm_nonneg _).trans (cltMom2_norm_stcltB_le d sz n E s σ hE hs β 0)
  have hset : {ω | CltMom2.BY sz n E s σ *
        ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1) <
      ‖STcltB sz n E s σ β ω‖ * (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have h1 := cltMom2_norm_stcltB_le d sz n E s σ hE hs β ω
    have hr : ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) ≤
        (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hβ _
    calc ‖STcltB sz n E s σ β ω‖ * (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)
        ≤ CltMom2.BY sz n E s σ * (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hBY0
  rw [hset]
  simp

/-- `|𝔼 ∏ X_k| ≤ (2 BY)^{2p}` for every tuple (`|STcltX| ≤ |STcltB| + |𝔼 STcltB| ≤ 2 BY`): `CltMom2.IsoHyp` at
`εf = (2 BY)^{2p}`. -/
private theorem cltMom2_isoHyp_envelope {d : ℕ} (sz : Sizes d) (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs : s < 1)
    (σ : Fin 2 → Bool) (p : ℕ) :
    CltMom2.IsoHyp sz n E s σ p ((2 * CltMom2.BY sz n E s σ) ^ (2 * p)) := by
  intro b _ _
  have hint : ∀ β : Fin 2 → Zd d (sz.L n),
      ‖∫ ω', STcltB sz n E s σ β ω' ∂(sz.seqP)‖ ≤ CltMom2.BY sz n E s σ := by
    intro β
    have := norm_integral_le_of_norm_le_const (μ := sz.seqP) (f := STcltB sz n E s σ β)
      (C := CltMom2.BY sz n E s σ)
      (Filter.Eventually.of_forall fun ω => cltMom2_norm_stcltB_le d sz n E s σ hE hs β ω)
    rwa [probReal_univ, mul_one] at this
  have hX : ∀ (β : Fin 2 → Zd d (sz.L n)) (cj : Bool) (ω : sz.SeqΩ),
      ‖STcltX sz n E s σ β cj ω‖ ≤ 2 * CltMom2.BY sz n E s σ := by
    intro β cj ω
    have h0 : ‖STcltB sz n E s σ β ω - ∫ ω', STcltB sz n E s σ β ω' ∂(sz.seqP)‖ ≤ 2 * CltMom2.BY sz n E s σ :=
      (norm_sub_le _ _).trans (by linarith [cltMom2_norm_stcltB_le d sz n E s σ hE hs β ω, hint β])
    cases cj
    · exact h0
    · change ‖(starRingEnd ℂ) _‖ ≤ _
      rw [RCLike.norm_conj]; exact h0
  have h := norm_integral_le_of_norm_le_const (μ := sz.seqP)
    (f := fun ω => ∏ k : Fin (2 * p), STcltX sz n E s σ (b k) (decide (p ≤ k.val)) ω)
    (C := (2 * CltMom2.BY sz n E s σ) ^ (2 * p)) (Filter.Eventually.of_forall fun ω => by
      rw [norm_prod]
      calc ∏ k : Fin (2 * p), ‖STcltX sz n E s σ (b k) (decide (p ≤ k.val)) ω‖
          ≤ ∏ _k : Fin (2 * p), (2 * CltMom2.BY sz n E s σ) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hX _ _ _
        _ = (2 * CltMom2.BY sz n E s σ) ^ (2 * p) := by simp)
  rw [probReal_univ, mul_one] at h
  exact h

private theorem cltMom2_sCL_lt (n : ℕ) : sCL n < 1 := by
  change (0 : ℝ) < 1; norm_num

private theorem cltMom2_lam_pos (n : ℕ) : 0 < szCL.lam n := by
  change (0 : ℝ) < 1; norm_num

private theorem cltMom2_lam_le (n : ℕ) : szCL.lam n ≤ 1 := by
  change (1 : ℝ) ≤ 1; norm_num

private theorem cltMom2_tCL_nonneg (n : ℕ) : 0 ≤ tCL n := by
  have h := szCL_hst n
  have h0 : sCL n = 0 := rfl
  rw [h0] at h
  exact h.le

private theorem cltMom2_tCL_lt (n : ℕ) : tCL n < 1 := by
  have h := szCL_one_sub_t n
  have h2 : 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ := by
    have := szCL_two_le_L n
    positivity
  linarith

/-- `16 ≤ log W_n` for every `n` (`W_n = 2^{n+24}`, `log 2 > 0.69`). -/
private theorem cltMom2_log_W_ge (n : ℕ) : (16 : ℝ) ≤ Real.log ((szCL.W n : ℕ) : ℝ) := by
  rw [szCL_log_W]
  have := Real.log_two_gt_d9
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `40 ≤ log W_n` for `n ≥ 34`: `(n+24) log 2 ≥ 58 · 0.69 > 40`. -/
private theorem cltMom2_log_W_ge40 (n : ℕ) (hn : 34 ≤ n) : (40 : ℝ) ≤ Real.log ((szCL.W n : ℕ) : ℝ) := by
  rw [szCL_log_W]
  have := Real.log_two_gt_d9
  have h0 : (34 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

private theorem cltMom2_mE0 : (1 / 2 : ℝ) ≤ (mE 0).im := by
  rw [mE_im]
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4]; norm_num

/-- **Instance of target 4a** (`cltMom2_norm_stcltB_le`) at `szCL`, `E = 0`, `s = sCL n`, `σ = (+,-)`, every `n`. -/
example (n : ℕ) (β : Fin 2 → Zd 3 (szCL.L n)) (ω : szCL.SeqΩ) :
    ‖STcltB szCL n 0 (sCL n) ![true, false] β ω‖ ≤ CltMom2.BY szCL n 0 (sCL n) ![true, false] :=
  cltMom2_norm_stcltB_le 3 szCL n 0 (sCL n) ![true, false] (by norm_num) (cltMom2_sCL_lt n) β ω

/-- **Instance of target 4b** (`cltMom2_weight_le`) at `szCL`, `E = 0`, `s = sCL n`, `t = tCL n`, `σ = (+,-)`, `a = (0,0)`,
`Λ = 1`, `κ = 1/2`, every `n` (`2·3 ≤ log W_n` by `szCL_log_W`). -/
example (n : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ β : Fin 2 → Zd 3 (szCL.L n),
    ‖CltMom2.Z szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] β‖ *
        (1 / (((zdistInf 3 (szCL.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) ≤
      CltMom1.uw ((![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 0) ((![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 1)
          (Real.log ((szCL.W n : ℕ) : ℝ) ^ 4 * ellT (szCL.L n) (szCL.lam n) (sCL n))
          (Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) M (β 0) *
        CltMom1.G 3 (szCL.L n) (Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n))
          (β 0 - β 1) := by
  obtain ⟨M, hM, H⟩ := cltMom2_weight_le 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  refine ⟨M, hM, fun β => H szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] (by norm_num) cltMom2_mE0
    (cltMom2_lam_pos n) (cltMom2_lam_le n) (cltMom2_tCL_nonneg n) (cltMom2_tCL_lt n) (szCL_reg5I n).1
    (by push_cast; linarith [cltMom2_log_W_ge n]) β⟩

/-- **Instance of target 3** (`cltMom2_decomp`) at the same data, every `n`, every sample point `ω`. -/
example (n : ℕ) (ω : szCL.SeqΩ) :
    STfFar szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] ω -
        ∫ ω', STfFar szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] ω' ∂(szCL.seqP) =
      (((1 - sCL n) ^ 2 / (szCL.lam n ^ 4 * (szCL.lam n ^ 2 * ((szCL.W n : ℕ) : ℝ) ^ 3) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.fluc szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] ω +
        CltMom2.off szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] ω :=
  cltMom2_decomp 3 szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] (by norm_num) (cltMom2_sCL_lt n)
    (cltMom2_lam_pos n) ω

/-- **Instance of target 5** (`cltMom2_moment_fixed`) at the same data for every `n ≥ 34` (`40 ≤ log W_n`), `p = 1`,
`Λ' = BY (w + 1)`, `q₁ = 0` (the event of `DomHyp` is empty by `cltMom2_norm_stcltB_le`), `εf = (2 BY)²` (`IsoHyp` by
`|STcltX| ≤ 2 BY`). -/
example (n : ℕ) (hn : 34 ≤ n) : ∃ M : ℝ, 0 < M ∧
    (∫ ω, ‖CltMom2.fluc szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] ω‖ ^ (2 * 1) ∂(szCL.seqP) ≤
        CltMom2.rhs szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] 1 M
          (CltMom2.BY szCL n 0 (sCL n) ![true, false] *
            ((Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) ^ (3 - 2) + 1)) 0
          ((2 * CltMom2.BY szCL n 0 (sCL n) ![true, false]) ^ (2 * 1)) ∧
      ∀ θ : ℝ, 0 < θ →
        szCL.seqP {ω | θ < ‖CltMom2.fluc szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] ω‖} ≤
          ENNReal.ofReal (CltMom2.rhs szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] 1 M
            (CltMom2.BY szCL n 0 (sCL n) ![true, false] *
              ((Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) ^ (3 - 2) + 1)) 0
            ((2 * CltMom2.BY szCL n 0 (sCL n) ![true, false]) ^ (2 * 1)) / θ ^ (2 * 1))) := by
  obtain ⟨M, hM, H⟩ := cltMom2_moment_fixed 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  have hBY0 : 0 ≤ CltMom2.BY szCL n 0 (sCL n) ![true, false] :=
    (norm_nonneg _).trans (cltMom2_norm_stcltB_le 3 szCL n 0 (sCL n) ![true, false] (by norm_num)
      (cltMom2_sCL_lt n) (0 : Fin 2 → Zd 3 (szCL.L n)) 0)
  exact ⟨M, hM, H szCL n 0 (sCL n) (tCL n) ![true, false] ![0, 0] 1 _ 0 _ le_rfl (by norm_num) cltMom2_mE0
    (cltMom2_lam_pos n) (cltMom2_lam_le n) (cltMom2_sCL_lt n) (cltMom2_tCL_nonneg n) (cltMom2_tCL_lt n)
    (szCL_reg5I n).1 (cltMom2_log_W_ge40 n hn) (by push_cast; linarith [cltMom2_log_W_ge n]) le_rfl
    (by positivity) (cltMom2_domHyp_zero szCL n (by norm_num) (cltMom2_sCL_lt n) _)
    (cltMom2_isoHyp_envelope szCL n (by norm_num) (cltMom2_sCL_lt n) _ 1)⟩


private theorem cltMom2_zCL_im (n : ℕ) : 0 < (zCL n).im := by
  have hL := szCL_two_le_L n
  change 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ / 2
  positivity

/-- The energies `E_n = lemE (zCL n)` of the flow of `szCL` satisfy `|E_n| ≤ 1/2` (`|lemE z| ≤ |Re z|`, `Re zCL = 1/2`). -/
private theorem cltMom2_zCL_E (n : ℕ) : |STflowE zCL n| ≤ 1 / 2 :=
  (abs_lemE_le (cltMom2_zCL_im n)).trans (by simp [zCL])

/-- `1/2 ≤ Im mE(E_n)` along the flow of `szCL` (`E_n² ≤ 1/4`; the argument of `lemT_zCL`, `Step5Pins.lean:752`). -/
private theorem cltMom2_zCL_mE (n : ℕ) : (1 / 2 : ℝ) ≤ (mE (STflowE zCL n)).im := by
  have hE := cltMom2_zCL_E n
  have hE2 : (STflowE zCL n) ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 hE
    nlinarith [this.1, this.2]
  rw [mE_im]
  have h4 : (1 : ℝ) ≤ Real.sqrt (4 - (STflowE zCL n) ^ 2) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- **Instance of target 6** (`cltMom2_tail_eventually`) at `(szCL, STflowE zCL, sCL, tCL)`, `Λ = 1`, `κ = 1/20`, `p = 1`,
`D = 1`, `σ = (+,-)`, `a = (0,0)`: `STCltIsoConcl` comes from the merged `inst_cltIso (stCltIso_holds 3) 1 one_pos`, whose
stochastic premises (`STKbound … STLKU`, other gates' pins) stay hypotheses of the example; every per-`n` premise of the
conclusion is discharged for `n ≥ 34` (`|E_n| ≤ 1/2 < 2`, `1/20 ≤ 1/2 ≤ Im mE(E_n)`, regime from `szCL_reg5I`,
`40 ≤ log W_n`, `2·3 ≤ log W_n`), and `DomHyp` holds with `q₁ = 0` at `Λ' = BY (w + 1)`. -/
example (hK : STKbound szCL (STflowE zCL)) (hKw : STKward szCL (STflowE zCL)) (ha : STLK szCL (STflowE zCL) sCL)
    (hD : STDecay szCL (STflowE zCL) sCL) (hDS : STDecayStrong szCL (STflowE zCL) sCL)
    (h1 : STStep1Loop szCL (STflowE zCL) sCL tCL) (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1)
    (h3 : STLmaxU szCL (STflowE zCL) sCL tCL) (h4 : STLKU szCL (STflowE zCL) sCL tCL) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, ∀ θ : ℝ, 0 < θ →
      szCL.seqP {ω | θ < ‖CltMom2.fluc szCL n (STflowE zCL n) (sCL n) (tCL n) ![true, false] ![0, 0] ω‖} ≤
        ENNReal.ofReal (CltMom2.rhs szCL n (STflowE zCL n) (sCL n) (tCL n) ![true, false] ![0, 0] 1 M
          (CltMom2.BY szCL n (STflowE zCL n) (sCL n) ![true, false] *
            ((Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) ^ (3 - 2) + 1)) 0
          (((szCL.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) / θ ^ (2 * 1)) := by
  obtain ⟨𝔠d, -, -, Hiso⟩ := inst_cltIso (stCltIso_holds 3) 1 one_pos
  have hiso : STCltIsoConcl szCL (STflowE zCL) sCL tCL := Hiso hK hKw ha hD hDS h1 h2 h3 h4
  obtain ⟨M, hM, H⟩ := cltMom2_tail_eventually 3 le_rfl 1 (1 / 20) one_pos (by norm_num)
  refine ⟨M, hM, ?_⟩
  filter_upwards [H szCL (STflowE zCL) sCL tCL hiso 1 le_rfl 1 one_pos, eventually_ge_atTop 34] with n hn hn34 θ hθ
  have hE2 : |STflowE zCL n| < 2 := lt_of_le_of_lt (cltMom2_zCL_E n) (by norm_num)
  exact hn ![true, false] (by decide) ![0, 0] _ 0 θ hE2 (by linarith [cltMom2_zCL_mE n]) (cltMom2_lam_pos n)
    (cltMom2_lam_le n) (cltMom2_sCL_lt n) (cltMom2_tCL_nonneg n) (cltMom2_tCL_lt n) (szCL_reg5I n).1
    (cltMom2_log_W_ge40 n hn34) (by push_cast; linarith [cltMom2_log_W_ge n]) le_rfl
    (cltMom2_domHyp_zero szCL n hE2 (cltMom2_sCL_lt n) _) hθ

/-- **Nonvacuity** (CLAUDE.md §4 step 2): for every `n`, the label `β⁰ = (x_n, x_n)` (`|x_n|_∞ = (n+24)^5 > (log W_n)^4`,
`zdistInf_xCL`) satisfies the condition of `CltMom2.Z` at `(szCL, n, s = 0, a = (0,0))`: far from both `a_i` at
`(log W)⁴ ℓ_s` and in the window `|β₀ - β₁| = 0 ≤ (log W)³ ℓ_s`. -/
example (n : ℕ) :
    Real.log ((szCL.W n : ℕ) : ℝ) ^ 4 * ellT (szCL.L n) (szCL.lam n) (sCL n) <
        ((zdistInf 3 (szCL.L n) ((![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n)) 0 -
          (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 0) : ℕ) : ℝ) ∧
      Real.log ((szCL.W n : ℕ) : ℝ) ^ 4 * ellT (szCL.L n) (szCL.lam n) (sCL n) <
        ((zdistInf 3 (szCL.L n) ((![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n)) 0 -
          (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 1) : ℕ) : ℝ) ∧
      ((zdistInf 3 (szCL.L n) ((![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n)) 0 -
          (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n)) 1) : ℕ) : ℝ) ≤
        Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n) := by
  have hlog := szCL_log_W_le n
  have h16 := cltMom2_log_W_ge n
  have hx : ∀ i : Fin 2, (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n)) 0 - (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) i = xCL n := by
    intro i; fin_cases i <;> simp
  have hfar : Real.log ((szCL.W n : ℕ) : ℝ) ^ 4 * ellT (szCL.L n) (szCL.lam n) (sCL n) <
      (((n + 24) ^ 5 : ℕ) : ℝ) := by
    rw [szCL_ellT_s, mul_one]
    push_cast
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h4 : Real.log ((szCL.W n : ℕ) : ℝ) ^ 4 ≤ ((n : ℝ) + 24) ^ 4 :=
      pow_le_pow_left₀ (by linarith) hlog 4
    have : ((n : ℝ) + 24) ^ 4 < ((n : ℝ) + 24) ^ 5 :=
      pow_lt_pow_right₀ (by linarith) (by norm_num)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hx, zdistInf_xCL]; exact hfar
  · rw [hx, zdistInf_xCL]; exact hfar
  · have h0 : (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n)) 0 - (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n)) 1 = 0 := by
      simp
    rw [h0, szCL_ellT_s, mul_one]
    have : zdistInf 3 (szCL.L n) (0 : Zd 3 (szCL.L n)) = 0 := by simp [zdistInf]
    rw [this]
    have : (0 : ℝ) ≤ Real.log ((szCL.W n : ℕ) : ℝ) := by linarith
    simp only [Nat.cast_zero]
    positivity

/-- **Nonvacuity** of the isolated/paired split at `p = 1`: `(β⁰, β⁰)` is paired at `10 w`, `w = (log W_n)³ ℓ_s`, for
every `n` (the first labels coincide). -/
example (n : ℕ) :
    CltMom1.Paired (10 * (Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)))
      (fun _ : Fin (2 * 1) => (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) := by
  have h16 := cltMom2_log_W_ge n
  have hpos : 0 < 10 * (Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) := by
    rw [szCL_ellT_s, mul_one]
    have : 0 < Real.log ((szCL.W n : ℕ) : ℝ) := by linarith
    positivity
  have hz0 : zdistInf 3 (szCL.L n) (0 : Zd 3 (szCL.L n)) = 0 := by simp [zdistInf]
  have hd : ∀ i k : Fin (2 * 1),
      ((zdistInf 3 (szCL.L n) (((fun _ : Fin (2 * 1) => (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) i) 0 -
        ((fun _ : Fin (2 * 1) => (![xCL n, xCL n] : Fin 2 → Zd 3 (szCL.L n))) k) 0) : ℕ) : ℝ) <
        10 * (Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n)) := by
    intro i k
    rw [sub_self, hz0, Nat.cast_zero]
    exact hpos
  intro i
  by_cases hi : i = 0
  · subst hi
    exact ⟨1, by decide, hd 0 1⟩
  · exact ⟨0, fun h => hi h.symm, hd i 0⟩

end SzCL

end Instances


#print axioms cltMom2_expand
#print axioms cltMom2_moment_le
#print axioms cltMom2_markov
#print axioms cltMom2_decomp
#print axioms cltMom2_norm_stcltB_le
#print axioms cltMom2_weight_le
#print axioms cltMom2_hzu
#print axioms cltMom2_moment_fixed
#print axioms cltMom2_tail_eventually

end RBM.Evol

end

