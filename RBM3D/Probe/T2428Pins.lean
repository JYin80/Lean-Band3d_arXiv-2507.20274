/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.Chain.Step2Kern
import RBM3D.BA.KInduct
import RBM3D.BA.EMn2BA
import RBM3D.Induction.LoopGenN
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.Step2Core
import RBM3D.Path.DifREP3

/-!
# T2428 probe (BA stage TL, row TL2a, probe step): the twisted loop hierarchy and its grid form

Never merged; ticket `docs/tickets/T2428.md`, report `docs/reports/T2428-prove.md` (a″).  Statements only: every pin is a `Prop`-valued `def`
(as `t/T2413:RBM3D/Probe/T2413Pins.lean`), the only proofs are the `example`s (`rfl` bridges, the two drift-kernel bridges, the instances).
Section 1: target 1 (matrix-level vocabulary at the carrier `baStep2Mat sz lam0 E`, bridges to TL0 by `rfl`).  Section 2: targets 2, 3
(`BATwistGen`, `BATwistHier`) and the `BAuKer` semigroup pin.  Section 3: the path level, target 4 (`BATwistDuhamel`, `BATwistGridMart`) and
its split into the three parts of item (v).  Section 4: item (iii), the drift kernel.  Section 5: the instances (`d = 3`, `sz0`, `zSeq`, `n = 0`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Target 1: the matrix-level vocabulary at `baStep2Mat sz lam0 E`

`G_u(H) = Gres H (ztOf m E u) true` is the convention of `baStep2Mat.LM`, `.GMM` (`BA/Step2BA.lean:54-74`); every object is the
TL0 object of `BA/TwistPins.lean` with `C.G n u ω` replaced by `G_u(H)`, so the bridge at `H = sz.seqHflowBA lam0 n u ω` is `rfl`. -/

section Vocab
variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- `G_u(H)` of a fine matrix `H`, as entries. -/
def twGM (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ :=
  fun x y => Gres H (ztOf (BAmF sz lam0 E n) (E n) u) true x y
/-- `L̃_{σ,(a;c₁,c₂)}(H) = Tr(G(σ₁) E_a G(σ₂) P_{c₁c₂})`. -/
def twL2M (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  twLoopX n (twChg (twGM sz lam0 E n u H) (σ 0)) (twChg (twGM sz lam0 E n u H) (σ 1)) a c₁ c₂
/-- `L̃^{(3)}_{σ,(a₁,a₂;c₁,c₂)}(H) = Tr(G(σ₁) E_{a₁} G(σ₂) E_{a₂} G(σ₃) P_{c₁c₂})`. -/
def twL3M (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 3 → Bool) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 * ∑ x ∈ twBlk n a₁, ∑ y ∈ twBlk n a₂, ∑ w ∈ twBlk n c₁,
    twChg (twGM sz lam0 E n u H) (σ 0) (twShift n c₂ w) x * twChg (twGM sz lam0 E n u H) (σ 1) x y * twChg (twGM sz lam0 E n u H) (σ 2) y w
/-- `Ẽ^{G̊}(H)`, `Tr(G̊(σ) E_{a'}) = 𝓛^{(1)}_{σ,a'} - m(σ)` (`LM` of the carrier). -/
def twEGM (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  let tr : Bool → Zd d (sz.L n) → ℂ := fun τ a' => (baStep2Mat sz lam0 E).LM n u H ![τ] ![a'] - (if τ then BAmF sz lam0 E n else (starRingEnd ℂ) (BAmF sz lam0 E n));
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a', (tr (σ 0) a' * twL3M sz lam0 E n u H ![σ 0, σ 0, σ 1] a' a c₁ c₂ + tr (σ 1) a' * twL3M sz lam0 E n u H ![σ 0, σ 1, σ 1] a a' c₁ c₂)
/-- `B̃₁(H)(a) = W^d Σ_b K̃(b) (𝓛-𝒦)^{(2)}_{σ,(a,b)}(H)`. -/
def twB1M (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b, twK (baFM sz lam0 E) n u σ b c₁ c₂ * ((baStep2Mat sz lam0 E).LM n u H σ ![a, b] - (baStep2Mat sz lam0 E).K n u σ ![a, b])
/-- `B̃₂(H)(a) = W^d Σ_b Z(b) (𝓛-𝒦)^{(2)}_{σ,(a,b)}(H)`, `Z = L̃ - K̃`. -/
def twB2M (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b, (twL2M sz lam0 E n u H σ b c₁ c₂ - twK (baFM sz lam0 E) n u σ b c₁ c₂) * ((baStep2Mat sz lam0 E).LM n u H σ ![a, b] - (baStep2Mat sz lam0 E).K n u σ ![a, b])
/-- `∂_{xy} L̃_{σ,(b;c₁,c₂)}(H) = -(G₁E_bG₂PG₁)_{yx} - (G₂PG₁E_bG₂)_{yx}` (D.2). -/
def twDerM (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  let G₁ := twChg (twGM sz lam0 E n u H) (σ 0); let G₂ := twChg (twGM sz lam0 E n u H) (σ 1);
  -((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * (∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, G₁ y z * G₂ z w * G₁ (twShift n c₂ w) x +
    ∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, G₂ y w * G₁ (twShift n c₂ w) z * G₂ z x)
/-- `(Ẽ⊗Ẽ)(H)(b,b') = Σ_{x,y} S_{xy} ∂_{xy}L̃(b) \overline{∂_{xy}L̃(b')}`, `S` the carrier's block kernel (`S^{(B)}(0) = 1`). -/
def twEEM (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (b b' c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ∑ x, ∑ y, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
    (twDerM sz lam0 E n u H σ b c₁ c₂ x y * (starRingEnd ℂ) (twDerM sz lam0 E n u H σ b' c₁ c₂ x y))
/-- `Ũ_{v,w} = BAuKer v w (σ₁, σ₂)`: the one-slot evolution kernel (`BA/EKPins.lean:49`). -/
def twU (σ : Fin 2 → Bool) (v w : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) v w (σ 0) (σ 1)
/-- `((Ũ_{v,w} ⊗ Ũ_{v,w}^{(σ̄)}) ∘ (Ẽ⊗Ẽ)_v)(a,a)`: `Σ_{b,b'} Ũ^{(σ)}(a,b) Ũ^{(σ̄)}(a,b') (Ẽ⊗Ẽ)(b,b')` (`Ũ^{(σ̄)} = conj Ũ^{(σ)}`). -/
def twEEUM (v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ∑ b, ∑ b', twU sz lam0 E n σ v w a b * twU sz lam0 E n (fun i => !σ i) v w a b' * twEEM sz lam0 E n v H σ b b' c₁ c₂

/-- The drift of (D.4) at `(u, H)`: `Θ̃_u∘Z + B̃₁ + B̃₂ + Ẽ^{G̊}`, `Θ̃_u = Θ_u M^{(σ₁σ₂)}` (`BATheta`, `BAMss`; the one-slot summand of (3.11)). -/
def twDriftM (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ((BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) * BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) *ᵥ
      fun b => twL2M sz lam0 E n u H σ b c₁ c₂ - twK (baFM sz lam0 E) n u σ b c₁ c₂) a +
    twB1M sz lam0 E n u H σ a c₁ c₂ + twB2M sz lam0 E n u H σ a c₁ c₂ + twEGM sz lam0 E n u H σ a c₁ c₂

/-- The generator of the coupling-0 walk applied to `L̃` (`genMatOf` of `Induction/LoopGenN.lean:554` with `g = 0`, for `L̃`). -/
def twGenM (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d (sz.L n) (sz.W n), ((gvarF d (sz.L n) (sz.W n) 0 c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ => twL2M sz lam0 E n u (H + (y : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c) σ a c₁ c₂)) 0 +
    deriv (fun v : ℝ => twL2M sz lam0 E n v H σ a c₁ c₂) u

end Vocab

/-! ### Bridges to TL0 (`BA/TwistPins.lean:70, 224-247`) at the flow matrix, all `rfl` -/

section Bridge
variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a b b' c₁ c₂ : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n))
example : twL2' (baFM sz lam0 E) n u ω σ a c₁ c₂ = twL2M sz lam0 E n u (sz.seqHflowBA lam0 n u ω) σ a c₁ c₂ := rfl
example (σ3 : Fin 3 → Bool) : twL3 (baFM sz lam0 E) n u ω σ3 a b c₁ c₂ = twL3M sz lam0 E n u (sz.seqHflowBA lam0 n u ω) σ3 a b c₁ c₂ := rfl
example : twEG (baFM sz lam0 E) n u ω σ a c₁ c₂ = twEGM sz lam0 E n u (sz.seqHflowBA lam0 n u ω) σ a c₁ c₂ := rfl
example : twB1 (baFM sz lam0 E) n u ω σ a c₁ c₂ = twB1M sz lam0 E n u (sz.seqHflowBA lam0 n u ω) σ a c₁ c₂ := rfl
example : twB2 (baFM sz lam0 E) n u ω σ a c₁ c₂ = twB2M sz lam0 E n u (sz.seqHflowBA lam0 n u ω) σ a c₁ c₂ := rfl
example : twDer (baFM sz lam0 E) n u ω σ b c₁ c₂ x y = twDerM sz lam0 E n u (sz.seqHflowBA lam0 n u ω) σ b c₁ c₂ x y := rfl
example : twEE (baFM sz lam0 E) n u ω σ b b' c₁ c₂ = twEEM sz lam0 E n u (sz.seqHflowBA lam0 n u ω) σ b b' c₁ c₂ := rfl
end Bridge

/-! ## 2. Targets 2, 3: T.8 and T.9 (D.1), (D.4)

T.8: `L̃` has the generator `W^d Σ_b L̃(b) 𝓛^{(2)}_{σ,(a,b)} + Ẽ^{G̊}` (the twist vertex `P_{c₁c₂}` is never cut; `S^{(B)}(0) = 1`, `EMn2BA_SB_zero`).
The loop `𝓛^{(2)}_{σ,(a,b)}` is `(baStep2Mat sz lam0 E).LM n u H σ ![a, b]`.  Hypotheses: `Im m > 0`, `u < 1`, `H` Hermitian; no `3 ≤ L`, no `0 ≤ u`.
T.9: `generator(L̃) - ∂_u K̃ = Θ̃_u∘Z + B̃₁ + B̃₂ + Ẽ^{G̊}`; `∂_u K̃` is the derivative of the explicit `twK` (`BATheta_hasDerivAt`, `twK_ba`),
`𝒦^{(2)} = W^{-d} Θ M^{(σ₁σ₂)}` is `baKsol_two`.  Hypotheses: `BAReal`, `0 < g₀`, `0 ≤ u < 1`, `H` Hermitian, `3 ≤ L` (`baKsol_two`). -/

section Gen
variable {d : ℕ}

/-- **Target 2, T.8 (D.1)** (twin of `loopGenNOf`, `Induction/LoopGenN.lean:567`): the generator of the coupling-0 walk applied to `L̃` is `W^d Σ_b L̃(b) 𝓛^{(2)}_{σ,(a,b)} + Ẽ^{G̊}`. -/
def BATwistGen (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im → ∀ u : ℝ, u < 1 →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
      twGenM sz lam0 E n u H σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b, twL2M sz lam0 E n u H σ b c₁ c₂ * (baStep2Mat sz lam0 E).LM n u H σ ![a, b] +
        twEGM sz lam0 E n u H σ a c₁ c₂

/-- **Target 3, T.9 (D.4)** (twin of `loopDrift_sub_K_deriv_n`, `Induction/HierAlgebra.lean:729`, with `hierarchyN_of_loopGenN`, `Induction/HierarchyN.lean:69`):
`generator(L̃) - ∂_u K̃ = Θ̃_u∘Z + B̃₁ + B̃₂ + Ẽ^{G̊}`. -/
def BATwistHier (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ → 0 < lam0 n → BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
    ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
        twGenM sz lam0 E n u H σ a c₁ c₂ - deriv (fun v : ℝ => twK (baFM sz lam0 E) n v σ a c₁ c₂) u = twDriftM sz lam0 E n u H σ a c₁ c₂

/-- The semigroup law of `Ũ = BAuKer` (measure-free; `Ũ_{v,v} = 1`, `Ũ_{v,w} Ũ_{u,v} = Ũ_{u,w}` for `0 ≤ v, w < 1`; from `BATheta_resolvent`, `BAuKer_eq_one_add`). -/
def BAuKerSemigroup (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ (σ₁ σ₂ : Bool) (u v w : ℝ), 0 ≤ v → v < 1 → 0 ≤ w → w < 1 →
    BAuKer d L g E m v v σ₁ σ₂ = 1 ∧ BAuKer d L g E m v w σ₁ σ₂ * BAuKer d L g E m u v σ₁ σ₂ = BAuKer d L g E m u w σ₁ σ₂

end Gen

/-! ## 3. Target 4: the grid walk (`Pp = pathP (sz.withLam 0)`, `Hpath = g₀ Ψ + pathH`), at `Flow = BAFlow`, `mk = baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`,
`T0 = BAflowT0`; the label is `i = (σ, a, c₁, c₂)`.  `A_k(a) = Z_{u_k}(H_k)(a)`. -/

section Path
variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- `A_k(a) = Z_{u_k}(H_k)(a) = L̃_{u_k}(H_k)(a) - K̃_{u_k}(a)`, `H_k = Hpath k ω`; a vector in `a`, so that `Ũ` acts by `*ᵥ`. -/
def twAk (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : Zd d (sz.L n) → ℂ := fun a =>
  twL2M sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a c₁ c₂ - twK (baFM sz lam0 E) n (gridTime s t K n k) σ a c₁ c₂
/-- `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]`. -/
def twMartInc (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : Zd d (sz.L n) → ℂ := fun a =>
  twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω a - ((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω
/-- `P_j = 𝔼[A_{j+1} | F_j] - Ũ_{u_j,u_{j+1}} A_j`. -/
def twPredInc (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : Zd d (sz.L n) → ℂ := fun a =>
  ((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω -
    (twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n (j + 1)) *ᵥ twAk sz lam0 E s t K n σ c₁ c₂ j ω) a
/-- The drift (target 3), the QV (target 1) and the `Ũ`-weighted QV at the grid state `(u_k, H_k)`. -/
def twDriftk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  twDriftM sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a c₁ c₂
def twEEk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  twEEM sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a a c₁ c₂
def twEEUk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (j k : ℕ) (ω : PathΩ sz) : ℂ :=
  twEEUM sz lam0 E n (gridTime s t K n j) (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂

/-- The canonical `Mart_k = Σ_{j<k} ξ_{j+1}` and `Rem_k = Σ_{j<k} (𝔼[A_{j+1}|F_j] - A_j - Δ Drift_j)` (twins of `difRepMartN` `:58`, `difRepRemN` `:64` of `Path/DifREP1.lean`). -/
def twMart (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, twMartInc sz lam0 E s t K n σ c₁ c₂ j ω a
def twRem (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, (((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω -
    twAk sz lam0 E s t K n σ c₁ c₂ j ω a - ((gridStep s t K n : ℝ) : ℂ) * twDriftk sz lam0 E s t K n σ a c₁ c₂ j ω)

end Path

/-- **4 (a)** (twin of `StoppedDuhamelN`, `Induction/GridDuhamelN.lean:293`): pathwise, `A_{j∧τ} = Ũ_{u₀,u_{j∧τ}} A₀ + Σ_{i<j∧τ} Ũ_{u_{i+1},u_{j∧τ}} (P_i + ξ_{i+1})`. -/
def BATwistDuhamel (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ (n : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz), min j (τ ω) ≤ K n →
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ (min j (τ ω)) ω =
          twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω))) *ᵥ
              twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ 0 ω +
            ∑ i ∈ Finset.range (min j (τ ω)), twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω))) *ᵥ
              (twPredInc sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ i ω + twMartInc sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ i ω)

/-- **4 (b)** (the shape of `STGridMartAtgL`, `Chain/Step2Gen.lean:857`, with the fourth clause of `STGridRepNAtgL`, `:994`): (i) the decomposition with the drift of target 3,
(ii) `‖Rem‖ ≤ N^{C₀} √Δ`, (iii) the martingale tail with the QV `(Ẽ⊗Ẽ)(a,a)`, (iv) the `Ũ`-weighted tail with `((Ũ⊗Ũ)∘(Ẽ⊗Ẽ))(a,a)`. -/
def BATwistGridMartAt (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
        ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
          ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) → ℕ → PathΩ sz → ℂ,
            (∀ n (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
              twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 k ω i.2.1 =
                twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 0 ω i.2.1 +
                  ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
                    twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω +
                  Rem n i k ω + Mart n i k ω) ∧
            (∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
              ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
            (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
                  ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                  ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) ∧
            (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
                  ‖twEEUk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                  ‖(∑ j ∈ Finset.range k, twU sz (BAflowLam0 sz z) (BAflowEs sz z) n i.1 (gridTime s t K n j) (gridTime s t K n k) *ᵥ
                    (fun b => Mart n (i.1, b, i.2.2.1, i.2.2.2) (j + 1) ω - Mart n (i.1, b, i.2.2.1, i.2.2.2) j ω)) i.2.1‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- `∃ C₀ ≥ 0` in front, as `STGridMartgL` (`Chain/Step2Gen.lean:882`). -/
def BATwistGridMart (d : ℕ) : Prop := ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridMartAt d C₀

/-! ### The split of 4 (b) (item (v)), as `GridRepRemNAt`, `GridRepTailNAt`, `GridRepWTailNAt` (`Path/DifREP1.lean:74, 95, 112`): clauses (i)-(ii) with the canonical `Mart`, `Rem`; (iii); (iv). -/

def BATwistGridRem (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
        (∀ n (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
          twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 k ω i.2.1 =
            twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 0 ω i.2.1 + ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
              twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω +
            twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω + twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω) ∧
        (∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
          ‖twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n))

def BATwistGridTail (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
          ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
            ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
          ‖twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

def BATwistGridWTail (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
          ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
            ‖twEEUk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
          ‖(∑ j ∈ Finset.range k, twU sz (BAflowLam0 sz z) (BAflowEs sz z) n i.1 (gridTime s t K n j) (gridTime s t K n k) *ᵥ
            (fun b => twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 b i.2.2.1 i.2.2.2 (j + 1) ω -
              twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 b i.2.2.1 i.2.2.2 j ω)) i.2.1‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- The assembly of the three parts into 4 (b) (twin of `stGridMartAt_of_parts2`, `Path/DifREP1.lean:1276`: `CK := max`, `∃ Mart Rem := twMart, twRem`, `N^{CK} ≤ K` by monotonicity). -/
def BATwistGridAssemble : Prop :=
  ∀ (d : ℕ) (C₀ : ℝ), 0 ≤ C₀ → BATwistGridRem d C₀ → BATwistGridTail d → BATwistGridWTail d → BATwistGridMartAt d C₀

/-! ## 4. Item (iii): the drift kernel.  `Θ̃_u = Θ_u M^{(σ₀σ₁)}` is T8b's `Step2Gen_thetaKer` (`X Θ_u(X)`, `X = M^{(σσ')} S`, `S = 1`) and `Ũ = BAuKer`
is `Step2Gen_uKer`; the two bridge lemmas (here for every `sz`, `lam0`, `E`, `n`).  The diagonal `2 m m' (1 - u m m')⁻¹` of the pre-T8b operator does not occur. -/

section Kern
variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0)
include hIm
example (σ : Fin 2 → Bool) (u : ℝ) : BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
    BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) = Step2Gen_thetaKer (baFM sz lam0 E) n (σ 0) (σ 1) u :=
  (Step2Kern_thetaKer_BA sz lam0 E n hIm (σ 0) (σ 1) u).symm
example (σ : Fin 2 → Bool) (v w : ℝ) : twU sz lam0 E n σ v w = Step2Gen_uKer (baFM sz lam0 E) n (σ 0) (σ 1) v w :=
  (Step2Kern_uKer_BA sz lam0 E n hIm (σ 0) (σ 1) v w).symm
end Kern

/-! ## 5. The instances (`d = 3`, `sz0`: `L = 4`, `W = 32`, `lam = 1/64`, `n = 0`, `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`; `σ = (false, true)`, `c₁ = 0`,
`c₂ = (1,0,0)`; `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` by `t0_sz0`).  The pins are hypotheses; every deterministic hypothesis is discharged. -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.EKPinsInst

/-- Target 2 (T.8) at a Hermitian `H = seqHflowBA ..` (all samples), `u = 1/2 < 1`, `Im m > 0` (`BAmF_sz0_im_pos`). -/
example (h : BATwistGen 3) (ω : sz0.SeqΩ) :=
  h sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 (BAmF_sz0_im_pos 0) (1 / 2) (by norm_num) _
    (EMn2BA_seqHflowBA_herm sz0 (BAflowLam0 sz0 zSeq) 0 (1 / 2) ω) ![false, true] 0 0 ![1, 0, 0]
/-- Target 3 (T.9): `BAReal` from `BAflow_real`, `0 < g₀` (`gI_pos`), `κ = 1/2`, `u = 1/2`. -/
example (h : BATwistHier 3) (ω : sz0.SeqΩ) :=
  h sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 (1 / 2) (by norm_num) gI_pos
    (BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0) (1 / 2) (by norm_num) (by norm_num) _
    (EMn2BA_seqHflowBA_herm sz0 (BAflowLam0 sz0 zSeq) 0 (1 / 2) ω) ![false, true] 0 0 ![1, 0, 0]
/-- The semigroup law at the flow datum (`hrI`), `v = 1/4`, `w = 1/2`, `u = 2/3`. -/
example (h : BAuKerSemigroup 3) := h (sz0.L 0) gI (1 / 2) EI mI hrI false true (2 / 3) (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
/-- Target 4 (a): the grid `K ≡ 4` (`Δ = 1/24`) on `[1/2, 2/3]`, `τ ≡ 3`, `j = 3`, `n = 0`: a three-step Duhamel sum. -/
example (h : BATwistDuhamel 3) (ω : PathΩ sz0) :=
  h (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) (fun _ => 4) (fun _ => by norm_num) 0 ![false, true] 0 ![1, 0, 0]
    (fun _ => 3) 3 ω (by norm_num)
/-- Target 4 (b): the pin at `(sz0, zSeq)`, any `D > 0`, the grid `K_n = ⌈N_n^{CK}⌉ + 1` (`≠ 0`, eventually `≥ N^{CK}`); `this` is the conclusion `∃ Mart Rem, (i)-(iv)`. -/
example (h : BATwistGridMart 3) {D : ℝ} (hD : 0 < D) : True := by
  obtain ⟨C₀, hC₀, H⟩ := h
  obtain ⟨CK, hCK, H2⟩ := H (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) D hD
  have := H2 (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _))
  trivial
end Inst

#check @twGM
#check @twL2M
#check @twL3M
#check @twEGM
#check @twB1M
#check @twB2M
#check @twDerM
#check @twEEM
#check @twEEUM
#check @twU
#check @twDriftM
#check @twGenM
#check @twAk
#check @twMartInc
#check @twPredInc
#check @twDriftk
#check @twEEk
#check @twEEUk
#check @BATwistGen
#check @BATwistHier
#check @BAuKerSemigroup
#check @BATwistDuhamel
#check @BATwistGridMartAt
#check @BATwistGridMart
-- merged names the proofs rely on (verified by this compile)
#check @sum_allCoords_trace_blocks
#check @hasDerivAt_green_moving
#check @RBM.Path.gridTransferPT
#check @RBM.Path.oneStepEnvelope
#check @RBM.Ind.azumaRandProxy_max
#check @RBM.Ind.difRep2_peel
#check @RBM.Ind.difRep2_peel_N
#check @RBM.Ind.difRepTail_condMGF_Z
#check @RBM.Path.duhamel_telescope_stopped
#check @RBM.Gauss.Sizes.ST_pathP_eq_seqP
#check @RBM.Gauss.Sizes.ST_whp_grid
#check @RBM.Path.OneStep_sum_coord
#check @EMn2BA_SB_zero
#check @baKsol_two
#check @BAflow_real
#check @BATheta_hasDerivAt

end RBM.BA
