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
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Path.OneStep

/-!
# BA stage TL, row TL2a (T2428), matrix level: the twisted loop hierarchy (T.8, T.9)

Ticket `docs/tickets/T2428.md` with Amend 1 (`docs/tickets/T2428-amend-1.md`); probe
`RBM3D/Probe/T2428Pins.lean` at `f6c3866` (branch `t/T2428`, never merged); proofs
`docs/tickets/T2398-TL-proofs.md` T.8, T.9 ((D.1), (D.4)); paper arXiv:2507.20274.  No measure
occurs in this file: the path level (the grid Duhamel identity and the grid martingale
decomposition) is `RBM3D/BA/TwistGrid2.lean`.

* **Target 1, the vocabulary** of a fine matrix `H` at the carrier `baStep2Mat sz lam0 E`:
  `twGM` (`G_u(H)`), `twL2M` (`L̃`), `twL3M` (`L̃^{(3)}`), `twEGM` (`Ẽ^{G̊}`), `twB1M`, `twB2M`
  (`B̃₁`, `B̃₂`), `twDerM` (`∂_{xy} L̃`), `twEEM` (`Ẽ⊗Ẽ`), `twU` (`Ũ = BAuKer`), `twEEUM`
  (`(Ũ⊗Ũ)∘(Ẽ⊗Ẽ)`), `twDriftM` (the drift of (D.4)), `twGenM` (the generator of the coupling-0
  walk applied to `L̃`), with the seven `rfl` bridges `twL2M_eq`, `twL3M_eq`, `twEGM_eq`,
  `twB1M_eq`, `twB2M_eq`, `twDerM_eq`, `twEEM_eq` to TL0 (`BA/TwistPins.lean:70, 224-247`) at `H
  = sz.seqHflowBA lam0 n u ω`.

* **`BAuKerSemigroup`** (`BAuKerSemigroup_holds`, `BAuKer_self`, `BAuKer_comp`): the semigroup
  law of `Ũ = BAuKer` for `0 ≤ v, w < 1`.

* **Item (iii)** `twTheta_eq_thetaKer`, `twU_eq_uKer`: the drift kernel `Θ_u M^{(σ₀σ₁)}` and `Ũ`
  are T8b's `Step2Gen_thetaKer`, `Step2Gen_uKer`.

* **Target 2, T.8** `BATwistGen`, `BATwistGen_holds` (D.1): for Hermitian `H`, `0 < Im m`, `u <
  1`, the generator of the coupling-0 walk applied to `L̃` is `W^d Σ_b L̃(b) 𝓛^{(2)}_{σ,(a,b)} +
  Ẽ^{G̊}`.  The route is the direct `n = 2` Itô computation (the twist vertex `P_{c₁c₂}` is
  never cut), the twisted twin of `DriftAlgebra_loopGen_core` (`Path/DriftAlgebra.lean:429`) at
  the block-product index: the line Hessian of `Tr(G₁ E_a G₂ P)` (`TwistGrid_second`), the
  coordinate contraction `sum_allCoords_trace_blocks` at `S^{(B)}(0) = I` (`EMn2BA_SB_zero`),
  the spectral derivative `∂_u G(z_u) = -m(σ) G²`, and `Σ_p E_p = W^{-d}`.

* **Target 3, T.9** `BATwistHier`, `BATwistHier_holds` (D.4): under `BAReal`, `generator(L̃) -
  ∂_u K̃ = Θ̃_u∘Z + B̃₁ + B̃₂ + Ẽ^{G̊}`; `∂_u K̃` from `BATheta_hasDerivAt`, `𝒦^{(2)} = W^{-d} Θ
  M^{(σ₀σ₁)}` from `baKsol_two`.

Every statement is for every `d` (no `3 ≤ d`); `3 ≤ L` is `sz.three_le_L`.  Every other helper
is `private` and prefixed `TwistGrid_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

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

/-! ## 2. The semigroup law of `Ũ = BAuKer` (`BAuKerSemigroup`)

`Ũ_{v,w} = (1 - v M)(1 - w M)⁻¹` with `M = M^{(σ₁σ₂)}` commuting with `Θ_w = (1 - w M)⁻¹` (`BATheta_resolvent`), so `Ũ_{v,v} = 1` and
`Ũ_{v,w} Ũ_{u,v} = Ũ_{u,w}` for `0 ≤ v, w < 1`; no condition on `u`. -/

section Semigroup

variable {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

private theorem TwistGrid_uKer_alg {R : Type*} [Ring R] [Algebra ℂ R] (X Tv Tw : R) (u v : ℂ)
    (hv : (1 - v • X) * Tv = 1) (cw : Commute X Tw) :
    (1 - v • X) * Tw * ((1 - u • X) * Tv) = (1 - u • X) * Tw := by
  have cXu : Commute X (1 - u • X) := (Commute.one_right X).sub_right ((Commute.refl X).smul_right u)
  have c1 : Commute (1 - v • X) Tw := (Commute.one_left _).sub_left (cw.smul_left v)
  have c2 : Commute Tw (1 - u • X) := ((Commute.one_left _).sub_left (cw.smul_left u)).symm
  have c3 : Commute (1 - v • X) (1 - u • X) := (Commute.one_left _).sub_left (cXu.smul_left v)
  calc (1 - v • X) * Tw * ((1 - u • X) * Tv) = (1 - v • X) * (1 - u • X) * (Tw * Tv) := by
        rw [Commute.mul_mul_mul_comm c2]
    _ = (1 - u • X) * (1 - v • X) * (Tw * Tv) := by rw [c3.eq]
    _ = (1 - u • X) * Tw * ((1 - v • X) * Tv) := by rw [Commute.mul_mul_mul_comm c1]
    _ = (1 - u • X) * Tw := by rw [hv, mul_one]

private theorem TwistGrid_uKer_left (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) * BATheta d L g E m t σ₁ σ₂ = 1 := by
  have h := (BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂).1
  rw [sub_mul, one_mul, smul_mul_assoc]
  linear_combination (norm := module) h

private theorem TwistGrid_uKer_comm (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    Commute (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) (BATheta d L g E m t σ₁ σ₂) := by
  have h := BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂
  by_cases h0 : t = 0
  · subst h0
    have : BATheta d L g E m 0 σ₁ σ₂ = 1 := by simpa using h.1
    rw [this]; exact Commute.one_right _
  · have hc : (t : ℂ) ≠ 0 := by exact_mod_cast h0
    have h2 : (t : ℂ) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂) =
        (t : ℂ) • (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) :=
      add_left_cancel (h.1.symm.trans h.2)
    exact smul_right_injective _ hc h2

/-- `Ũ_{v,v} = 1` for `0 ≤ v < 1`. -/
theorem BAuKer_self (hr : BAReal d L g κ E m) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (σ₁ σ₂ : Bool) :
    BAuKer d L g E m v v σ₁ σ₂ = 1 := TwistGrid_uKer_left hr hv0 hv1 σ₁ σ₂

/-- `Ũ_{v,w} Ũ_{u,v} = Ũ_{u,w}` for `0 ≤ v, w < 1` (no condition on `u`). -/
theorem BAuKer_comp (hr : BAReal d L g κ E m) {u v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) (σ₁ σ₂ : Bool) :
    BAuKer d L g E m v w σ₁ σ₂ * BAuKer d L g E m u v σ₁ σ₂ = BAuKer d L g E m u w σ₁ σ₂ :=
  TwistGrid_uKer_alg _ _ _ _ _ (TwistGrid_uKer_left hr hv0 hv1 σ₁ σ₂) (TwistGrid_uKer_comm hr hw0 hw1 σ₁ σ₂)

end Semigroup

/-- The semigroup law of `Ũ = BAuKer` (measure-free; `Ũ_{v,v} = 1`, `Ũ_{v,w} Ũ_{u,v} = Ũ_{u,w}` for `0 ≤ v, w < 1`; from `BATheta_resolvent`). -/
def BAuKerSemigroup (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ (σ₁ σ₂ : Bool) (u v w : ℝ), 0 ≤ v → v < 1 → 0 ≤ w → w < 1 →
    BAuKer d L g E m v v σ₁ σ₂ = 1 ∧ BAuKer d L g E m v w σ₁ σ₂ * BAuKer d L g E m u v σ₁ σ₂ = BAuKer d L g E m u w σ₁ σ₂

theorem BAuKerSemigroup_holds (d : ℕ) : BAuKerSemigroup d := fun _ _ _ _ _ _ hr σ₁ σ₂ _ _ _ hv0 hv1 hw0 hw1 =>
  ⟨BAuKer_self hr hv0 hv1 σ₁ σ₂, BAuKer_comp hr hv0 hv1 hw0 hw1 σ₁ σ₂⟩

/-! ## 3. Item (iii): the drift kernel.  `Θ̃_u = Θ_u M^{(σ₀σ₁)}` is T8b's `Step2Gen_thetaKer` (`X Θ_u(X)`, `X = M^{(σσ')} S`, `S = 1`) and `Ũ = BAuKer`
is `Step2Gen_uKer` (`Chain/Step2Gen.lean:188, 192`); the diagonal `2 m m' (1 - u m m')⁻¹` of the pre-T8b operator does not occur. -/

section Kern
variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0)
include hIm

theorem twTheta_eq_thetaKer (σ : Fin 2 → Bool) (u : ℝ) :
    BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
      BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) = Step2Gen_thetaKer (baFM sz lam0 E) n (σ 0) (σ 1) u :=
  (Step2Kern_thetaKer_BA sz lam0 E n hIm (σ 0) (σ 1) u).symm

theorem twU_eq_uKer (σ : Fin 2 → Bool) (v w : ℝ) :
    twU sz lam0 E n σ v w = Step2Gen_uKer (baFM sz lam0 E) n (σ 0) (σ 1) v w :=
  (Step2Kern_uKer_BA sz lam0 E n hIm (σ 0) (σ 1) v w).symm

end Kern

/-! ## 4. The twisted loops as traces at the block-product index (private helpers)

`P_{c₁c₂} = W^{-d} Σ_o |(c₁,o)⟩⟨(c₂,o)|` on `Vtx d L W` and the reindexing of the block sums `twBlk` over `Idx` to sums over `Vtx`
(`splitEquiv`): `twLoopX` and `twL3M` are `Tr(X₁ E_a X₂ P)`, `Tr(X₀ E_{a₁} X₁ E_{a₂} X₂ P)` for the resolvent `Gres (blockMat H)`. -/

section Conv
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `P_{c₁c₂} = W^{-d} Σ_o |(c₁,o)⟩⟨(c₂,o)|` on the block-product index. -/
private def TwistGrid_Pb (c₁ c₂ : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.of fun p q => if p.1 = c₁ ∧ q.1 = c₂ ∧ p.2 = q.2 then ((W : ℂ) ^ d)⁻¹ else 0

private theorem TwistGrid_trace_Pb (c₁ c₂ : Zd d L) (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (M * TwistGrid_Pb c₁ c₂) =
      ((W : ℂ) ^ d)⁻¹ * ∑ q : Vtx d L W, if q.1 = c₁ then M (c₂, q.2) q else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, TwistGrid_Pb, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q.1 = c₁
  · simp only [hq, true_and, ite_true]
    rw [Finset.sum_eq_single (c₂, q.2)]
    · simp
      ring
    · intro i _ hi
      have : ¬ (i.1 = c₂ ∧ q.2 = i.2) := by
        rintro ⟨h1, h2⟩
        exact hi (Prod.ext h1 h2.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [hq]

private theorem TwistGrid_mul_Eblk_mul_apply (M N : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) (i j : Vtx d L W) :
    (M * Eblk d L W a * N) i j = ((W : ℂ) ^ d)⁻¹ * ∑ p : Vtx d L W, if p.1 = a then M i p * N p j else 0 := by
  simp only [Matrix.mul_apply, Eblk, Matrix.diagonal_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.1 = a
  · simp [hp]; ring
  · simp [hp]

private theorem TwistGrid_sum_blk (a : Zd d L) (F : Vtx d L W → ℂ) :
    ∑ x ∈ Iblk d L W a, F (split d L W x) = ∑ p : Vtx d L W, if p.1 = a then F p else 0 := by
  simp only [Iblk, Finset.sum_filter]
  exact (splitEquiv d L W).sum_comp (fun p => if p.1 = a then F p else 0)

private theorem TwistGrid_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : (Gres H z true)ᴴ = Gres H z false := by
  have hH' : Hᴴ = H := hH
  simp only [Gres, ↓reduceIte, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hH', Complex.star_def]

private theorem TwistGrid_Gres_blockMat (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (s : Bool) :
    Gres (blockMat d L W M) z s = (Gres M z s).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold Gres
  generalize (if s then z else (starRingEnd ℂ) z) = w
  have h : blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - w • 1).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    simp [blockMat, Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]

/-- `Gres (blockMat H) z σ` read at `(split x, split y)` is `twChg` of the fine resolvent (Hermitian `H`). -/
private theorem TwistGrid_Gres_blockMat_apply {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (s : Bool) (x y : Idx d L W) :
    Gres (blockMat d L W H) z s (split d L W x) (split d L W y) = twChg (fun x y => Gres H z true x y) s x y := by
  rw [TwistGrid_Gres_blockMat]
  have hx : (splitEquiv d L W).symm (split d L W x) = x := (splitEquiv d L W).symm_apply_apply x
  have hy : (splitEquiv d L W).symm (split d L W y) = y := (splitEquiv d L W).symm_apply_apply y
  rw [Matrix.submatrix_apply]
  change Gres H z s ((splitEquiv d L W).symm ((splitEquiv d L W) x)) ((splitEquiv d L W).symm ((splitEquiv d L W) y)) = _
  rw [(splitEquiv d L W).symm_apply_apply, (splitEquiv d L W).symm_apply_apply]
  cases s
  · simp only [twChg, Bool.false_eq_true, ite_false]
    rw [← TwistGrid_Gres_conjTranspose hH z]
    rfl
  · rfl

end Conv

section Conv2
variable {d : ℕ} {sz : Sizes d} (n : ℕ)

private theorem TwistGrid_split_shift (c : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    split d (sz.L n) (sz.W n) (twShift n c x) = (c, (split d (sz.L n) (sz.W n) x).2) :=
  (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _

/-- `twLoopX` of block-product matrices is the trace of the word `X₁ E_a X₂ P_{c₁c₂}`. -/
private theorem TwistGrid_twLoopX_eq (X₁ X₂ : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n (fun x y => X₁ (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) y))
      (fun x y => X₂ (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) y)) a c₁ c₂ =
      Matrix.trace (X₁ * Eblk d (sz.L n) (sz.W n) a * X₂ * TwistGrid_Pb c₁ c₂) := by
  rw [TwistGrid_trace_Pb]
  simp only [TwistGrid_mul_Eblk_mul_apply]
  have hin : ∀ x : Idx d (sz.L n) (sz.W n), ∑ w ∈ twBlk n c₁, X₂ (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) w) *
      X₁ (split d (sz.L n) (sz.W n) (twShift n c₂ w)) (split d (sz.L n) (sz.W n) x) =
      ∑ q : Vtx d (sz.L n) (sz.W n), if q.1 = c₁ then X₂ (split d (sz.L n) (sz.W n) x) q * X₁ (c₂, q.2) (split d (sz.L n) (sz.W n) x) else 0 := by
    intro x
    have h := TwistGrid_sum_blk (d := d) (L := sz.L n) (W := sz.W n) c₁
      (fun q => X₂ (split d (sz.L n) (sz.W n) x) q * X₁ (c₂, q.2) (split d (sz.L n) (sz.W n) x))
    rw [← h]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [TwistGrid_split_shift]
  unfold twLoopX
  have hsum : ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, X₂ (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) w) *
      X₁ (split d (sz.L n) (sz.W n) (twShift n c₂ w)) (split d (sz.L n) (sz.W n) x) =
      ∑ q : Vtx d (sz.L n) (sz.W n), ∑ p : Vtx d (sz.L n) (sz.W n),
        if p.1 = a then (if q.1 = c₁ then X₂ p q * X₁ (c₂, q.2) p else 0) else 0 := by
    rw [Finset.sum_congr rfl (fun x _ => hin x)]
    have hout := TwistGrid_sum_blk (d := d) (L := sz.L n) (W := sz.W n) a
      (fun p => ∑ q : Vtx d (sz.L n) (sz.W n), if q.1 = c₁ then X₂ p q * X₁ (c₂, q.2) p else 0)
    refine Eq.trans hout ?_
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.1 = a <;> simp [hp]
  simp only [] at hsum ⊢
  rw [hsum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q.1 = c₁
  · simp only [hq, ite_true]
    rw [← mul_assoc, ← pow_two]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp [mul_comm]
  · simp [hq]

/-- Three nested block sums as sums over the block-product index (innermost variable outermost, as in the trace). -/
private theorem TwistGrid_sum_blk3 {L W : ℕ} [NeZero L] [NeZero W] (a₁ a₂ a₃ : Zd d L) (F : Vtx d L W → Vtx d L W → Vtx d L W → ℂ) :
    ∑ x ∈ Iblk d L W a₁, ∑ y ∈ Iblk d L W a₂, ∑ w ∈ Iblk d L W a₃, F (split d L W x) (split d L W y) (split d L W w) =
      ∑ r : Vtx d L W, ∑ q : Vtx d L W, ∑ p : Vtx d L W,
        if r.1 = a₃ then (if q.1 = a₂ then (if p.1 = a₁ then F p q r else 0) else 0) else 0 := by
  have h3 : ∀ x y, ∑ w ∈ Iblk d L W a₃, F (split d L W x) (split d L W y) (split d L W w) =
      ∑ r : Vtx d L W, if r.1 = a₃ then F (split d L W x) (split d L W y) r else 0 :=
    fun x y => TwistGrid_sum_blk a₃ (fun r => F (split d L W x) (split d L W y) r)
  have h2 : ∀ x, ∑ y ∈ Iblk d L W a₂, ∑ w ∈ Iblk d L W a₃, F (split d L W x) (split d L W y) (split d L W w) =
      ∑ q : Vtx d L W, if q.1 = a₂ then ∑ r : Vtx d L W, (if r.1 = a₃ then F (split d L W x) q r else 0) else 0 := by
    intro x
    simp only [h3]
    exact TwistGrid_sum_blk a₂ (fun q => ∑ r : Vtx d L W, if r.1 = a₃ then F (split d L W x) q r else 0)
  have h1 : ∑ x ∈ Iblk d L W a₁, ∑ y ∈ Iblk d L W a₂, ∑ w ∈ Iblk d L W a₃, F (split d L W x) (split d L W y) (split d L W w) =
      ∑ p : Vtx d L W, if p.1 = a₁ then ∑ q : Vtx d L W, (if q.1 = a₂ then ∑ r : Vtx d L W, (if r.1 = a₃ then F p q r else 0) else 0) else 0 := by
    simp only [h2]
    exact TwistGrid_sum_blk a₁ (fun p => ∑ q : Vtx d L W, if q.1 = a₂ then ∑ r : Vtx d L W, (if r.1 = a₃ then F p q r else 0) else 0)
  rw [h1]
  -- reorder: p, q, r  ↦  r, q, p
  have e1 : ∀ p : Vtx d L W, (if p.1 = a₁ then ∑ q : Vtx d L W, (if q.1 = a₂ then ∑ r : Vtx d L W, (if r.1 = a₃ then F p q r else 0) else 0) else 0) =
      ∑ q : Vtx d L W, ∑ r : Vtx d L W, if r.1 = a₃ then (if q.1 = a₂ then (if p.1 = a₁ then F p q r else 0) else 0) else 0 := by
    intro p
    by_cases hp : p.1 = a₁
    · simp only [hp, ite_true]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q.1 = a₂
      · simp [hq]
      · simp [hq]
    · simp [hp]
  simp only [e1]
  set G : Vtx d L W → Vtx d L W → Vtx d L W → ℂ := fun p q r =>
    if r.1 = a₃ then (if q.1 = a₂ then (if p.1 = a₁ then F p q r else 0) else 0) else 0 with hG
  change ∑ p : Vtx d L W, ∑ q : Vtx d L W, ∑ r : Vtx d L W, G p q r = ∑ r : Vtx d L W, ∑ q : Vtx d L W, ∑ p : Vtx d L W, G p q r
  calc ∑ p : Vtx d L W, ∑ q : Vtx d L W, ∑ r : Vtx d L W, G p q r
      = ∑ q : Vtx d L W, ∑ p : Vtx d L W, ∑ r : Vtx d L W, G p q r := Finset.sum_comm
    _ = ∑ q : Vtx d L W, ∑ r : Vtx d L W, ∑ p : Vtx d L W, G p q r :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ r : Vtx d L W, ∑ q : Vtx d L W, ∑ p : Vtx d L W, G p q r := Finset.sum_comm

/-- `twL3M`'s sum for block-product matrices is the trace of the word `X₀ E_{a₁} X₁ E_{a₂} X₂ P_{c₁c₂}`. -/
private theorem TwistGrid_twL3_eq (X₀ X₁ X₂ : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) :
    ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 * ∑ x ∈ twBlk n a₁, ∑ y ∈ twBlk n a₂, ∑ w ∈ twBlk n c₁,
      X₀ (split d (sz.L n) (sz.W n) (twShift n c₂ w)) (split d (sz.L n) (sz.W n) x) *
        X₁ (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) y) * X₂ (split d (sz.L n) (sz.W n) y) (split d (sz.L n) (sz.W n) w) =
      Matrix.trace (X₀ * Eblk d (sz.L n) (sz.W n) a₁ * X₁ * Eblk d (sz.L n) (sz.W n) a₂ * X₂ * TwistGrid_Pb c₁ c₂) := by
  rw [TwistGrid_trace_Pb]
  simp only [TwistGrid_mul_Eblk_mul_apply]
  have h := TwistGrid_sum_blk3 (d := d) (L := sz.L n) (W := sz.W n) a₁ a₂ c₁
    (fun p q r => X₀ (c₂, r.2) p * X₁ p q * X₂ q r)
  have h' : ∑ x ∈ twBlk n a₁, ∑ y ∈ twBlk n a₂, ∑ w ∈ twBlk n c₁,
      X₀ (split d (sz.L n) (sz.W n) (twShift n c₂ w)) (split d (sz.L n) (sz.W n) x) *
        X₁ (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) y) * X₂ (split d (sz.L n) (sz.W n) y) (split d (sz.L n) (sz.W n) w) =
      ∑ r : Vtx d (sz.L n) (sz.W n), ∑ q : Vtx d (sz.L n) (sz.W n), ∑ p : Vtx d (sz.L n) (sz.W n),
        if r.1 = c₁ then (if q.1 = a₂ then (if p.1 = a₁ then X₀ (c₂, r.2) p * X₁ p q * X₂ q r else 0) else 0) else 0 := by
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
    rw [TwistGrid_split_shift]
  rw [h']
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r.1 = c₁
  · simp only [hr, ite_true]
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.1 = a₂
    · simp only [hq, ite_true]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p.1 = a₁
      · simp only [hp, ite_true]; ring
      · simp [hp]
    · simp [hq]
  · simp [hr]

end Conv2

/-! ## 5. Derivatives of the twisted word `Tr(G₁ E G₂ P)` (the line Hessian and the spectral derivative) -/
section Word

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem TwistGrid_hasDerivAt_trace {f : ℝ → Matrix ι ι ℂ} {f' : Matrix ι ι ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix ι ι ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap ι ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

private theorem TwistGrid_hasDerivAt_Gsig {H : ℝ → Matrix ι ι ℂ} {zf : ℝ → ℂ}
    {H' : Matrix ι ι ℂ} {z' : ℂ} {t : ℝ}
    (hH : HasDerivAt H H' t) (hz : HasDerivAt zf z' t) (hherm : (H t).IsHermitian)
    (him : (zf t).im ≠ 0) (σ : Bool) :
    HasDerivAt (fun s => Gres (H s) (zf s) σ)
      (-(Gres (H t) (zf t) σ *
        (H' - (if σ then z' else (starRingEnd ℂ) z') • (1 : Matrix ι ι ℂ)) *
        Gres (H t) (zf t) σ)) t := by
  cases σ with
  | true => exact hasDerivAt_green_moving hH hz hherm him
  | false =>
      have hz' : HasDerivAt (fun s => (starRingEnd ℂ) (zf s)) ((starRingEnd ℂ) z') t := hz.star
      have him' : ((starRingEnd ℂ) (zf t)).im ≠ 0 := by simpa using him
      exact hasDerivAt_green_moving hH hz' hherm him'

private theorem TwistGrid_hasDerivAt_line (M A : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

private theorem TwistGrid_hasDerivAt_G {H C : Matrix ι ι ℂ} (hH : H.IsHermitian) (hC : C.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (y : ℝ) (σ : Bool) :
    HasDerivAt (fun s : ℝ => Gres (H + (s : ℂ) • C) z σ)
      (-(Gres (H + (y : ℂ) • C) z σ * C * Gres (H + (y : ℂ) • C) z σ)) y := by
  have := TwistGrid_hasDerivAt_Gsig (TwistGrid_hasDerivAt_line H C y) (hasDerivAt_const y z)
    (OneStep_isHermitian_add_realSmul hH hC y) hz σ
  simpa using this

/-- The second derivative of the twisted word `Tr(G₁ E G₂ P)` along a Hermitian line, at `0`. -/
private theorem TwistGrid_second (H C E P : Matrix ι ι ℂ) (hH : H.IsHermitian) (hC : C.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (σ₁ σ₂ : Bool) :
    deriv (deriv (fun y : ℝ => Matrix.trace (Gres (H + (y : ℂ) • C) z σ₁ * E * Gres (H + (y : ℂ) • C) z σ₂ * P))) 0 =
      2 * (Matrix.trace (Gres H z σ₁ * C * Gres H z σ₁ * C * Gres H z σ₁ * E * Gres H z σ₂ * P) +
        Matrix.trace (Gres H z σ₁ * C * Gres H z σ₁ * E * Gres H z σ₂ * C * Gres H z σ₂ * P) +
        Matrix.trace (Gres H z σ₁ * E * Gres H z σ₂ * C * Gres H z σ₂ * C * Gres H z σ₂ * P)) := by
  set G₁ : ℝ → Matrix ι ι ℂ := fun y => Gres (H + (y : ℂ) • C) z σ₁ with hG₁
  set G₂ : ℝ → Matrix ι ι ℂ := fun y => Gres (H + (y : ℂ) • C) z σ₂ with hG₂
  have hd₁ : ∀ y, HasDerivAt G₁ (-(G₁ y * C * G₁ y)) y := fun y => TwistGrid_hasDerivAt_G hH hC hz y σ₁
  have hd₂ : ∀ y, HasDerivAt G₂ (-(G₂ y * C * G₂ y)) y := fun y => TwistGrid_hasDerivAt_G hH hC hz y σ₂
  have hF : ∀ y, HasDerivAt (fun s => G₁ s * E * G₂ s * P)
      (-(G₁ y * C * G₁ y) * E * G₂ y * P + G₁ y * E * (-(G₂ y * C * G₂ y)) * P) y := by
    intro y
    have := (((hd₁ y).mul_const E).mul (hd₂ y)).mul_const P
    refine this.congr_deriv ?_
    simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hf1 : ∀ y, HasDerivAt (fun s => Matrix.trace (G₁ s * E * G₂ s * P))
      (Matrix.trace (-(G₁ y * C * G₁ y) * E * G₂ y * P + G₁ y * E * (-(G₂ y * C * G₂ y)) * P)) y :=
    fun y => TwistGrid_hasDerivAt_trace (hF y)
  have hderiv : deriv (fun s => Matrix.trace (G₁ s * E * G₂ s * P)) = fun y =>
      Matrix.trace (-(G₁ y * C * G₁ y) * E * G₂ y * P + G₁ y * E * (-(G₂ y * C * G₂ y)) * P) :=
    funext fun y => (hf1 y).deriv
  change deriv (deriv (fun s => Matrix.trace (G₁ s * E * G₂ s * P))) 0 = _
  rw [hderiv]
  have hq₁ : HasDerivAt (fun y => G₁ y * C * G₁ y) (-(G₁ 0 * C * G₁ 0) * C * G₁ 0 + G₁ 0 * C * (-(G₁ 0 * C * G₁ 0))) 0 :=
    (((hd₁ 0).mul_const C).mul (hd₁ 0)).congr_deriv (by simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc])
  have hq₂ : HasDerivAt (fun y => G₂ y * C * G₂ y) (-(G₂ 0 * C * G₂ 0) * C * G₂ 0 + G₂ 0 * C * (-(G₂ 0 * C * G₂ 0))) 0 :=
    (((hd₂ 0).mul_const C).mul (hd₂ 0)).congr_deriv (by simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc])
  have hF2 : HasDerivAt (fun y => -(G₁ y * C * G₁ y) * E * G₂ y * P + G₁ y * E * (-(G₂ y * C * G₂ y)) * P)
      ((-(-(G₁ 0 * C * G₁ 0) * C * G₁ 0 + G₁ 0 * C * (-(G₁ 0 * C * G₁ 0)))) * E * G₂ 0 * P + (-(G₁ 0 * C * G₁ 0)) * E * (-(G₂ 0 * C * G₂ 0)) * P +
        ((-(G₁ 0 * C * G₁ 0)) * E * (-(G₂ 0 * C * G₂ 0)) * P + G₁ 0 * E * (-(-(G₂ 0 * C * G₂ 0) * C * G₂ 0 + G₂ 0 * C * (-(G₂ 0 * C * G₂ 0)))) * P)) 0 := by
    have h1 := (((hq₁.neg.mul_const E).mul (hd₂ 0)).mul_const P)
    have h2 := (((hd₁ 0).mul_const E).mul (hq₂.neg)).mul_const P
    refine (h1.add h2).congr_deriv ?_
    simp only [Pi.neg_apply, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, neg_neg]
  rw [(TwistGrid_hasDerivAt_trace hF2).deriv]
  have hG10 : G₁ 0 = Gres H z σ₁ := by simp [hG₁]
  have hG20 : G₂ 0 = Gres H z σ₂ := by simp [hG₂]
  rw [hG10, hG20]
  simp only [Matrix.trace_add, Matrix.trace_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, neg_neg]
  ring

/-- The derivative of one signed resolvent along the spectral flow `z_v = E + (1-v) m` at a fixed Hermitian matrix. -/
private theorem TwistGrid_hasDerivAt_ztOf (m : ℂ) (E u : ℝ) : HasDerivAt (ztOf m E) (-m) u := by
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
  have h2 : HasDerivAt (fun v : ℝ => ((E : ℂ) + (1 - (v : ℂ)) * m)) (-m) u := by
    have h := (((hasDerivAt_const u (1 : ℂ)).sub h1).mul_const m).const_add (E : ℂ)
    simpa using h
  exact h2

private theorem TwistGrid_hasDerivAt_Gsig_spec {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu : u < 1) (σ : Bool) :
    HasDerivAt (fun v : ℝ => Gres H (ztOf m E v) σ)
      (-(Gres H (ztOf m E u) σ * (PropSpin m σ • (1 : Matrix ι ι ℂ)) * Gres H (ztOf m E u) σ)) u := by
  have him : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im, etaOf]
    exact ne_of_gt (mul_pos (by linarith) hm)
  have h := TwistGrid_hasDerivAt_Gsig (hasDerivAt_const u H) (TwistGrid_hasDerivAt_ztOf m E u) hH
    him σ
  refine h.congr_deriv ?_
  cases σ <;> simp [PropSpin]

end Word

/-! ## 6. The matrix-level core of T.8 (the twisted twin of `DriftAlgebra_loopGen_core`, `Path/DriftAlgebra.lean:429`) -/
section Core

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem TwistGrid_blockMat_add_smul (M C : Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℂ) :
    blockMat d L W (M + y • C) = blockMat d L W M + y • blockMat d L W C := by
  ext i j
  simp [blockMat]

/-- The spectral derivative of the twisted word at a Hermitian block matrix. -/
private theorem TwistGrid_deriv_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu : u < 1) (σ₀ σ₁ : Bool)
    (Ea P : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    deriv (fun v : ℝ => Matrix.trace (Gres H (ztOf m E v) σ₀ * Ea * Gres H (ztOf m E v) σ₁ * P)) u =
      -(PropSpin m σ₀ * Matrix.trace (Gres H (ztOf m E u) σ₀ * Gres H (ztOf m E u) σ₀ * Ea * Gres H (ztOf m E u) σ₁ * P)) -
        PropSpin m σ₁ * Matrix.trace (Gres H (ztOf m E u) σ₀ * Ea * Gres H (ztOf m E u) σ₁ * Gres H (ztOf m E u) σ₁ * P) := by
  have h0 := TwistGrid_hasDerivAt_Gsig_spec hH hm E hu σ₀
  have h1 := TwistGrid_hasDerivAt_Gsig_spec hH hm E hu σ₁
  have hF : HasDerivAt (fun v : ℝ => Gres H (ztOf m E v) σ₀ * Ea * Gres H (ztOf m E v) σ₁ * P)
      ((-(Gres H (ztOf m E u) σ₀ * (PropSpin m σ₀ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Gres H (ztOf m E u) σ₀) * Ea *
          Gres H (ztOf m E u) σ₁ + Gres H (ztOf m E u) σ₀ * Ea *
          (-(Gres H (ztOf m E u) σ₁ * (PropSpin m σ₁ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Gres H (ztOf m E u) σ₁))) * P) u :=
    ((h0.mul_const Ea).mul h1).mul_const P
  rw [(TwistGrid_hasDerivAt_trace hF).deriv]
  simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

/-- The coordinate contraction at block level (`Gauss.sum_allCoords_trace_blocks`; `Path/DriftAlgebra.lean:282`). -/
private theorem TwistGrid_cov (g : ℝ) (X Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        Matrix.trace (X * blockMat d L W (coordinateMatrix d L W c) * Y *
          blockMat d L W (coordinateMatrix d L W c)) =
      (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace (X * Eblk d L W p) * SB d L g p q * Matrix.trace (Y * Eblk d L W q) := by
  have key := sum_allCoords_trace_blocks d L W g (X.submatrix (split d L W) (split d L W))
    (Y.submatrix (split d L W) (split d L W))
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hX := blockRelabel_submatrix_split d L W X
  have hY := blockRelabel_submatrix_split d L W Y
  have hmul : ∀ P Q : Matrix (Idx d L W) (Idx d L W) ℂ,
      blockRelabel d L W (P * Q) = blockRelabel d L W P * blockRelabel d L W Q :=
    fun P Q => (Matrix.submatrix_mul_equiv P Q
      (splitEquiv d L W).symm (splitEquiv d L W).symm (splitEquiv d L W).symm).symm
  have htr : ∀ P : Matrix (Idx d L W) (Idx d L W) ℂ,
      Matrix.trace (blockRelabel d L W P) = Matrix.trace P := by
    intro P
    simp only [Matrix.trace, Matrix.diag, blockRelabel]
    exact Equiv.sum_comp (splitEquiv d L W).symm (fun i => P i i)
  have hC : blockMat d L W (coordinateMatrix d L W c) =
      blockRelabel d L W (coordinateMatrix d L W c) := rfl
  conv_lhs => rw [← hX, ← hY, hC, ← hmul, ← hmul, ← hmul, htr]

private theorem TwistGrid_sum_Eblk :
    ∑ a : Zd d L, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- Inserting `1 = W^d Σ_p E_p` in a trace. -/
private theorem TwistGrid_trace_insert (X Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (X * Y) = (W : ℂ) ^ d * ∑ p : Zd d L, Matrix.trace (X * Eblk d L W p * Y) := by
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  have h : ∑ p : Zd d L, Matrix.trace (X * Eblk d L W p * Y) =
      Matrix.trace (X * (∑ p : Zd d L, Eblk d L W p) * Y) := by
    rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  rw [h, TwistGrid_sum_Eblk, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.mul_one, smul_eq_mul, ← mul_assoc]
  field_simp

private theorem TwistGrid_sum_SB_zero (f g : Zd d L → ℂ) :
    ∑ p : Zd d L, ∑ q : Zd d L, f p * SB d L 0 p q * g q = ∑ p : Zd d L, f p * g p := by
  rw [EMn2BA_SB_zero]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Matrix.one_apply]

private theorem TwistGrid_sum_algebra (w m₀ m₁ : ℂ) (f₁ g₁ f₂ h₂ f₃ g₃ : Zd d L → ℂ) :
    w * ∑ p : Zd d L, f₁ p * g₁ p + w * ∑ p : Zd d L, f₂ p * h₂ p + w * ∑ p : Zd d L, f₃ p * g₃ p +
        (-(m₀ * (w * ∑ p : Zd d L, f₁ p)) - m₁ * (w * ∑ p : Zd d L, f₃ p)) =
      w * ∑ b : Zd d L, f₂ b * h₂ b + w * ∑ a' : Zd d L, ((g₁ a' - m₀) * f₁ a' + (g₃ a' - m₁) * f₃ a') := by
  have h : ∀ a' : Zd d L, (g₁ a' - m₀) * f₁ a' + (g₃ a' - m₁) * f₃ a' =
      (f₁ a' * g₁ a' + f₃ a' * g₃ a') - (m₀ * f₁ a' + m₁ * f₃ a') := fun a' => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **The matrix-level core of T.8**: the generator at `g = 0` of the twisted word, at the block-product index. -/
private theorem TwistGrid_gen_core {m : ℂ} (hm : 0 < m.im) (E u : ℝ) (hu1 : u < 1)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d L) :
    (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
        deriv (deriv (fun y : ℝ => Matrix.trace (Gres (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) (ztOf m E u) (σ 0) *
          Eblk d L W a * Gres (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) (ztOf m E u) (σ 1) * TwistGrid_Pb c₁ c₂))) 0 +
      deriv (fun v : ℝ => Matrix.trace (Gres (blockMat d L W M) (ztOf m E v) (σ 0) * Eblk d L W a *
        Gres (blockMat d L W M) (ztOf m E v) (σ 1) * TwistGrid_Pb c₁ c₂)) u =
    (W : ℂ) ^ d * ∑ b : Zd d L, Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (σ 0) * Eblk d L W b *
          Gres (blockMat d L W M) (ztOf m E u) (σ 1) * TwistGrid_Pb c₁ c₂) *
        Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (σ 0) * Eblk d L W a * Gres (blockMat d L W M) (ztOf m E u) (σ 1) * Eblk d L W b) +
      (W : ℂ) ^ d * ∑ a' : Zd d L,
        ((Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (σ 0) * Eblk d L W a') - PropSpin m (σ 0)) *
            Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (σ 0) * Eblk d L W a' * Gres (blockMat d L W M) (ztOf m E u) (σ 0) *
              Eblk d L W a * Gres (blockMat d L W M) (ztOf m E u) (σ 1) * TwistGrid_Pb c₁ c₂) +
          (Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (σ 1) * Eblk d L W a') - PropSpin m (σ 1)) *
            Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (σ 0) * Eblk d L W a * Gres (blockMat d L W M) (ztOf m E u) (σ 1) *
              Eblk d L W a' * Gres (blockMat d L W M) (ztOf m E u) (σ 1) * TwistGrid_Pb c₁ c₂)) := by
  have hz : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im, etaOf]
    exact ne_of_gt (mul_pos (by linarith) hm)
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  set H := blockMat d L W M with hHdef
  set z := ztOf m E u with hzdef
  set R₀ := Gres H z (σ 0) with hR₀
  set R₁ := Gres H z (σ 1) with hR₁
  set Ea := Eblk d L W a with hEa
  set Pb : Matrix (Vtx d L W) (Vtx d L W) ℂ := TwistGrid_Pb c₁ c₂ with hPb
  set Cb : CoordF d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun c => blockMat d L W (coordinateMatrix d L W c) with hCb
  have hspace : ∀ c : CoordF d L W, deriv (deriv (fun y : ℝ => Matrix.trace (Gres (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) z (σ 0) *
          Ea * Gres (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) z (σ 1) * Pb))) 0 =
      2 * (Matrix.trace ((R₀ * Ea * R₁ * Pb * R₀) * Cb c * R₀ * Cb c) +
        Matrix.trace ((R₁ * Pb * R₀) * Cb c * (R₀ * Ea * R₁) * Cb c) +
        Matrix.trace ((R₁ * Pb * R₀ * Ea * R₁) * Cb c * R₁ * Cb c)) := by
    intro c
    simp only [TwistGrid_blockMat_add_smul]
    rw [← hHdef, TwistGrid_second (H := H) (C := Cb c) (E := Ea) (P := Pb) hH
      ((coordinateMatrix_isHermitian d L W c).submatrix _) hz]
    have h1 := Matrix.trace_mul_comm (R₀ * Cb c * R₀ * Cb c) (R₀ * Ea * R₁ * Pb)
    have h2 := Matrix.trace_mul_comm (R₀ * Cb c * R₀ * Ea * R₁ * Cb c) (R₁ * Pb)
    have h3 := Matrix.trace_mul_comm (R₀ * Ea * R₁ * Cb c * R₁ * Cb c) (R₁ * Pb)
    simp only [Matrix.mul_assoc] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  have hspec : deriv (fun v : ℝ => Matrix.trace (Gres H (ztOf m E v) (σ 0) * Ea * Gres H (ztOf m E v) (σ 1) * Pb)) u =
      -(PropSpin m (σ 0) * Matrix.trace (R₀ * R₀ * Ea * R₁ * Pb)) - PropSpin m (σ 1) * Matrix.trace (R₀ * Ea * R₁ * R₁ * Pb) :=
    TwistGrid_deriv_spec (d := d) (L := L) (W := W) hH hm E hu1 (σ 0) (σ 1) Ea Pb
  have e1 : ∀ p : Zd d L, Matrix.trace ((R₀ * Ea * R₁ * Pb * R₀) * Eblk d L W p) =
      Matrix.trace (R₀ * Eblk d L W p * R₀ * Ea * R₁ * Pb) := by
    intro p
    have h := Matrix.trace_mul_comm (R₀ * Ea * R₁ * Pb) (R₀ * Eblk d L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e2 : ∀ p : Zd d L, Matrix.trace ((R₁ * Pb * R₀) * Eblk d L W p) =
      Matrix.trace (R₀ * Eblk d L W p * R₁ * Pb) := by
    intro p
    have h := Matrix.trace_mul_comm (R₁ * Pb) (R₀ * Eblk d L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e4 : ∀ p : Zd d L, Matrix.trace ((R₁ * Pb * R₀ * Ea * R₁) * Eblk d L W p) =
      Matrix.trace (R₀ * Ea * R₁ * Eblk d L W p * R₁ * Pb) := by
    intro p
    have h := Matrix.trace_mul_comm (R₁ * Pb) (R₀ * Ea * R₁ * Eblk d L W p)
    simp only [Matrix.mul_assoc] at h ⊢
    exact h
  have e5 : Matrix.trace (R₀ * R₀ * Ea * R₁ * Pb) =
      (W : ℂ) ^ d * ∑ p : Zd d L, Matrix.trace (R₀ * Eblk d L W p * R₀ * Ea * R₁ * Pb) := by
    rw [show R₀ * R₀ * Ea * R₁ * Pb = R₀ * (R₀ * Ea * R₁ * Pb) by simp only [Matrix.mul_assoc],
      TwistGrid_trace_insert]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    simp only [Matrix.mul_assoc]
  have e6 : Matrix.trace (R₀ * Ea * R₁ * R₁ * Pb) =
      (W : ℂ) ^ d * ∑ p : Zd d L, Matrix.trace (R₀ * Ea * R₁ * Eblk d L W p * R₁ * Pb) := by
    rw [show R₀ * Ea * R₁ * R₁ * Pb = (R₀ * Ea * R₁) * (R₁ * Pb) by simp only [Matrix.mul_assoc],
      TwistGrid_trace_insert]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    simp only [Matrix.mul_assoc]
  have hsplit : (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
        (2 * (Matrix.trace ((R₀ * Ea * R₁ * Pb * R₀) * Cb c * R₀ * Cb c) +
          Matrix.trace ((R₁ * Pb * R₀) * Cb c * (R₀ * Ea * R₁) * Cb c) +
          Matrix.trace ((R₁ * Pb * R₀ * Ea * R₁) * Cb c * R₁ * Cb c))) =
        ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
            Matrix.trace ((R₀ * Ea * R₁ * Pb * R₀) * Cb c * R₀ * Cb c) +
          ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
            Matrix.trace ((R₁ * Pb * R₀) * Cb c * (R₀ * Ea * R₁) * Cb c) +
          ∑ c : CoordF d L W, ((gvarF d L W 0 c : ℝ) : ℂ) *
            Matrix.trace ((R₁ * Pb * R₀ * Ea * R₁) * Cb c * R₁ * Cb c) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [Finset.sum_congr rfl fun c _ => by rw [hspace c], hspec, hsplit]
  simp only [hCb]
  rw [TwistGrid_cov 0, TwistGrid_cov 0, TwistGrid_cov 0]
  rw [TwistGrid_sum_SB_zero, TwistGrid_sum_SB_zero, TwistGrid_sum_SB_zero]
  simp only [e1, e2, e4, e5, e6]
  exact TwistGrid_sum_algebra ((W : ℂ) ^ d) (PropSpin m (σ 0)) (PropSpin m (σ 1))
    (fun p => Matrix.trace (R₀ * Eblk d L W p * R₀ * Ea * R₁ * Pb)) (fun p => Matrix.trace (R₀ * Eblk d L W p))
    (fun p => Matrix.trace (R₀ * Eblk d L W p * R₁ * Pb)) (fun p => Matrix.trace (R₀ * Ea * R₁ * Eblk d L W p))
    (fun p => Matrix.trace (R₀ * Ea * R₁ * Eblk d L W p * R₁ * Pb)) (fun p => Matrix.trace (R₁ * Eblk d L W p))

end Core

section Glue

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

private theorem TwistGrid_twL2M_trace (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    twL2M sz lam0 E n u H σ a c₁ c₂ =
      Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * Eblk d (sz.L n) (sz.W n) a *
        Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) * TwistGrid_Pb c₁ c₂) := by
  rw [← TwistGrid_twLoopX_eq]
  unfold twL2M
  have h0 : twChg (twGM sz lam0 E n u H) (σ 0) = fun x y => Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0)
      (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) y) :=
    funext fun x => funext fun y => (TwistGrid_Gres_blockMat_apply hH _ _ x y).symm
  have h1 : twChg (twGM sz lam0 E n u H) (σ 1) = fun x y => Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)
      (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) y) :=
    funext fun x => funext fun y => (TwistGrid_Gres_blockMat_apply hH _ _ x y).symm
  rw [h0, h1]

private theorem TwistGrid_twL3M_trace (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 3 → Bool) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) :
    twL3M sz lam0 E n u H σ a₁ a₂ c₁ c₂ =
      Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * Eblk d (sz.L n) (sz.W n) a₁ *
        Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) * Eblk d (sz.L n) (sz.W n) a₂ *
        Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 2) * TwistGrid_Pb c₁ c₂) := by
  rw [← TwistGrid_twL3_eq]
  unfold twL3M
  have h : ∀ i : Fin 3, ∀ x y, twChg (twGM sz lam0 E n u H) (σ i) x y = Gres (blockMat d (sz.L n) (sz.W n) H)
      (ztOf (BAmF sz lam0 E n) (E n) u) (σ i) (split d (sz.L n) (sz.W n) x) (split d (sz.L n) (sz.W n) y) :=
    fun i x y => (TwistGrid_Gres_blockMat_apply hH _ _ x y).symm
  simp only [h]

private theorem TwistGrid_LM_one (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (τ : Bool) (a' : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H ![τ] ![a'] =
      Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) τ * Eblk d (sz.L n) (sz.W n) a') := by
  simp [baStep2Mat, loopFine, loopM]

private theorem TwistGrid_LM_two (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H σ ![a, b] =
      Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * Eblk d (sz.L n) (sz.W n) a *
        Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) * Eblk d (sz.L n) (sz.W n) b) := by
  simp [baStep2Mat, loopFine, loopM, List.ofFn_succ, Matrix.mul_assoc]

end Glue

/-! ## 7. Target 2, T.8 (D.1) -/

/-- **Target 2, T.8 (D.1)** (twin of `loopGenNOf`, `Induction/LoopGenN.lean:567`): the generator of the coupling-0 walk applied to `L̃` is `W^d Σ_b L̃(b) 𝓛^{(2)}_{σ,(a,b)} + Ẽ^{G̊}`. -/
def BATwistGen (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im → ∀ u : ℝ, u < 1 →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
      twGenM sz lam0 E n u H σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b, twL2M sz lam0 E n u H σ b c₁ c₂ * (baStep2Mat sz lam0 E).LM n u H σ ![a, b] +
        twEGM sz lam0 E n u H σ a c₁ c₂

theorem BATwistGen_holds (d : ℕ) : BATwistGen d := by
  intro sz lam0 E n hm u hu1 H hH σ a c₁ c₂
  have hcore := TwistGrid_gen_core (d := d) (L := sz.L n) (W := sz.W n) (m := BAmF sz lam0 E n) hm (E n) u hu1 hH σ a c₁ c₂
  refine Eq.trans (?_ : twGenM sz lam0 E n u H σ a c₁ c₂ = _) (hcore.trans ?_)
  · unfold twGenM
    have hF : ∀ c : CoordF d (sz.L n) (sz.W n), (fun y : ℝ => twL2M sz lam0 E n u (H + (y : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c) σ a c₁ c₂) =
        fun y : ℝ => Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) (H + (y : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c))
            (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * Eblk d (sz.L n) (sz.W n) a *
          Gres (blockMat d (sz.L n) (sz.W n) (H + (y : ℂ) • coordinateMatrix d (sz.L n) (sz.W n) c)) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) *
            TwistGrid_Pb c₁ c₂) := fun c => funext fun y =>
      TwistGrid_twL2M_trace sz lam0 E n u (OneStep_isHermitian_add_realSmul hH (coordinateMatrix_isHermitian d (sz.L n) (sz.W n) c) y) σ a c₁ c₂
    have hG : (fun v : ℝ => twL2M sz lam0 E n v H σ a c₁ c₂) = fun v : ℝ => Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) H)
        (ztOf (BAmF sz lam0 E n) (E n) v) (σ 0) * Eblk d (sz.L n) (sz.W n) a *
          Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) v) (σ 1) * TwistGrid_Pb c₁ c₂) :=
      funext fun v => TwistGrid_twL2M_trace sz lam0 E n v hH σ a c₁ c₂
    simp only [hF, hG]
  · unfold twEGM
    simp only [TwistGrid_twL2M_trace sz lam0 E n u hH, TwistGrid_LM_two, TwistGrid_LM_one, TwistGrid_twL3M_trace sz lam0 E n u hH, PropSpin]
    simp
/-! ## 8. Target 3, T.9 (D.4) -/

section Hier

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- At the BA carrier `twMB` is `M^{(B)}` (the generic-`(g₀, E)` form of `twMB_ba`, `BA/TwistPins.lean:96`). -/
private theorem TwistGrid_twMB_ba (hm : 0 < (BAmF sz lam0 E n).im) :
    twMB (baFM sz lam0 E) n = BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) := by
  ext a b
  have ha : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (a, 0)) = (a, 0) := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
  have hb : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (b, 0)) = (b, 0) := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
  simp only [twMB, Matrix.of_apply, baFM]
  rw [BAMfine_eq sz _ _ n hm]
  change (if (split d (sz.L n) (sz.W n) _).2 = (split d (sz.L n) (sz.W n) _).2 then _ else _) = _
  rw [ha, hb]
  exact ite_eq_left_of_eq_true _ _ (eq_true rfl)

private theorem TwistGrid_twK_eq (hm : 0 < (BAmF sz lam0 E n).im) (t : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    twK (baFM sz lam0 E) n t σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n),
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) t (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁ := by
  unfold twK; rw [TwistGrid_twMB_ba sz lam0 E n hm]; rfl

private theorem TwistGrid_hasDerivAt_twK {κ : ℝ} (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ => twK (baFM sz lam0 E) n v σ a c₁ c₂)
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n),
        (BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) *
          BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1)) a a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁) u := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hfun : (fun v : ℝ => twK (baFM sz lam0 E) n v σ a c₁ c₂) = fun v : ℝ => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n),
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) v (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁ :=
    funext fun v => TwistGrid_twK_eq sz lam0 E n hm v σ a c₁ c₂
  rw [hfun]
  refine HasDerivAt.const_mul _ ?_
  refine HasDerivAt.fun_sum fun a' _ => ?_
  exact ((BATheta_hasDerivAt d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) hr hu0 hu1 (σ 0) (σ 1) a a').mul_const _).mul_const _

end Hier

/-- **Target 3, T.9 (D.4)** (twin of `loopDrift_sub_K_deriv_n`, `Induction/HierAlgebra.lean:729`, with `hierarchyN_of_loopGenN`, `Induction/HierarchyN.lean:69`):
`generator(L̃) - ∂_u K̃ = Θ̃_u∘Z + B̃₁ + B̃₂ + Ẽ^{G̊}`. -/
def BATwistHier (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ → 0 < lam0 n → BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
    ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
        twGenM sz lam0 E n u H σ a c₁ c₂ - deriv (fun v : ℝ => twK (baFM sz lam0 E) n v σ a c₁ c₂) u = twDriftM sz lam0 E n u H σ a c₁ c₂

theorem BATwistHier_holds (d : ℕ) : BATwistHier d := by
  intro sz lam0 E n κ hκ hg hr u hu0 hu1 H hH σ a c₁ c₂
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne (sz.W n)))
  rw [BATwistGen_holds d sz lam0 E n hm u hu1 H hH σ a c₁ c₂,
    (TwistGrid_hasDerivAt_twK sz lam0 E n hκ hr hu0 hu1 σ a c₁ c₂).deriv]
  set T : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
    BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) with hT
  have hK2 : ∀ b : Zd d (sz.L n), (baStep2Mat sz lam0 E).K n u σ ![a, b] = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * T a b := by
    intro b
    have h := baKsol_two d hκ hg hL (sz.W n) hr ⟨hu0, hu1⟩ σ ![a, b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact h
  have hd : (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n),
        (BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) *
          BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1)) a a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) c₂ a' *
        BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 1) a' c₁ =
      ∑ b : Zd d (sz.L n), T a b * twK (baFM sz lam0 E) n u σ b c₁ c₂ := by
    simp only [TwistGrid_twK_eq sz lam0 E n hm, hT, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [hd]
  have key : ∀ b : Zd d (sz.L n), ((sz.W n : ℕ) : ℂ) ^ d * (twL2M sz lam0 E n u H σ b c₁ c₂ * (baStep2Mat sz lam0 E).LM n u H σ ![a, b]) -
      T a b * twK (baFM sz lam0 E) n u σ b c₁ c₂ =
      T a b * (twL2M sz lam0 E n u H σ b c₁ c₂ - twK (baFM sz lam0 E) n u σ b c₁ c₂) +
      ((sz.W n : ℕ) : ℂ) ^ d * (twK (baFM sz lam0 E) n u σ b c₁ c₂ * ((baStep2Mat sz lam0 E).LM n u H σ ![a, b] - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * T a b)) +
      ((sz.W n : ℕ) : ℂ) ^ d * ((twL2M sz lam0 E n u H σ b c₁ c₂ - twK (baFM sz lam0 E) n u σ b c₁ c₂) *
        ((baStep2Mat sz lam0 E).LM n u H σ ![a, b] - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * T a b)) := by
    intro b
    field_simp
    ring
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (Zd d (sz.L n))) = Finset.univ) (fun b _ => key b)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  unfold twDriftM twB1M twB2M
  simp only [hK2, Matrix.mulVec, dotProduct]
  linear_combination hsum

/-! ## 9. Compiled nonempty instances (`d = 3`, `sz0`: `L = 4`, `W = 32`, `lam = 1/64`, `n = 0`, flow `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`;
`σ = (false, true)`, `c₁ = 0`, `c₂ = (1,0,0)`).  Every deterministic hypothesis is discharged: `0 < Im m` (`BAmF_sz0_im_pos`), `u = 1/2 < 1`, `H` the Hermitian
flow matrix `seqHflowBA` of an arbitrary sample, `BAReal` (`BAflow_real`), `0 < g₀` (`gI_pos`). -/

-- Target 1: the other six bridges at the instance (`u = 1/2`, `H = seqHflowBA`, all `rfl`).
end RBM.BA
