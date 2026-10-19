/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QGridA
import RBM3D.Induction.QProxy
import RBM3D.Chain.NQGood2Gen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Induction.NQGood2
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopNorm
import RBM3D.Evolution.SumDecayZero

/-!
# The drift and the initial term of the `𝒬`-process, `d ≥ 3`

Paper: (4.35) `int_K-L+Q`, Claim 4.9 (`lem_+Q`), Lemma 4.16 (`lem:sum_decay`) with (4.56) `sum_res_2`,
and (4.58) `eq:alternatecase1`.
As RBM2D's `dFlowQ`, `AltDriftQ_Qop_add`, `dGridQN_eq_dFlowQ`,
`altQ_hker`, `AltDriftQ_meas_*`, for `d ≥ 3`: the `ℚ/𝔼` split of RBM2D collapses, because
`ekSumDecay2_holds` ((4.56) `sum_res_2`) needs only `EKSumZero` and `EKFastDecay`, for every `σ`, and
the drift `𝒬_u(ℬ₁+ℬ₂+ℬ₃) + ℬ₄ + ℬ₅` is sum-zero pathwise.  All statements are deterministic,
level-free, per matrix or per grid time.

## What is here (namespace `RBM.Ind`)

* §1 the vocabulary: `altB4N`, `altB5N`, `dFlowQN`, `altClsQN`, `kappaAltQN`, `epsAltQN`.
* §2 `dGridQN_eq_dFlowQN`, `dFlowQN_sumZero`.
* §3 `Qop_fastDecay`, `fastDecay_of_diamInf`: the `𝒬`-process is sum-zero, and decay survives `𝒬_t`.
* §4 `hker_altQN`, `alt_hkerQN`: `ekSumDecay2_holds` in the field shape of `GridAssemblyHypN.hker`.
* §5 `goodSetN_A0clsQN`, `alt_hA0clsQN`: the initial-term class, radius `ε'` (not `τ'`).

The generic twins over a carrier `Cm : Step2Mat sz` (namespace `RBM.Ind`, `open RBM.BA`): `altB4Ng`,
`altB5Ng`, `dFlowQNg`, `kappaAltQNg`, `epsAltQNg` (explicit constant `Cv`; §1g), `dGridQNg_eq_dFlowQNg`,
`dFlowQNg_sumZero` (§2g), `fastDecay_of_diamInfg`, `hker_altQNg`, `alt_hkerQNg` (§4g: `QProxyG_KerEK4` at
the kernel coupling `gK`, the comparison to the size level `sz.lam`, two constants `C4 ≤ Cv`),
`goodSetNg_A0clsQNg`, `alt_hA0clsQNg` (§5g).

Every helper that is not part of the statements is `private` or prefixed `QDriftA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.BA

/-! ## 1. The vocabulary -/

/-- `ℬ₄ = [𝒬_u, Θ^{(m+1)}_{u,σ}](𝓛-𝒦)_{u,σ}(H)` at a fine matrix `H` ((4.35) `int_K-L+Q`; the
second summand of `dGridQN`, at a matrix; RBM2D `B4` inside `altB`). -/
def altB4N {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ u
        (ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u (fun b => sz.STLKM n E u H σ b)) a -
      ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
        (STQop (d := d) ϑ u (fun b => sz.STLKM n E u H σ b)) a

/-- `ℬ₅ = -[𝒫∘(𝓛-𝒦)_{u,σ}(H)]_{a₁} ∂_uϑ_{u,a}` with the paper's sign inside ((4.35) `int_K-L+Q`; the last term of
`dGridQN`). -/
def altB5N {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => -(STPsum (d := d) (fun b => sz.STLKM n E u H σ b) (a 0) * deriv (fun τ => ϑ τ a) u)

/-- **The drift of `int_K-L+Q` at a matrix**: `𝒬_u(ℬ₁ + ℬ₂ + ℬ₃) + ℬ₄ + ℬ₅` (RBM2D `dFlowQ`; the first summand is the text of `dGridQN` with `H` for `pathH … j ω`). -/
def dFlowQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ u
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n E u H l (loopOf σ b) +
            sz.STelklkM n E u H (loopOf σ b) +
            sz.STegtM n E u H (loopOf σ b)) a +
      altB4N sz n E u ϑ σ H a + altB5N sz n E u ϑ σ H a

/-- **The kernel class of the alternating chain** (the `d ≥ 3` form of RBM2D's `AltCase4Cls`; pattern `nonAltClsN`): `Cls i δ X :⇔` `X` is sum-zero (`EKSumZero`),
`δ ≤ W^{-Dc}`, and `‖X b‖ ≤ δ` when `ℓ_{u_i} W^{τ'} ≤ diam_∞ b`.  No symmetry clause, no alternation. -/
def altClsQN (d L : ℕ) [NeZero L] {k : ℕ} (g W τ' Dc : ℝ) (u : ℕ → ℝ) :
    ℕ → ℝ → ((Fin k → Zd d L) → ℂ) → Prop :=
  fun i δ X => EKSumZero X ∧ δ ≤ W ^ (-Dc) ∧
    ∀ b : Fin k → Zd d L, ellT L g (u i) * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ

/-- **The kernel weight `κ_{i,m}` of the alternating chain**: `W^{C₄ε}((g²+|1-u_i|)/(g²+|1-u_m|))^k`,
`C₄ = qProxy4C d k Λg κ' K` (exponent `k`, not `k-1`: `(sum_res_2)`). -/
def kappaAltQN (d k : ℕ) (Λg κ' K g W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
  W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - u i|) / (g ^ 2 + |1 - u m|)) ^ k

/-- **The additive decay-error weight `ε_{i,m}` of the alternating chain**: `W^{C₄}`. -/
def epsAltQN (d k : ℕ) (Λg κ' K W : ℝ) (_i _m : ℕ) : ℝ :=
  W ^ qProxy4C d k Λg κ' K

/-! ## 1g. The vocabulary over a carrier -/

section VocabG

variable {d : ℕ} {sz : Sizes d}

/-- `ℬ₄` over a carrier (band `altB4N`). -/
def altB4Ng (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ u (Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKMg Cm n u H σ b)) a -
      Step2Gen_ThetaN Cm.toFlowFM n σ u (STQop (d := d) ϑ u (fun b => STLKMg Cm n u H σ b)) a

/-- `ℬ₅` over a carrier (band `altB5N`). -/
def altB5Ng (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => -(STPsum (d := d) (fun b => STLKMg Cm n u H σ b) (a 0) * deriv (fun τ => ϑ τ a) u)

/-- The drift of `int_K-L+Q` at a matrix over a carrier (band `dFlowQN`). -/
def dFlowQNg (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ u
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), STksimLKMg Cm n u H l (KLloopOf d (sz.L n) σ b) +
            STelklkMg Cm n u H (KLloopOf d (sz.L n) σ b) +
            STegtMg Cm n u H (KLloopOf d (sz.L n) σ b)) a +
      altB4Ng Cm n u ϑ σ H a + altB5Ng Cm n u ϑ σ H a

/-- The kernel weight of the alternating chain with the explicit constant `Cv` (band `kappaAltQN`, `Cv = qProxy4C d k Λg κ' K`). -/
def kappaAltQNg (k : ℕ) (Cv g W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
  W ^ (Cv * ε) * ((g ^ 2 + |1 - u i|) / (g ^ 2 + |1 - u m|)) ^ k

/-- The additive decay-error weight with the explicit constant `Cv` (band `epsAltQN`). -/
def epsAltQNg (Cv W : ℝ) (_i _m : ℕ) : ℝ :=
  W ^ Cv

end VocabG

/-! ## 2. The drift along the walk and its sum-zero structure -/

section Drift

private theorem QDriftA_Psum_add {d L m : ℕ} [NeZero L] (A B : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    STPsum (d := d) (fun a => A a + B a) a₁ = STPsum (d := d) A a₁ + STPsum (d := d) B a₁ := by
  unfold STPsum
  exact Finset.sum_add_distrib

private theorem QDriftA_Psum_sub {d L m : ℕ} [NeZero L] (A B : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    STPsum (d := d) (fun a => A a - B a) a₁ = STPsum (d := d) A a₁ - STPsum (d := d) B a₁ := by
  unfold STPsum
  rw [Finset.sum_sub_distrib]

private theorem QDriftA_ekSumZero_of_Psum {d L m : ℕ} [NeZero L] {A : (Fin (m + 1) → Zd d L) → ℂ}
    (h : ∀ a₁, STPsum (d := d) A a₁ = 0) : EKSumZero A := by
  intro i₀ hi x
  have hi0 : i₀ = 0 := Fin.ext (by simpa using hi)
  subst hi0
  exact h x

/-- **`dGridQN` along the walk** is `dFlowQN` at the grid state
(RBM2D `dGridQN_eq_dFlowQ`): `dGridQN` already has `ℬ₄`, `ℬ₅` inside, so
this is an unfolding of `dGridQN` and `AvecN`. -/
theorem dGridQN_eq_dFlowQN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    dGridQN sz E s t K n ϑ σ j ω =
      dFlowQN sz n (E n) (gridTime s t K n j) ϑ σ (pathH sz s t K n j ω) := by
  funext a
  unfold dGridQN dFlowQN altB4N altB5N
  exact sub_eq_add_neg _ _

/-- **The drift is sum-zero**: `𝒫ℬ₄ = 𝒫ℬ₅ = 0`, hence `𝒬_uℬ₄ = ℬ₄`, `𝒬_uℬ₅ = ℬ₅`, and the
drift is sum-zero in the form of `ekSumDecay2_holds`, for every `σ`.  `𝒫ℬ₄ = 𝒫𝒬(Θ𝒜) - 𝒫Θ(𝒬𝒜) = 0` by
`QopAlgebra_Psum_Qop` and `QopAlgebra_ThetaN_sumZero`; `𝒫ℬ₅ = -(𝒫𝒜)_{a₁} 𝒫(∂ϑ) = 0` by
`QopAlgebra_Psum_deriv`. -/
theorem dFlowQN_sumZero {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    |E| ≤ 2 → 0 ≤ u → u < 1 →
    (∀ (τ : ℝ) (a₁ : Zd d (sz.L n)),
      ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁), ϑ τ a = 1) →
    (∀ a : Fin (m + 1) → Zd d (sz.L n), DifferentiableAt ℝ (fun τ => ϑ τ a) u) →
    (∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB4N sz n E u ϑ σ H) a₁ = 0) ∧
    (∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB5N sz n E u ϑ σ H) a₁ = 0) ∧
    STQop (d := d) ϑ u (altB4N sz n E u ϑ σ H) = altB4N sz n E u ϑ σ H ∧
    STQop (d := d) ϑ u (altB5N sz n E u ϑ σ H) = altB5N sz n E u ϑ σ H ∧
    EKSumZero (dFlowQN sz n E u ϑ σ H) := by
  intro hE hu0 hu1 hsum hdiff
  have hB4 : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB4N sz n E u ϑ σ H) a₁ = 0 := by
    intro a₁
    unfold altB4N
    rw [QDriftA_Psum_sub]
    have h1 := QopAlgebra_Psum_Qop (d := d) ϑ (hsum u)
      (ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u (fun b => sz.STLKM n E u H σ b)) a₁
    have h2 := QopAlgebra_ThetaN_sumZero (d := d) (sz.lam n) (sz.three_le_L n)
      (μs := fun i => mSigma E (σ i)) (fun i => norm_mSigma hE (σ i)) hu0 hu1
      (A := STQop (d := d) ϑ u (fun b => sz.STLKM n E u H σ b))
      (QopAlgebra_Psum_Qop (d := d) ϑ (hsum u) (fun b => sz.STLKM n E u H σ b)) a₁
    rw [h1, h2, sub_zero]
  have hB5 : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB5N sz n E u ϑ σ H) a₁ = 0 := by
    intro a₁
    have hd' : ∀ a, HasDerivAt (fun τ => ϑ τ a) (deriv (fun τ => ϑ τ a) u) u :=
      fun a => (hdiff a).hasDerivAt
    have hP := QopAlgebra_Psum_deriv (d := d) hsum hd' a₁
    unfold STPsum at hP ⊢
    unfold altB5N
    have : ∀ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁),
        -(STPsum (d := d) (fun b => sz.STLKM n E u H σ b) (a 0) * deriv (fun τ => ϑ τ a) u) =
          -(STPsum (d := d) (fun b => sz.STLKM n E u H σ b) a₁) * deriv (fun τ => ϑ τ a) u := by
      intro a ha
      rw [(Finset.mem_filter.1 ha).2]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hP, mul_zero]
  have hQ : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (STQop (d := d) ϑ u
      (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n E u H l (loopOf σ b) +
            sz.STelklkM n E u H (loopOf σ b) + sz.STegtM n E u H (loopOf σ b))) a₁ = 0 :=
    fun a₁ => QopAlgebra_Psum_Qop (d := d) ϑ (hsum u) _ a₁
  refine ⟨hB4, hB5, QopAlgebra_Qop_of_sumZero ϑ u hB4, QopAlgebra_Qop_of_sumZero ϑ u hB5, ?_⟩
  refine QDriftA_ekSumZero_of_Psum fun a₁ => ?_
  unfold dFlowQN
  rw [QDriftA_Psum_add, QDriftA_Psum_add, hQ a₁, hB4 a₁, hB5 a₁]
  ring

end Drift

/-! ## 2g. The drift along the walk and its sum-zero structure -/

section DriftG

variable {d : ℕ} {sz : Sizes d}

theorem dGridQNg_eq_dFlowQNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    dGridQNg Cm s t K n ϑ σ j ω = dFlowQNg Cm n (gridTime s t K n j) ϑ σ (Cm.Hpath s t K n j ω) := by
  funext a
  unfold dGridQNg dFlowQNg altB4Ng altB5Ng AvecNg
  exact sub_eq_add_neg _ _

theorem dFlowQNg_sumZero (Cm : Step2Mat sz) (n : ℕ) (hKS : ZeroModeGen_KerSums Cm.toFlowFM n) (u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (∀ (τ : ℝ) (a₁ : Zd d (sz.L n)),
      ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁), ϑ τ a = 1) →
    (∀ a : Fin (m + 1) → Zd d (sz.L n), DifferentiableAt ℝ (fun τ => ϑ τ a) u) →
    (∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB4Ng Cm n u ϑ σ H) a₁ = 0) ∧
    (∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB5Ng Cm n u ϑ σ H) a₁ = 0) ∧
    STQop (d := d) ϑ u (altB4Ng Cm n u ϑ σ H) = altB4Ng Cm n u ϑ σ H ∧
    STQop (d := d) ϑ u (altB5Ng Cm n u ϑ σ H) = altB5Ng Cm n u ϑ σ H ∧
    EKSumZero (dFlowQNg Cm n u ϑ σ H) := by
  intro hsum hdiff
  have hB4 : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB4Ng Cm n u ϑ σ H) a₁ = 0 := by
    intro a₁
    unfold altB4Ng
    rw [QDriftA_Psum_sub]
    have h1 := QopAlgebra_Psum_Qop (d := d) ϑ (hsum u)
      (Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKMg Cm n u H σ b)) a₁
    have h2 := QopAlgebra_ThetaN_sumZerog Cm.toFlowFM n hKS σ u
      (STQop (d := d) ϑ u (fun b => STLKMg Cm n u H σ b))
      (QopAlgebra_Psum_Qop (d := d) ϑ (hsum u) (fun b => STLKMg Cm n u H σ b)) a₁
    rw [h1, h2, sub_zero]
  have hB5 : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (altB5Ng Cm n u ϑ σ H) a₁ = 0 := by
    intro a₁
    have hd' : ∀ a, HasDerivAt (fun τ => ϑ τ a) (deriv (fun τ => ϑ τ a) u) u :=
      fun a => (hdiff a).hasDerivAt
    have hP := QopAlgebra_Psum_deriv (d := d) hsum hd' a₁
    unfold STPsum at hP ⊢
    unfold altB5Ng
    have : ∀ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁),
        -(STPsum (d := d) (fun b => STLKMg Cm n u H σ b) (a 0) * deriv (fun τ => ϑ τ a) u) =
          -(STPsum (d := d) (fun b => STLKMg Cm n u H σ b) a₁) * deriv (fun τ => ϑ τ a) u := by
      intro a ha
      rw [(Finset.mem_filter.1 ha).2]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hP, mul_zero]
  have hQ : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (STQop (d := d) ϑ u
      (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), STksimLKMg Cm n u H l (KLloopOf d (sz.L n) σ b) +
            STelklkMg Cm n u H (KLloopOf d (sz.L n) σ b) + STegtMg Cm n u H (KLloopOf d (sz.L n) σ b))) a₁ = 0 :=
    fun a₁ => QopAlgebra_Psum_Qop (d := d) ϑ (hsum u) _ a₁
  refine ⟨hB4, hB5, QopAlgebra_Qop_of_sumZero ϑ u hB4, QopAlgebra_Qop_of_sumZero ϑ u hB5, ?_⟩
  refine QDriftA_ekSumZero_of_Psum fun a₁ => ?_
  unfold dFlowQNg
  rw [QDriftA_Psum_add, QDriftA_Psum_add, hQ a₁, hB4 a₁, hB5 a₁]
  ring

end DriftG


/-! ## 3. The `𝒬`-process is sum-zero, and decay survives `𝒬_t` -/

section QDecay

/-- **Decay survives `𝒬_t`**.  `𝒬A = A - (A - 𝒬A)`, with
`stQop_sub_fastDecay` for `A - 𝒬A`. -/
theorem Qop_fastDecay :
    ∀ (d m : ℕ) (K C c C₀ ε' D' : ℝ), 0 < C → 0 < c → 0 < ε' →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D' A →
        ∀ a : Fin (m + 1) → Zd d L, (∃ i j, W ^ ε' * ellT L g t ≤ (zdistD d L (a i - a j) : ℝ)) →
          ‖STQop (d := d) ϑ t A a‖ ≤ 2 * W ^ (-D') := by
  intro d m K C c C₀ ε' D' hC hc hε'
  obtain ⟨W₀, hW₀, H⟩ := stQop_sub_fastDecay d m K C c C₀ ε' D' hC hc hε'
  refine ⟨W₀, hW₀, fun L _ hL g hg W hW hLK ϑ hϑ t ht0 ht1 A hA hfast a ha => ?_⟩
  have h1 : ‖A a‖ ≤ W ^ (-D') := hfast a ha
  have h2 : ‖(A - STQop (d := d) ϑ t A) a‖ ≤ W ^ (-D') :=
    H L hL g hg W hW hLK ϑ hϑ t ht0 ht1 A hA a ha
  have e : STQop (d := d) ϑ t A a = A a - (A - STQop (d := d) ϑ t A) a := by
    simp
  rw [e]
  calc ‖A a - (A - STQop (d := d) ϑ t A) a‖ ≤ ‖A a‖ + ‖(A - STQop (d := d) ϑ t A) a‖ := norm_sub_le _ _
    _ ≤ W ^ (-D') + W ^ (-D') := add_le_add h1 h2
    _ = 2 * W ^ (-D') := by ring

/-- **The `L^∞` class gives the `ℓ¹` window**: the `L^∞` class of the good set gives the `ℓ¹` window of
`EKFastDecay` once `d W^{τ'} ≤ W^ε` (`zdistD ≤ d · zdistInf`).  As the private
`nqGood1_fast_of_cls`. -/
theorem fastDecay_of_diamInf :
    ∀ {d L k : ℕ}, 0 < d → 1 ≤ (L : ℝ) → ∀ {g s W ε τ' D δ : ℝ},
    (d : ℝ) * W ^ τ' ≤ W ^ ε → δ ≤ W ^ (-D) → ∀ {X : (Fin k → Zd d L) → ℂ},
    (∀ b : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ) →
    EKFastDecay g s W ε D X := by
  intro d L k hd hL g s W ε τ' D δ hdW hδ X hcls a ⟨i, j, hij⟩
  refine (hcls a ?_).trans hδ
  have hell : 0 < ellT L g s := ellT_pos hL
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (zdistD d L (a i - a j) : ℝ) ≤ (d : ℝ) * (STdiamInf a : ℝ) := by
    have h2 := zdistD_le_mul_zdistInf d L (a i - a j)
    have h3 : zdistInf d L (a i - a j) ≤ STdiamInf a :=
      Finset.le_sup (f := fun p : Fin k × Fin k => zdistInf d L (a p.1 - a p.2))
        (Finset.mem_univ (i, j))
    exact_mod_cast h2.trans (Nat.mul_le_mul_left d h3)
  have h4 := mul_le_mul_of_nonneg_left hdW hell.le
  have h5 : (d : ℝ) * (ellT L g s * W ^ τ') ≤ (d : ℝ) * (STdiamInf a : ℝ) := by
    calc (d : ℝ) * (ellT L g s * W ^ τ') = ellT L g s * ((d : ℝ) * W ^ τ') := by ring
      _ ≤ ellT L g s * W ^ ε := h4
      _ = W ^ ε * ellT L g s := by ring
      _ ≤ _ := hij
      _ ≤ _ := h1
  exact le_of_mul_le_mul_left h5 hd0

end QDecay


/-! ## 4. `hker` of the alternating chain from `ekSumDecay2_holds` -/

section Hker

/-- The specification of `ekSumDecay2_holds` at the constant `qProxy4C`. -/
private theorem QDriftA_qProxy4C_spec {d k : ℕ} (hd : 3 ≤ d) (hk : 2 ≤ k) {Λg κ' K : ℝ} (hΛ : 0 < Λg)
    (hκ' : 0 < κ') (hK : 0 < K) :
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λg →
      ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
      (L : ℝ) ^ d ≤ W ^ K →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ m : ℂ, ‖m‖ = 1 → κ' ≤ m.im → ∀ σ : Fin k → Bool, ∀ A : (Fin k → Zd d L) → ℂ,
        haveI : NeZero L := ⟨by omega⟩
        EKFastDecay g s W ε D A → EKSumZero A →
        ‖UN d L g (EKsgn m σ) s t A‖ ≤
          W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * ‖A‖ +
            W ^ (-D + qProxy4C d k Λg κ' K) := by
  have h : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' ∧ 0 < K := ⟨hd, hk, hΛ, hκ', hK⟩
  unfold qProxy4C
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec (ekSumDecay2_holds d k Λg κ' (prop5Decay_holds d Λg)
    (prop5Short_holds d Λg κ') (prop6Diff1_holds d Λg κ' (1 / 2)) hd hk hΛ hκ' K hK)).2

/-- **`hker` of the alternating chain from `ekSumDecay2_holds`**
((4.56) `sum_res_2`), every `σ`; pattern `hker_of_case1N`.
Sum-zero and window decay `≤ δ ≤ W^{-D}` give `W^{C₄ε} r^k M + W^{C₄} δ`, `C₄ = qProxy4C d k Λg κ' K`
(exponent `k`, not `k - 1`; no hypothesis on `σ`).  The `δ`-form: for `δ > 0`, `D'' = -log_W δ ≥ D`;
for `δ = 0`, every `D'' > 1` and a limit. -/
theorem hker_altQN :
    ∀ {d k : ℕ} (Λg κ' K : ℝ), 3 ≤ d → 2 ≤ k → 0 < Λg → 0 < κ' → 0 < K →
    ∀ {L : ℕ} [NeZero L], 3 ≤ L → ∀ {g : ℝ}, 0 < g → g ≤ Λg →
    ∀ {W ε τ' D : ℝ}, 1 < W → 0 < ε → ε < 1 → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
    (L : ℝ) ^ d ≤ W ^ K → (d : ℝ) * W ^ τ' ≤ W ^ ε → 1 < D →
    ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
    ∀ {E : ℝ}, |E| ≤ 2 → κ' ≤ (mE E).im →
    ∀ (σ : Fin k → Bool) (X : (Fin k → Zd d L) → ℂ) {M δ : ℝ}, 0 ≤ M → 0 ≤ δ → δ ≤ W ^ (-D) →
    (∀ b, ‖X b‖ ≤ M) → EKSumZero X →
    (∀ b : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ) →
    ∀ a : Fin k → Zd d L,
      ‖Ugen d L g E σ s t X a‖ ≤
        W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * M +
          W ^ qProxy4C d k Λg κ' K * δ := by
  intro d k Λg κ' K hd hk hΛ hκ' hK L _ hL g hg hgΛ W ε τ' D hW hε0 hε1 hWε hlog hLK hdW hD
    s t hs hst ht hWt E hE hκm σ X M δ hM hδ hδD hXM hXsum hXcls a
  have hCdef : ∀ (D'' : ℝ), 1 < D'' → δ ≤ W ^ (-D'') → ‖Ugen d L g E σ s t X a‖ ≤
      W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * M +
        W ^ (-D'' + qProxy4C d k Λg κ' K) := by
    intro D'' hD'' hδD''
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have hX : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr hXM
    have hfast : EKFastDecay g s W ε D'' X :=
      fastDecay_of_diamInf (by omega) hL1 hdW hδD'' hXcls
    have h := QDriftA_qProxy4C_spec hd hk hΛ hκ' hK L hL g hg hgΛ W ε D'' hW hε0 hε1 hD'' hWε hlog hLK
      s t hs hst ht hWt (mE E) (norm_mE hE) hκm σ X hfast hXsum
    have h2 : ‖Ugen d L g E σ s t X a‖ ≤ ‖UN d L g (EKsgn (mE E) σ) s t X‖ :=
      norm_le_pi_norm (UN d L g (EKsgn (mE E) σ) s t X) a
    calc ‖Ugen d L g E σ s t X a‖ ≤ ‖UN d L g (EKsgn (mE E) σ) s t X‖ := h2
      _ ≤ W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * ‖X‖ +
          W ^ (-D'' + qProxy4C d k Λg κ' K) := h
      _ ≤ _ := by gcongr
  set C := qProxy4C d k Λg κ' K with hC
  have hW0 : (0 : ℝ) < W := by linarith
  rcases hδ.eq_or_lt with h0 | hpos
  · -- `δ = 0`: let `D'' → ∞`
    subst h0
    rw [mul_zero, add_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    set D'' : ℝ := max 2 (C - Real.logb W η) with hD''
    have hD1 : 1 < D'' := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have h1 := hCdef D'' hD1 (Real.rpow_nonneg hW0.le _)
    have h2 : W ^ (-D'' + C) ≤ η := by
      calc W ^ (-D'' + C) ≤ W ^ (Real.logb W η) :=
            Real.rpow_le_rpow_of_exponent_le hW.le (by
              have := le_max_right 2 (C - Real.logb W η); linarith)
        _ = η := Real.rpow_logb hW0 hW.ne' hη
    linarith
  · -- `δ > 0`: `D'' = -log_W δ ≥ D`
    set D'' : ℝ := -Real.logb W δ with hD''
    have hWD'' : W ^ (-D'') = δ := by
      rw [hD'', neg_neg]; exact Real.rpow_logb hW0 hW.ne' hpos
    have hDle : D ≤ D'' := by
      have := (Real.logb_le_iff_le_rpow hW hpos).2 hδD
      rw [hD'']; linarith
    have h1 := hCdef D'' (by linarith) hWD''.symm.le
    rw [Real.rpow_add hW0, hWD''] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring

/-- **The field `hker` of `GridAssemblyHypN` for the alternating
chain** (pattern `nonAlt_hkerN`; RBM2D `altQ_hker`),
`Cls = altClsQN`, `κ = kappaAltQN`, `εK = epsAltQN`; no hypothesis on `σ`. -/
theorem alt_hkerQN :
    ∀ {d k : ℕ} (Λg κ' K : ℝ), 3 ≤ d → 2 ≤ k → 0 < Λg → 0 < κ' → 0 < K →
    ∀ {L : ℕ} [NeZero L], 3 ≤ L → ∀ {g : ℝ}, 0 < g → g ≤ Λg →
    ∀ {W ε τ' Dc : ℝ}, 1 < W → 0 < ε → ε < 1 → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
    (L : ℝ) ^ d ≤ W ^ K → (d : ℝ) * W ^ τ' ≤ W ^ ε → 1 < Dc →
    ∀ {Kg : ℕ} {u : ℕ → ℝ}, (∀ i ≤ Kg, 0 ≤ u i) → (∀ i m, i ≤ m → m ≤ Kg → u i ≤ u m) →
    u Kg ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - u Kg) / (1 - u 0) →
    ∀ {E : ℝ}, |E| ≤ 2 → κ' ≤ (mE E).im → ∀ σ : Fin k → Bool,
    ∀ i m, i ≤ m → m ≤ Kg → ∀ (X : (Fin k → Zd d L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → altClsQN d L g W τ' Dc u i δ X →
      ∀ a : Fin k → Zd d L,
      ‖Ugen d L g E σ (u i) (u m) X a‖ ≤
        kappaAltQN d k Λg κ' K g W ε u i m * M + epsAltQN d k Λg κ' K W i m * δ := by
  intro d k Λg κ' K hd hk hΛ hκ' hK L _ hL g hg hgΛ W ε τ' Dc hW hε0 hε1 hWε hlog hLK hdW hDc
    Kg u hu0 hmono huK hWt E hE hκm σ i m him hmK X M δ hM hδ hXM hcls a
  obtain ⟨hXsum, hδD, hXcls⟩ := hcls
  have hiK : i ≤ Kg := him.trans hmK
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hgL : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
  have hK1 : u Kg < 1 := by linarith
  have hmK' : u m ≤ u Kg := hmono m Kg hmK le_rfl
  have hi0 : u 0 ≤ u i := hmono 0 i (Nat.zero_le _) hiK
  have hwin : W⁻¹ ≤ (1 - u m) / (1 - u i) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith [hmono i Kg hiK le_rfl]) (by linarith)
  exact hker_altQN Λg κ' K hd hk hΛ hκ' hK hL hg hgΛ hW hε0 hε1 hWε hlog hLK hdW hDc (hu0 i hiK)
    (hmono i m him hmK) (hmK'.trans huK) hwin hE hκm σ X hM hδ hδD hXM hXsum hXcls a

end Hker

/-! ## 4g. `hker` of the alternating chain over a carrier (`QProxyG_KerEK4` at `gK`, comparison to the size level, two constants `C4 ≤ Cv`) -/

section HkerG

variable {d k : ℕ} {sz : Sizes d}

/-- **`fastDecay_of_diamInfg`** (band `fastDecay_of_diamInf`, with the comparison of couplings): the `L^∞` class at the size level
(`ℓ_s(lam) W^{τ'} ≤ diam_∞ b ⟹ ‖X b‖ ≤ δ`, `d √A W^{τ'} ≤ W^ε`) gives the `ℓ¹` window of `EKFastDecay` at the kernel coupling `gK`
(`ℓ(lam) ≤ √A ℓ(gK)`, `step34Gen_ellT_ge`). -/
theorem fastDecay_of_diamInfg {gK : ℕ → ℝ} {A : ℝ} (hd : 0 < d)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hW0 : 0 < ((sz.W n : ℕ) : ℝ)) {ε τ' D δ s : ℝ}
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hδ : δ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    {X : (Fin k → Zd d (sz.L n)) → ℂ}
    (hX : ∀ b : Fin k → Zd d (sz.L n), ellT (sz.L n) (sz.lam n) s * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ) :
    EKFastDecay (gK n) s ((sz.W n : ℕ) : ℝ) ε D X := by
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hell := step34Gen_ellT_ge hcmp hA n s
  intro a' ⟨i, j, hij⟩
  refine (hX a' ?_).trans hδ
  have hdist : (zdistD d (sz.L n) (a' i - a' j) : ℝ) ≤ d * (STdiamInf a' : ℝ) := by
    have h3 : zdistInf d (sz.L n) (a' i - a' j) ≤ STdiamInf a' :=
      Finset.le_sup (f := fun p : Fin k × Fin k => zdistInf d (sz.L n) (a' p.1 - a' p.2)) (Finset.mem_univ (i, j))
    exact_mod_cast (zdistD_le_mul_zdistInf d (sz.L n) (a' i - a' j)).trans (Nat.mul_le_mul_left d h3)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hE0 : 0 ≤ ellT (sz.L n) (gK n) s := le_min (le_trans zero_le_one (le_max_right _ _)) (Nat.cast_nonneg _)
  refine le_of_mul_le_mul_left (a := (d : ℝ)) ?_ hd0
  calc (d : ℝ) * (ellT (sz.L n) (sz.lam n) s * W ^ τ')
      ≤ (d : ℝ) * (Real.sqrt A * ellT (sz.L n) (gK n) s * W ^ τ') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hell (Real.rpow_nonneg hW0.le _)) hd0.le
    _ = ellT (sz.L n) (gK n) s * ((d : ℝ) * Real.sqrt A * W ^ τ') := by ring
    _ ≤ ellT (sz.L n) (gK n) s * W ^ ε := mul_le_mul_of_nonneg_left hdW hE0
    _ = W ^ ε * ellT (sz.L n) (gK n) s := mul_comm _ _
    _ ≤ _ := hij
    _ ≤ _ := hdist

/-- **`hker_altQNg`** (band `hker_altQN`): **`hker` of the alternating chain from `ekSumDecay2_holds` over a carrier**: `QProxyG_KerEK4` at the kernel coupling `gK`
(`hKer`, constant `C4`), the comparison (`hcmp`, `hA`) to the size level `sz.lam`, the two constants `C4 ≤ Cv` with `A^k ≤ W^{(Cv-C4)ε}`; sum-zero
`X` of sup-norm `≤ M`, `≤ δ ≤ W^{-D}` on the `L^∞` window `ℓ_s(lam) W^{τ'}`, every `σ`: `‖𝒰_{s,t,σ} X (a)‖ ≤ W^{Cv ε} r^k M + W^{Cv} δ`,
`r = (lam²+|1-s|)/(lam²+|1-t|)`. -/
theorem hker_altQNg (C : FlowFM sz) {gK : ℕ → ℝ} {A C4 Cv KL : ℝ} (hd : 0 < d)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : QProxyG_KerEK4 C gK k KL C4 n) (hCv : C4 ≤ Cv) {ε τ' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ k ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) {D : ℝ} (hD : 1 < D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s))
    (σ : Fin k → Bool) (X : (Fin k → Zd d (sz.L n)) → ℂ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hδD : δ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) (hXM : ∀ b, ‖X b‖ ≤ M) (hsum : EKSumZero X)
    (hXcls : ∀ b : Fin k → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) s * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ)
    (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ s t X a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) *
        ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k * M + ((sz.W n : ℕ) : ℝ) ^ Cv * δ := by
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have ht1 : t < 1 := NQGood1Gen_t_lt_one hW ht hWt
  have hL2 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := pow_pos (by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)) 2
  have hwin : t ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    linarith [div_le_div_of_nonneg_right (hcmp n).2.1 hL2.le]
  have hX : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr hXM
  have hrat := step34Gen_ratio_pow_le hcmp hA n (v := s) ht1 k
  have hat : ∀ D'' : ℝ, 1 < D'' → δ ≤ W ^ (-D'') → ‖Step2Gen_UN C n σ s t X a‖ ≤
      W ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k * M + W ^ (-D'' + Cv) := by
    intro D'' hD'' hδ''
    have h := hKer hW hLK ε D'' hε0 hε1 hD'' hWε hlog s t hs hst hwin hWt σ X
      (fastDecay_of_diamInfg hd hcmp hA hW0 hdW hδ'' hXcls) hsum
    have e0 : W ^ (C4 * ε) * W ^ ((Cv - C4) * ε) = W ^ (Cv * ε) := by rw [← Real.rpow_add hW0]; ring_nf
    have e1 : W ^ (C4 * ε) * ((gK n ^ 2 + |1 - s|) / (gK n ^ 2 + |1 - t|)) ^ k * ‖X‖ ≤
        W ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k * M := by
      calc _ ≤ W ^ (C4 * ε) * (A ^ k * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k) * M := by gcongr
        _ ≤ W ^ (C4 * ε) * (W ^ ((Cv - C4) * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k) * M := by gcongr
        _ = _ := by rw [← e0]; ring
    have e2 : W ^ (-D'' + C4) ≤ W ^ (-D'' + Cv) := Real.rpow_le_rpow_of_exponent_le hW.le (by linarith)
    exact (norm_le_pi_norm (Step2Gen_UN C n σ s t X) a).trans (h.trans (by linarith))
  rcases hδ.eq_or_lt with h0 | hpos
  · subst h0
    rw [mul_zero, add_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hD1 : 1 < max 2 (Cv - Real.logb W η) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have h1 := hat _ hD1 (Real.rpow_nonneg hW0.le _)
    have h2 : W ^ (-max 2 (Cv - Real.logb W η) + Cv) ≤ η :=
      calc _ ≤ W ^ (Real.logb W η) := Real.rpow_le_rpow_of_exponent_le hW.le (by linarith [le_max_right 2 (Cv - Real.logb W η)])
        _ = η := Real.rpow_logb hW0 hW.ne' hη
    linarith
  · have hWD : W ^ (-(-Real.logb W δ)) = δ := by rw [neg_neg]; exact Real.rpow_logb hW0 hW.ne' hpos
    have hDle : D ≤ -Real.logb W δ := by linarith [(Real.logb_le_iff_le_rpow hW hpos).2 hδD]
    have h1 := hat (-Real.logb W δ) (by linarith) hWD.symm.le
    rw [Real.rpow_add hW0, hWD] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring

/-- **`alt_hkerQNg`** (band `alt_hkerQN`): the field `hker` of `GridAssemblyHypNg` for the alternating chain over a carrier,
`Cls = altClsQN` at the size level `sz.lam`, `κ = kappaAltQNg`, `εK = epsAltQNg`; no hypothesis on `σ`. -/
theorem alt_hkerQNg (C : FlowFM sz) {gK : ℕ → ℝ} {A C4 Cv KL : ℝ} (hd : 0 < d)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : QProxyG_KerEK4 C gK k KL C4 n) (hCv : C4 ≤ Cv) {ε τ' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ k ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) {Dc : ℝ} (hDc : 1 < Dc) {Kg : ℕ} {u : ℕ → ℝ}
    (hu0 : ∀ i ≤ Kg, 0 ≤ u i) (hmono : ∀ i m, i ≤ m → m ≤ Kg → u i ≤ u m)
    (huK : u Kg ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - u Kg) / (1 - u 0))
    (σ : Fin k → Bool) (i m : ℕ) (him : i ≤ m) (hmK : m ≤ Kg) (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hXM : ∀ b, ‖X b‖ ≤ M)
    (hcls : altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i δ X) (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ (u i) (u m) X a‖ ≤ kappaAltQNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m * M +
      epsAltQNg Cv ((sz.W n : ℕ) : ℝ) i m * δ := by
  obtain ⟨hXsum, hδD, hXcls⟩ := hcls
  have hiK : i ≤ Kg := him.trans hmK
  have hmK' : u m ≤ u Kg := hmono m Kg hmK le_rfl
  have hi0 : u 0 ≤ u i := hmono 0 i (Nat.zero_le _) hiK
  have hK1 : u Kg < 1 := NQGood1Gen_t_lt_one hW huK hWt
  have hwin : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - u m) / (1 - u i) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith [hmono i Kg hiK le_rfl]) (by linarith)
  exact hker_altQNg C hd hcmp hA hKer hCv hW hLK hε0 hε1 hWε hlog hdW hAk hDc (hu0 i hiK) (hmono i m him hmK)
    (hmK'.trans huK) hwin σ X hM hδ hδD hXM hXsum hXcls a

end HkerG


/-! ## 5. The initial-term class of the `𝒬`-process -/

section A0cls

/-- A pair of indices realising `R ≤ diam_∞ b` gives the `ℓ¹` window `R ≤ zdistD (b i - b j)`
(`zdistInf ≤ zdistD`; the sup over the finite nonempty set of pairs is attained). -/
private theorem QDriftA_window_of_diamInf {d L k : ℕ} (hk : 1 ≤ k) {R : ℝ} (b : Fin k → Zd d L)
    (hb : R ≤ (STdiamInf b : ℝ)) : ∃ i j : Fin k, R ≤ (zdistD d L (b i - b j) : ℝ) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k × Fin k))
    Finset.univ_nonempty (fun p : Fin k × Fin k => zdistInf d L (b p.1 - b p.2))
  refine ⟨p.1, p.2, hb.trans ?_⟩
  have h1 : STdiamInf b = zdistInf d L (b p.1 - b p.2) := hp
  rw [h1]
  exact_mod_cast zdistInf_le_zdistD d L _

/-- **The threshold `W₀(d, m, K, C, c, C₀, ε', D')` of the decay clause of `Qop_fastDecay`**,
chosen once for all `L, g, W, t`; `2` outside the range `0 < C`, `0 < c`, `0 < ε'`.  (Pattern
`qProxyW0`: the threshold is a constant, so that the class statements below have
`altClsQN` as their conclusion.) -/
def QDriftA_W0 (d m : ℕ) (K C c C₀ ε' D' : ℝ) : ℝ :=
  if h : 0 < C ∧ 0 < c ∧ 0 < ε' then
    Classical.choose (Qop_fastDecay d m K C c C₀ ε' D' h.1 h.2.1 h.2.2)
  else 2

/-- The spec of `QDriftA_W0`: `1 < W₀`, and the decay clause of `Qop_fastDecay` holds for `W ≥ W₀`. -/
private theorem QDriftA_W0_spec (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε' : 0 < ε') :
    1 < QDriftA_W0 d m K C c C₀ ε' D' ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g →
      ∀ W : ℝ, QDriftA_W0 d m K C c C₀ ε' D' ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D' A →
        ∀ a : Fin (m + 1) → Zd d L, (∃ i j, W ^ ε' * ellT L g t ≤ (zdistD d L (a i - a j) : ℝ)) →
          ‖STQop (d := d) ϑ t A a‖ ≤ 2 * W ^ (-D') := by
  have h : 0 < C ∧ 0 < c ∧ 0 < ε' := ⟨hC, hc, hε'⟩
  have hdef : QDriftA_W0 d m K C c C₀ ε' D' =
      Classical.choose (Qop_fastDecay d m K C c C₀ ε' D' h.1 h.2.1 h.2.2) := by
    unfold QDriftA_W0; rw [dite_eq_left_of_eq_true (eq_true h)]
  rw [hdef]
  exact Classical.choose_spec (Qop_fastDecay d m K C c C₀ ε' D' h.1 h.2.1 h.2.2)

theorem QDriftA_W0_gt_one (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
    1 < QDriftA_W0 d m K C c C₀ ε' D' :=
  (QDriftA_W0_spec d m K C c C₀ ε' D' hC hc hε').1

/-- **The initial-term class** (RBM2D `goodSetN_A0cls`; pattern `goodSetN_A0clsN`): for `M ∈ GoodSetN … u_i` at loop length `k = m + 1`, the tensor
`𝒬_{u_i}(𝓛-𝒦)_{u_i,σ}(M)` is in `altClsQN … i` with `δ = 2 W^{-D'}`, **at the radius `ε'`**, not `τ'`:
the decay clause of `GoodSetN` at length `k ≤ 2k+2` gives the `L^∞` decay at radius `τ'`; `fastDecay_of_diamInf`
(`d W^{τ'} ≤ W^{ε'}`) turns it into the `ℓ¹` window `W^{ε'}`; `Qop_fastDecay` decays `𝒬A` there (given the
crude sup `‖A‖ ≤ W^{C₀}`, a hypothesis, and `W ≥ W₀ = QDriftA_W0`); `diam_∞ ≥ ℓ W^{ε'}` gives a pair with
`zdistD ≥ W^{ε'} ℓ`.  Sum-zero by `QopAlgebra_Psum_Qop`.  `Γ Λ Φ` occur only in the `GoodSetN`
membership. -/
theorem goodSetN_A0clsQN {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) (m : ℕ)
    (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε')
    {n : ℕ} {E Γ Λ Φ τ' Dc : ℝ} {u : ℕ → ℝ} {i : ℕ}
    (hW : QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hlam : 0 < sz.lam n) (hu0 : 0 ≤ u i) (hu1 : u i < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ sz.GoodSetN n E (u i) (m + 1) Γ Λ Φ τ' D')
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (σ : Fin (m + 1) → Bool)
    (hcrude : ‖fun a => sz.STLKM n E (u i) M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
    altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc u i
      (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (STQop (d := d) ϑ (u i) (fun a => sz.STLKM n E (u i) M σ a)) := by
  obtain ⟨hW₀, H⟩ := QDriftA_W0_spec d m K C c C₀ ε' D' hC hc hε'
  have hW1 : 1 ≤ ((sz.W n : ℕ) : ℝ) := (hW₀.trans_le hW).le
  have hcls := (goodSetN_A0clsN sz (k := m + 1) (by omega) (E := E) (Γ := Γ) (Λ := Λ) (Φ := Φ)
    (τ' := τ') (D' := D') (Dc := D') le_rfl hW1 (u := u) (i := i) hM σ).2
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hfast : EKFastDecay (sz.lam n) (u i) ((sz.W n : ℕ) : ℝ) ε' D'
      (fun a => sz.STLKM n E (u i) M σ a) :=
    fastDecay_of_diamInf (by omega) hL1 hdW le_rfl hcls
  refine ⟨QDriftA_ekSumZero_of_Psum fun a₁ => QopAlgebra_Psum_Qop (d := d) ϑ (hϑ.1 (u i)) _ a₁,
    hDD, fun b hb => ?_⟩
  obtain ⟨i', j', hij⟩ := QDriftA_window_of_diamInf (by omega) b
    (R := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) (u i)) (by rw [mul_comm]; exact hb)
  exact H (sz.L n) (sz.three_le_L n) (sz.lam n) hlam ((sz.W n : ℕ) : ℝ) hW hLK ϑ hϑ (u i) hu0 hu1 _
    hcrude hfast b ⟨i', j', hij⟩

/-- **The initial-term class on the event `{0 < τ}`** (pattern `nonAlt_hA0clsN`): `A^Q_0 = aTrueQN … 0 ω` is in `altClsQN … 0` with `δ_0 = 2 W^{-D'}` when `H_j ∈
GoodSetN(u_j)` for `j < τ`, and `‖A_0‖ ≤ W^{C₀}` (crude sup) on `{0 < τ}`. -/
theorem alt_hA0clsQN {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) (m : ℕ)
    (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε')
    {n : ℕ} (σ : Fin (m + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
    (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (hW : QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hlam : 0 < sz.lam n) (hs0 : 0 ≤ s n) (hs1 : s n < 1)
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (hτG : ∀ ω j, j < τ ω → pathH sz s v Kg n j ω ∈ sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1)
      (Γ n) (Λ n) (Φ n) τ' D')
    (hcrude : ∀ ω, 0 < τ ω → ‖AvecN sz E s v Kg n 0 σ ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
    ∀ ω, 0 < τ ω →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) 0
        (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (aTrueQN sz E s v Kg n ϑ σ 0 ω) := by
  intro ω hω
  have hu0 : 0 ≤ gridTime s v Kg n 0 := by rw [ST_gridTime_zero]; exact hs0
  have hu1 : gridTime s v Kg n 0 < 1 := by rw [ST_gridTime_zero]; exact hs1
  exact goodSetN_A0clsQN sz hd m K C c C₀ ε' D' hC hc hε' (E := E n) (Γ := Γ n) (Λ := Λ n) (Φ := Φ n)
    (τ' := τ') (Dc := Dc) (u := gridTime s v Kg n) (i := 0) hW hLK hdW hDD hlam hu0 hu1 (hτG ω 0 hω) ϑ
    hϑ σ (hcrude ω hω)

end A0cls

/-! ## 5g. The initial-term class of the `𝒬`-process over a carrier -/

section A0clsG

variable {d : ℕ} {sz : Sizes d}

/-- **`goodSetNg_A0clsQNg`** (band `goodSetN_A0clsQN`): for `M ∈ GoodSetNg … u_i`, the tensor `𝒬_{u_i}(𝓛-𝒦)_{u_i,σ}(M)` is in `altClsQN … i`
with `δ = 2 W^{-D'}` at the radius `ε'` (size level `sz.lam`; no coupling comparison is read). -/
theorem goodSetNg_A0clsQNg (Cm : Step2Mat sz) (hd : 3 ≤ d) (m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε')
    {n : ℕ} {Γ Λ Φ τ' Dc : ℝ} {u : ℕ → ℝ} {i : ℕ}
    (hW : QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hlam : 0 < sz.lam n) (hu0 : 0 ≤ u i) (hu1 : u i < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : GoodSetNg Cm n (u i) (m + 1) Γ Λ Φ τ' D' M)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (σ : Fin (m + 1) → Bool)
    (hcrude : ‖fun a => STLKMg Cm n (u i) M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
    altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc u i (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (STQop (d := d) ϑ (u i) (fun a => STLKMg Cm n (u i) M σ a)) := by
  obtain ⟨hW₀, H⟩ := QDriftA_W0_spec d m K C c C₀ ε' D' hC hc hε'
  have hW1 : 1 ≤ ((sz.W n : ℕ) : ℝ) := (hW₀.trans_le hW).le
  have hcls := (goodSetNg_A0clsNg (Cm := Cm) (k := m + 1) (by omega) (Dc := D') (τ' := τ') le_rfl hW1 (u := u) (i := i) hM σ).2
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hfast : EKFastDecay (sz.lam n) (u i) ((sz.W n : ℕ) : ℝ) ε' D' (fun a => STLKMg Cm n (u i) M σ a) :=
    fastDecay_of_diamInf (by omega) hL1 hdW le_rfl hcls
  refine ⟨QDriftA_ekSumZero_of_Psum fun a₁ => QopAlgebra_Psum_Qop (d := d) ϑ (hϑ.1 (u i)) _ a₁,
    hDD, fun b hb => ?_⟩
  obtain ⟨i', j', hij⟩ := QDriftA_window_of_diamInf (by omega) b
    (R := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) (u i)) (by rw [mul_comm]; exact hb)
  exact H (sz.L n) (sz.three_le_L n) (sz.lam n) hlam ((sz.W n : ℕ) : ℝ) hW hLK ϑ hϑ (u i) hu0 hu1 _
    hcrude hfast b ⟨i', j', hij⟩

/-- **`alt_hA0clsQNg`** (band `alt_hA0clsQN`): the initial-term class on the event `{0 < τ}`. -/
theorem alt_hA0clsQNg (Cm : Step2Mat sz) (hd : 3 ≤ d) (m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε')
    {n : ℕ} (σ : Fin (m + 1) → Bool) (s v : ℕ → ℝ) (Kg : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (hW : QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hlam : 0 < sz.lam n) (hs0 : 0 ≤ s n) (hs1 : s n < 1)
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (hτG : ∀ ω j, j < τ ω → GoodSetNg Cm n (gridTime s v Kg n j) (m + 1) (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v Kg n j ω))
    (hcrude : ∀ ω, 0 < τ ω → ‖AvecNg Cm s v Kg n 0 σ ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
    ∀ ω, 0 < τ ω →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) 0
        (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (aTrueQNg Cm s v Kg n ϑ σ 0 ω) := by
  intro ω hω
  have hu0 : 0 ≤ gridTime s v Kg n 0 := by rw [ST_gridTime_zero]; exact hs0
  have hu1 : gridTime s v Kg n 0 < 1 := by rw [ST_gridTime_zero]; exact hs1
  exact goodSetNg_A0clsQNg Cm hd m K C c C₀ ε' D' hC hc hε' (Γ := Γ n) (Λ := Λ n) (Φ := Φ n)
    (τ' := τ') (Dc := Dc) (u := gridTime s v Kg n) (i := 0) hW hLK hdW hDD hlam hu0 hu1 (hτG ω 0 hω) ϑ
    hϑ σ (hcrude ω hω)

end A0clsG


end RBM.Ind

end
