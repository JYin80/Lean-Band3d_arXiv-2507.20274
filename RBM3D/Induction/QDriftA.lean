/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QGridA
import RBM3D.Induction.QProxy
import RBM3D.Induction.NQGood2
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopNorm
import RBM3D.Evolution.SumDecayZero

/-!
# S3-15a (ticket T2250): the drift and the initial term of the `𝒬`-process, `d ≥ 3`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: `int_K-L+Q` (`3_5:1337-1346`),
`lem_+Q` (`3_5:1284-1289`), `lem:sum_decay` `(sum_res_2)`, `(eq:alternatecase1)` (`3_5:1680-1690`).
Port of RBM2D `Induction/AltDriftQ.lean` at `c9a24cf` (`dFlowQ` `:86`, `AltDriftQ_Qop_add/sub`
`:95-113`, `dGridQN_eq_dFlowQ` `:119-180`, `altQ_hker` `:203`, `AltDriftQ_meas_*` `:407-513`),
re-derived for `d ≥ 3`: the `ℚ/𝔼` split of RBM2D collapses, because the merged EK-4 `(sum_res_2)`
(`ekSumDecay2_holds`) needs only `EKSumZero` and `EKFastDecay`, for every `σ`, and the drift
`𝒬_u(ℬ₁+ℬ₂+ℬ₃) + ℬ₄ + ℬ₅` is sum-zero pathwise (paper-delta candidate `T2250a`).  All statements are
deterministic, level-free, per matrix or per grid time.

## What is here (namespace `RBM.Ind`)

* §1 the vocabulary: `altB4N`, `altB5N`, `dFlowQN`, `altClsQN`, `kappaAltQN`, `epsAltQN` (the six
  definitions of the ticket, verbatim from the check file).
* §2 `dGridQN_eq_dFlowQN` (target 2), `dFlowQN_sumZero` (target 3).
* §3 `aTrueQN_sumZero`, `Qop_fastDecay`, `fastDecay_of_diamInf` (targets 4a, 4b, 4c).
* §4 `hker_altQN`, `alt_hkerQN` (targets 5a, 5b): EK-4 in the field shape of
  `GridAssemblyHypN.hker`.
* §5 `goodSetN_A0clsQN`, `alt_hA0clsQN` (target 6): the initial-term class, radius `ε'` (not `τ'`).
* §6 `measurable_altB4N`, `measurable_altB5N`, `measurable_STQopDriftN`, `measurable_dFlowQN`
  (target 7), with copies of the private measurability helpers of `GridGoodN` (prefix `QDriftA_`).
* §7 compiled nonempty instances (namespace `QDriftAInst`).

Every unpinned helper is `private` or prefixed `QDriftA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. The vocabulary (the six definitions of the ticket, verbatim) -/

/-- `ℬ₄ = [𝒬_u, Θ^{(m+1)}_{u,σ}](𝓛-𝒦)_{u,σ}(H)` at a fine matrix `H` (`int_K-L+Q`, `3_5:1337-1346`; the
second summand of the merged `dGridQN`, `QGridA.lean:1274`, at a matrix; RBM2D `B4` inside `altB`,
`StoppedEndDefs.lean:88`). -/
def altB4N {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ u
        (ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u (fun b => sz.STLKM n E u H σ b)) a -
      ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
        (STQop (d := d) ϑ u (fun b => sz.STLKM n E u H σ b)) a

/-- `ℬ₅ = -[𝒫∘(𝓛-𝒦)_{u,σ}(H)]_{a₁} ∂_uϑ_{u,a}` with the paper's sign inside (`3_5:1345`; the last term of
`dGridQN`). -/
def altB5N {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => -(STPsum (d := d) (fun b => sz.STLKM n E u H σ b) (a 0) * deriv (fun τ => ϑ τ a) u)

/-- **The drift of `int_K-L+Q` at a matrix**: `𝒬_u(ℬ₁ + ℬ₂ + ℬ₃) + ℬ₄ + ℬ₅` (RBM2D `dFlowQ`,
`AltDriftQ.lean:86`; the first summand is the text of `dGridQN` with `H` for `pathH … j ω`). -/
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

/-- **The kernel class of the alternating chain** (d ≥ 3 replacement of RBM2D `AltCase4Cls`,
`AltDriftQ.lean:197`; pattern `nonAltClsN`, `NQGood2.lean:79`): `Cls i δ X :⇔` `X` is sum-zero (`EKSumZero`),
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

/-! ## 2. Targets 2 and 3: the drift along the walk and its sum-zero structure -/

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

/-- **Target 2** (`T2250_dGridQN_eq_dFlowQN`): `dGridQN` along the walk is `dFlowQN` at the grid state
(RBM2D `dGridQN_eq_dFlowQ`, `AltDriftQ.lean:119-180`): `dGridQN` already has `ℬ₄`, `ℬ₅` inside, so
this is an unfolding of `dGridQN` and `AvecN`. -/
theorem dGridQN_eq_dFlowQN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    dGridQN sz E s t K n ϑ σ j ω =
      dFlowQN sz n (E n) (gridTime s t K n j) ϑ σ (pathH sz s t K n j ω) := by
  funext a
  unfold dGridQN dFlowQN altB4N altB5N
  exact sub_eq_add_neg _ _

/-- **Target 3** (`T2250_dFlowQN_sumZero`): `𝒫ℬ₄ = 𝒫ℬ₅ = 0`, hence `𝒬_uℬ₄ = ℬ₄`, `𝒬_uℬ₅ = ℬ₅`, and the
drift is sum-zero in the EK-4 form, for every `σ`.  `𝒫ℬ₄ = 𝒫𝒬(Θ𝒜) - 𝒫Θ(𝒬𝒜) = 0` by
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

/-! ## 3. Target 4: the `𝒬`-process is sum-zero, and decay survives `𝒬_t` -/

section QDecay

/-- **Target 4a** (`T2250_aTrueQN_sumZero`): the `𝒬`-process (in particular `A^Q_0`) is sum-zero in the
EK-4 form. -/
theorem aTrueQN_sumZero {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (∀ a₁ : Zd d (sz.L n), ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁),
      ϑ (gridTime s t K n j) a = 1) →
    EKSumZero (aTrueQN sz E s t K n ϑ σ j ω) := by
  intro hsum
  exact QDriftA_ekSumZero_of_Psum fun a₁ =>
    QopAlgebra_Psum_Qop (d := d) ϑ hsum (AvecN sz E s t K n j σ ω) a₁

/-- **Target 4b** (`T2250_Qop_fastDecay`): decay survives `𝒬_t`.  `𝒬A = A - (A - 𝒬A)`, with
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

/-- **Target 4c** (`T2250_fastDecay_of_diamInf`): the `L^∞` class of the good set gives the `ℓ¹` window of
`EKFastDecay` once `d W^{τ'} ≤ W^ε` (`zdistD ≤ d · zdistInf`).  The proof of the private
`nqGood1_fast_of_cls` (`NQGood1.lean:278`), copied. -/
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


/-! ## 4. Targets 5a, 5b: `hker` of the alternating chain from EK-4 -/

section Hker

/-- The spec of EK-4 at the constant `qProxy4C` (`ekSumDecay2_holds`); a copy of the private
`qProxy4C_spec` (`QProxy.lean:519`). -/
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

/-- **Target 5a** (`T2250_hker_altQN`): **`hker` of the alternating chain from EK-4**
(`ekSumDecay2_holds`, `(sum_res_2)`), every `σ`; pattern `hker_of_case1N` (`NQGood1.lean:310-376`).
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

/-- **Target 5b** (`T2250_alt_hkerQN`): **the field `hker` of `GridAssemblyHypN` for the alternating
chain** (pattern `nonAlt_hkerN`, `NQGood2.lean:252-282`; RBM2D `altQ_hker`, `AltDriftQ.lean:203`),
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

/-! ## 5. Target 6: the initial-term class of the `𝒬`-process -/

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

/-- **The threshold `W₀(d, m, K, C, c, C₀, ε', D')` of the decay clause of `Qop_fastDecay`** (target 4b),
chosen once for all `L, g, W, t`; `2` outside the range `0 < C`, `0 < c`, `0 < ε'`.  (Pattern
`qProxyW0`, `QProxy.lean:456`: the threshold is a constant, so that the class statements below have
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

/-- **Target 6a, the initial-term class** (RBM2D `goodSetN_A0cls`; pattern `goodSetN_A0clsN`,
`NQGood2.lean:284`): for `M ∈ GoodSetN … u_i` at loop length `k = m + 1`, the tensor
`𝒬_{u_i}(𝓛-𝒦)_{u_i,σ}(M)` is in `altClsQN … i` with `δ = 2 W^{-D'}`, **at the radius `ε'`**, not `τ'`:
clause (Dec) of `GoodSetN` at length `k ≤ 2k+2` gives the `L^∞` decay at radius `τ'`; `fastDecay_of_diamInf`
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

/-- **Target 6b, the initial-term class on the event `{0 < τ}`** (pattern `nonAlt_hA0clsN`,
`NQGood2.lean:303`): `A^Q_0 = aTrueQN … 0 ω` is in `altClsQN … 0` with `δ_0 = 2 W^{-D'}` when `H_j ∈
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

/-! ## 6. Target 7: measurability of the drift tensors in `H` -/

section Meas

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-! Copies of the private measurability helpers of `GridGoodN.lean:255-346` (`gridGood_meas_STLIM`,
`_STLKIM`, `_loopFine`, `_STksimLKM`, `_STelklkM`, `_STavgErrM`, `_STegtM`; ticket T2146, `2f246bf`). -/

private theorem QDriftA_meas_STLIM (E τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLIM sz n E τ H I :=
  (walk_measurable_loopL d (sz.L n) (sz.W n) (zt E τ) I).comp
    (walk_measurable_blockMat d (sz.L n) (sz.W n))

private theorem QDriftA_meas_STLKIM (E τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLKIM sz n E τ H I :=
  (QDriftA_meas_STLIM sz n E τ I).sub_const _

private theorem QDriftA_meas_loopFine (E u : ℝ) {j : ℕ} (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      loopFine d (sz.L n) (sz.W n) H (zt E u) σ a :=
  walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E u) σ a

private theorem QDriftA_meas_STLKM (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      sz.STLKM n E u H σ a :=
  (QDriftA_meas_loopFine sz n E u σ a).sub_const _

private theorem QDriftA_meas_STksimLKM (E u : ℝ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STksimLKM sz n E u H l I := by
  unfold STksimLKM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  refine Measurable.add ?_ ?_
  · exact Measurable.ite (MeasurableSet.const _)
      (((QDriftA_meas_STLKIM sz n E u _).mul_const _).mul_const _) measurable_const
  · exact Measurable.ite (MeasurableSet.const _)
      ((measurable_const.mul_const _).mul (QDriftA_meas_STLKIM sz n E u _)) measurable_const

private theorem QDriftA_meas_STelklkM (E u : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STelklkM sz n E u H I := by
  unfold STelklkM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((QDriftA_meas_STLKIM sz n E u _).mul_const _).mul (QDriftA_meas_STLKIM sz n E u _)

private theorem QDriftA_meas_STavgErrM (E u : ℝ) (σ : Bool) (a : Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STavgErrM sz n E u H σ a := by
  unfold STavgErrM
  exact (QDriftA_meas_STLIM sz n E u _).sub_const _

private theorem QDriftA_meas_STegtM (E u : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STegtM sz n E u H I := by
  unfold STegtM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((QDriftA_meas_STavgErrM sz n E u _ a).mul_const _).mul (QDriftA_meas_STLIM sz n E u _)

/-- The three tensor operators are measurable images of measurable tensor-valued maps. -/
private theorem QDriftA_meas_Psum {α : Type*} [MeasurableSpace α] {L m : ℕ} [NeZero L]
    {A : α → (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ b, Measurable fun x => A x b) (a₁ : Zd d L) :
    Measurable fun x => STPsum (d := d) (A x) a₁ :=
  Finset.measurable_sum _ fun b _ => hA b

private theorem QDriftA_meas_Qop {α : Type*} [MeasurableSpace α] {L m : ℕ} [NeZero L]
    (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (u : ℝ)
    {A : α → (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ b, Measurable fun x => A x b)
    (a : Fin (m + 1) → Zd d L) : Measurable fun x => STQop (d := d) ϑ u (A x) a :=
  (hA a).sub ((QDriftA_meas_Psum hA (a 0)).mul_const _)

private theorem QDriftA_meas_ThetaN {α : Type*} [MeasurableSpace α] {L m : ℕ} [NeZero L] (g : ℝ)
    (μs : Fin (m + 1) → ℂ) (u : ℝ)
    {A : α → (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ b, Measurable fun x => A x b)
    (a : Fin (m + 1) → Zd d L) : Measurable fun x => ThetaN d L g μs u (A x) a :=
  Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun b _ =>
    measurable_const.mul (hA _)

/-- **Target 7a** (`measurable_altB4N`): `H ↦ ℬ₄(H)_a` is measurable, for every `a` (no hypothesis). -/
theorem measurable_altB4N (E u : ℝ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      altB4N sz n E u ϑ σ H a := by
  unfold altB4N
  have hA : ∀ b, Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      sz.STLKM n E u H σ b := fun b => QDriftA_meas_STLKM sz n E u σ b
  have hΘ : ∀ b, Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u (fun c => sz.STLKM n E u H σ c) b :=
    fun b => QDriftA_meas_ThetaN (d := d) (sz.lam n) _ u (A := fun H c => sz.STLKM n E u H σ c) hA b
  have hQ : ∀ b, Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STQop (d := d) ϑ u (fun c => sz.STLKM n E u H σ c) b :=
    fun b => QDriftA_meas_Qop (d := d) ϑ u (A := fun H c => sz.STLKM n E u H σ c) hA b
  exact (QDriftA_meas_Qop (d := d) ϑ u (A := fun H b =>
      ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u (fun c => sz.STLKM n E u H σ c) b)
      hΘ a).sub
    (QDriftA_meas_ThetaN (d := d) (sz.lam n) _ u (A := fun H b =>
      STQop (d := d) ϑ u (fun c => sz.STLKM n E u H σ c) b) hQ a)

/-- **Target 7b** (`measurable_altB5N`): `H ↦ ℬ₅(H)_a` is measurable, for every `a` (no hypothesis;
`ϑ` is fixed, so `∂_uϑ` is a constant). -/
theorem measurable_altB5N (E u : ℝ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      altB5N sz n E u ϑ σ H a := by
  unfold altB5N
  exact ((QDriftA_meas_Psum (d := d) (A := fun H c => sz.STLKM n E u H σ c)
    (fun b => QDriftA_meas_STLKM sz n E u σ b) (a 0)).mul_const _).neg

/-- **Target 7c** (`measurable_STQopDriftN`): `H ↦ (𝒬_u(Σ_l 𝒦^{(l)}∼(𝓛-𝒦) + ℰ^{LK×LK} + ℰ^{G̃}))_a` is
measurable, for every `a` (no hypothesis). -/
theorem measurable_STQopDriftN (E u : ℝ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STQop (d := d) ϑ u
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n E u H l (loopOf σ b) +
            sz.STelklkM n E u H (loopOf σ b) + sz.STegtM n E u H (loopOf σ b)) a :=
  QDriftA_meas_Qop (d := d) ϑ u (A := fun H b =>
      ∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n E u H l (loopOf σ b) +
        sz.STelklkM n E u H (loopOf σ b) + sz.STegtM n E u H (loopOf σ b))
    (fun b => ((Finset.measurable_sum _ fun l _ => QDriftA_meas_STksimLKM sz n E u l (loopOf σ b)).add
      (QDriftA_meas_STelklkM sz n E u (loopOf σ b))).add (QDriftA_meas_STegtM sz n E u (loopOf σ b))) a

/-- **Target 7d** (`measurable_dFlowQN`): `H ↦ (dFlowQN H)_a` is measurable, for every `a` (no
hypothesis). -/
theorem measurable_dFlowQN (E u : ℝ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      dFlowQN sz n E u ϑ σ H a := by
  unfold dFlowQN
  exact ((measurable_STQopDriftN sz n E u ϑ σ a).add (measurable_altB4N sz n E u ϑ σ a)).add
    (measurable_altB5N sz n E u ϑ σ a)

end Meas

/-! ## 7. Compiled nonempty instances (namespace `QDriftAInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`),
the grid data of `GridDriftNCheck` (`E ≡ 0`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`) and `QGridACheck` (`σ = (+,-,+,-)`,
`m = 3`, the merged mollifier `QopAlgebra_mollifier`).  Targets 2, 3, 4a at `n = 0` (target 3 at the non-zero
Hermitian `H = 1`); targets 4b, 4c, 5a, 5b, 6 at an `n` with `x = 2(n+1) ≥ 10` (`n = 9` for 4c, 5a, 5b;
`W_n ≥ W₀` for 4b, 6), `W = x^5`, `L = 2x`, `ε = 1/5`, `τ' = 1/10`: both windows fit in the torus, so the
decay clauses are not vacuous.  No hypothesis is left open: in the instances of target 6 the crude sup
`‖(𝓛-𝒦)_{0,σ}(0)‖ ≤ W^7` follows from `sz0.STKbound E0`, which is the proved `stKbound_holds`. -/

namespace QDriftAInst

open RBM.Gauss.SizesInst RBM.Ind.GridDriftNCheck RBM.Ind.QGridACheck

/-- A point of the path space (all coordinates `0`). -/
def ω0 : PathΩ sz0 := fun _ _ => 0

/-- The identity matrix at `sz0`, `n = 0`: Hermitian and non-zero. -/
abbrev H1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := 1

theorem H1_hermitian : H1.IsHermitian := Matrix.isHermitian_one

theorem H1_ne_zero : H1 ≠ 0 := by
  have : Nonempty (Idx 3 (sz0.L 0) (sz0.W 0)) := ⟨0⟩
  exact one_ne_zero

/-- **Instance of target 2** (`dGridQN_eq_dFlowQN`) at the `QGridACheck` data, `n = 0`, `j = 0`, `σ = (+,-,+,-)`. -/
theorem dGridQN_eq_dFlowQN_instance :
    dGridQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω0 =
      dFlowQN sz0 0 (E0 0) (gridTime s0 t0 K0 0 0) moll sigma4 (pathH sz0 s0 t0 K0 0 0 ω0) :=
  dGridQN_eq_dFlowQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω0

/-- **Instance of target 3** (`dFlowQN_sumZero`): `n = 0`, `E = 0`, `u = 1/10`, the merged mollifier, the non-zero
Hermitian `H = 1`, `σ` alternating.  Every hypothesis is discharged (`Σϑ = 1`: `QopAlgebra_mollifier_sum`;
differentiability: `QopAlgebra_mollifier_differentiableAt`).  The value of `ℬ₄`, `ℬ₅` is not computed
(it would need an explicit evaluation of `STLKM` and of `∂_uϑ`). -/
theorem dFlowQN_sumZero_instance :
    H1.IsHermitian ∧ H1 ≠ 0 ∧ STAlternating sigma4 ∧
    (∀ a₁ : Zd 3 (sz0.L 0), STPsum (d := 3) (altB4N sz0 0 0 (1 / 10) moll sigma4 H1) a₁ = 0) ∧
    (∀ a₁ : Zd 3 (sz0.L 0), STPsum (d := 3) (altB5N sz0 0 0 (1 / 10) moll sigma4 H1) a₁ = 0) ∧
    STQop (d := 3) moll (1 / 10) (altB4N sz0 0 0 (1 / 10) moll sigma4 H1) =
      altB4N sz0 0 0 (1 / 10) moll sigma4 H1 ∧
    STQop (d := 3) moll (1 / 10) (altB5N sz0 0 0 (1 / 10) moll sigma4 H1) =
      altB5N sz0 0 0 (1 / 10) moll sigma4 H1 ∧
    EKSumZero (dFlowQN sz0 0 0 (1 / 10) moll sigma4 H1) :=
  ⟨H1_hermitian, H1_ne_zero, sigma4_alternating, dFlowQN_sumZero sz0 0 0 (1 / 10) moll sigma4 H1
    (by norm_num) (by norm_num) (by norm_num)
    (fun τ a₁ => QopAlgebra_mollifier_sum 3 (sz0.L 0) 3 (sz0.lam 0) τ a₁)
    (fun a => QopAlgebra_mollifier_differentiableAt 3 (sz0.L 0) 3 (sz0.three_le_L 0) lam_pos
      (by norm_num) a)⟩

/-- **Instance of target 4a** (`aTrueQN_sumZero`) at `j = 0`, the `QGridACheck` data. -/
theorem aTrueQN_sumZero_instance : EKSumZero (aTrueQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω0) :=
  aTrueQN_sumZero sz0 E0 s0 t0 K0 0 moll sigma4 0 ω0
    (fun a₁ => QopAlgebra_mollifier_sum 3 (sz0.L 0) 3 (sz0.lam 0) _ a₁)

/-- **Instance of target 7** (measurability) at `sz0`, `n = 0`: for every label `a` the maps are measurable. -/
theorem measurable_instance (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    Measurable (fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
      altB4N sz0 0 0 (1 / 10) moll sigma4 H a) ∧
    Measurable (fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
      altB5N sz0 0 0 (1 / 10) moll sigma4 H a) ∧
    Measurable (fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
      STQop (d := 3) moll (1 / 10)
        (fun b => ∑ l ∈ Finset.Icc 3 (3 + 1), sz0.STksimLKM 0 0 (1 / 10) H l (loopOf sigma4 b) +
          sz0.STelklkM 0 0 (1 / 10) H (loopOf sigma4 b) + sz0.STegtM 0 0 (1 / 10) H (loopOf sigma4 b)) a) ∧
    Measurable (fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
      dFlowQN sz0 0 0 (1 / 10) moll sigma4 H a) :=
  ⟨measurable_altB4N sz0 0 0 (1 / 10) moll sigma4 a, measurable_altB5N sz0 0 0 (1 / 10) moll sigma4 a,
    measurable_STQopDriftN sz0 0 0 (1 / 10) moll sigma4 a, measurable_dFlowQN sz0 0 0 (1 / 10) moll sigma4 a⟩


/-! ### The data at a large `n`: `x = 2(n+1)`, `W = x^5`, `L = 2x`, `ε = 1/5`, `τ' = 1/10`

(Copies, in this namespace, of the private numeric lemmas of `QProxyInst`, `QProxy.lean:1634-1962`.) -/

private theorem rpow_pow5 {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y ^ 5) ^ r = y ^ (5 * r) := by
  rw [← Real.rpow_natCast y 5, ← Real.rpow_mul hy]; norm_num

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem mE_zero_im_ge : (1 / 2 : ℝ) ≤ (mE 0).im := by
  rw [mE_zero_im]; norm_num

private theorem etaT_zero_zero : etaT 0 0 = 1 := by
  unfold etaT
  rw [mE_zero_im]
  norm_num

private theorem etaT_zero_half : etaT 0 (1 / 2) = 1 / 2 := by
  unfold etaT
  rw [mE_zero_im]
  norm_num

private theorem sz0_facts (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 ∧
      ((sz0.L n : ℕ) : ℝ) = 2 * (2 * ((n : ℝ) + 1)) ∧
      sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := by
  refine ⟨?_, ?_, rfl⟩
  · simp [sz0]
  · simp [sz0]; ring

private theorem lam_pos_n (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

private theorem lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1)

private theorem L_ge_four (n : ℕ) : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
  have h := (sz0_facts n).2.1
  have := Nat.cast_nonneg (α := ℝ) n
  rw [h]; linarith

/-- All the numeric hypotheses of the instances at `n` with `x = 2(n+1) ≥ 10`. -/
private theorem numeric (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) :
    1 < ((sz0.W n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    Real.log ((sz0.L n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ) ∧
    ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    (3 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ∧ (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
  obtain ⟨hW, hL, hlam⟩ := sz0_facts n
  set x : ℝ := 2 * ((n : ℝ) + 1) with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxW : ((sz0.W n : ℕ) : ℝ) = x ^ 5 := hW
  have h7 : (10 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx 7
  have hW2 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
    rw [hxW]
    have : (10 : ℝ) ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
    linarith
  have hW15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hs3 : (3 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
  have hW110 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  refine ⟨by rw [hxW]; nlinarith [pow_le_pow_left₀ (by norm_num) hx 5], ?_, ?_, ?_, ?_, ?_, hW2⟩
  · rw [hW15]; linarith
  · rw [hW15, hL, Real.log_mul (by norm_num) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x by linarith)
    have h2 := Real.log_two_lt_d9
    linarith
  · rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * 2 = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hL]
    have h10 : x ^ 10 = x ^ 3 * x ^ 7 := by ring
    have h8 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h7 (pow_nonneg hx0 3)]
  · rw [hW15, hW110]
    push_cast
    nlinarith
  · rw [hW110]; exact hs3

/-- `ℓ_0 = 1` for `g ≤ 1`. -/
private theorem ellT_zero_eq (L : ℕ) (hL : 1 ≤ L) {g : ℝ} (hg : g ≤ 1) : ellT L g 0 = 1 := by
  unfold ellT
  rw [sub_zero, abs_one, Real.sqrt_one, div_one, max_eq_right hg]
  exact min_eq_left (by exact_mod_cast hL)

private theorem ellT_sz0 (n : ℕ) : ellT (sz0.L n) (sz0.lam n) 0 = 1 :=
  ellT_zero_eq _ (by have := sz0.three_le_L n; omega) (lam_le_one n)

/-- The coordinate `x = L/2 = 2(n+1)` is at distance `2(n+1)` from `0` on `Z_{4(n+1)}`. -/
private theorem zdist_far (n : ℕ) :
    zdist (sz0.L n) (((2 * (n + 1) : ℕ) : ZMod (sz0.L n))) = 2 * (n + 1) := by
  have hL : sz0.L n = 4 * (n + 1) := rfl
  have hv : (((2 * (n + 1) : ℕ) : ZMod (sz0.L n))).val = 2 * (n + 1) := by
    rw [ZMod.val_natCast, hL]
    exact Nat.mod_eq_of_lt (by omega)
  unfold zdist
  rw [hv, hL]
  omega

/-- The far point `(x, x, x)`. -/
private def farv (n : ℕ) : Zd 3 (sz0.L n) := fun _ => (((2 * (n + 1) : ℕ) : ZMod (sz0.L n)))

private theorem zdistD_farv (n : ℕ) : zdistD 3 (sz0.L n) (farv n) = 3 * (2 * (n + 1)) := by
  unfold zdistD farv
  simp only [zdist_far, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private theorem zdistInf_farv (n : ℕ) : zdistInf 3 (sz0.L n) (farv n) = 2 * (n + 1) := by
  unfold zdistInf farv
  simp only [zdist_far]
  rw [Finset.sup_const (Finset.univ_nonempty)]

/-- The far tuple `(0, x⃗, 0, 0)`. -/
private def farb (n : ℕ) : Fin (3 + 1) → Zd 3 (sz0.L n) := ![0, farv n, 0, 0]

/-- The `ℓ¹` window is attained: a tuple of `ℓ¹`-spread `3x ≥ x ≥ w ℓ_0`. -/
private theorem window_l1 (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j,
      w * ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ) := by
  refine ⟨farb n, 1, 0, ?_⟩
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistD_farv, ellT_sz0]
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The `L^∞` window is attained: `diam_∞ (farb n) ≥ x ≥ ℓ_0 w`. -/
private theorem window_linf (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b : Fin (3 + 1) → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) 0 * w ≤ (STdiamInf b : ℝ) := by
  refine ⟨farb n, ?_⟩
  have h := Finset.le_sup (f := fun q : Fin (3 + 1) × Fin (3 + 1) =>
      zdistInf 3 (sz0.L n) (farb n q.1 - farb n q.2)) (Finset.mem_univ ((1 : Fin (3 + 1)), (0 : Fin (3 + 1))))
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistInf_farv] at h
  have h2 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (STdiamInf (farb n) : ℝ) := by exact_mod_cast h
  rw [ellT_sz0]
  push_cast at h2
  linarith

private theorem diam_zero {d L k : ℕ} : STdiamInf (0 : Fin k → Zd d L) = 0 := by
  unfold STdiamInf
  refine (Finset.sup_eq_bot_iff _ _).2 fun p _ => ?_
  simp [zdistInf]

/-- `W^{x} ≤ x'` for `x ≤ 1/5`: the exponents of the instances are at most `1/5`, and `W^{1/5} = x`. -/
private theorem W_rpow_fifth (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) :
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := by
  have hx0 : 0 ≤ 2 * ((n : ℝ) + 1) := by linarith
  rw [(sz0_facts n).1, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]

/-- The delta tensor `1_{b = 0}` on `(Z_L^3)^4` (non-zero, not sum-zero, supported at spread `0`). -/
def deltaVec (n : ℕ) : (Fin (3 + 1) → Zd 3 (sz0.L n)) → ℂ := fun b => if b = 0 then 1 else 0

theorem deltaVec_ne (n : ℕ) : deltaVec n ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [deltaVec] at this

private theorem deltaVec_norm (n : ℕ) : ‖deltaVec n‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => by
    unfold deltaVec; split_ifs <;> simp

/-- `(0 ≠) b` for a tuple with a positive `ℓ¹` or `L^∞` spread. -/
private theorem deltaVec_zero_of_window (n : ℕ) {b : Fin (3 + 1) → Zd 3 (sz0.L n)} {R : ℝ} (hR : 0 < R)
    (hb : R ≤ (STdiamInf b : ℝ)) : deltaVec n b = 0 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [diam_zero, Nat.cast_zero] at hb
    linarith
  simp [deltaVec, hb0]

/-- The constants of the mollifier of `QopAlgebra_mollifier_props` at `d = 3`, `m = 3`. -/
private noncomputable abbrev Cmol3 : ℝ := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)

/-- **Instance of target 4b** (`Qop_fastDecay`): `d = 3`, `m = 3`, `K = 2`, the merged mollifier
(`C = (1 + 40·9)·6^9`, `c = 1/2`), `C₀ = 0`, `ε' = 1/5`, `D' = 1`, `t = 0`, at an `n` with `W_n ≥ W₀`; the tensor
is the non-zero delta tensor `A = 1_{b=0}` (`‖A‖ ≤ 1 = W^0`, `(t, ε', D')`-decaying: its support has spread `0`),
and the `ℓ¹` window `W^{ε'} ℓ_0` is attained by a tuple `b` (`ℓ¹`-spread `3x ≥ x`), at which the bound
`‖𝒬_0 A (b)‖ ≤ 2 W^{-1}` is the conclusion. -/
theorem Qop_fastDecay_instance :
    ∃ n : ℕ, deltaVec n ≠ 0 ∧
      EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 1 (deltaVec n) ∧
      ∃ b : Fin (3 + 1) → Zd 3 (sz0.L n),
        (∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤
          (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧
        ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (deltaVec n) b‖ ≤
          2 * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨W₀, hW₀, H⟩ := Qop_fastDecay 3 3 2 Cmol3 (1 / 2) 0 (1 / 5) 1 (by positivity) (by norm_num)
    (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_ge (max W₀ 10)
  have hx : max W₀ 10 ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hWx : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := W_rpow_fifth n hx10
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := by
    have h1 : W₀ ≤ 2 * ((n : ℝ) + 1) := (le_max_left _ _).trans hx
    have h2 : 2 * ((n : ℝ) + 1) ≤ ((sz0.W n : ℕ) : ℝ) := by
      rw [(sz0_facts n).1]
      exact le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by linarith [L_ge_four n]
  have hfast : EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 1 (deltaVec n) := by
    intro a ⟨i, j, hij⟩
    have h1 : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (ellT_pos hL1)
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hij
      linarith
    simp only [deltaVec, ha, ite_false, norm_zero]
    exact Real.rpow_nonneg (by linarith) _
  obtain ⟨b, i, j, hbij⟩ := window_l1 n (w := ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ)) hWx.le
  refine ⟨n, deltaVec_ne n, hfast, b, ⟨i, j, hbij⟩, ?_⟩
  have hnorm : ‖deltaVec n‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (0 : ℝ) := by
    rw [Real.rpow_zero]; exact deltaVec_norm n
  exact H (sz0.L n) (sz0.three_le_L n) (sz0.lam n) (lam_pos_n n) ((sz0.W n : ℕ) : ℝ) hW0W
    hLK
    (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n))
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) 0 le_rfl (by norm_num)
    (deltaVec n) hnorm hfast b ⟨i, j, hbij⟩

/-- **Instance of target 4c** (`fastDecay_of_diamInf`): the same `n`, the delta tensor (class radius `ℓ_0 W^{τ'}`,
`τ' = 1/10`, with `δ = 0`: the support has `L^∞`-spread `0`), `ε = 1/5`, `D = 1`: the `ℓ¹` decay `EKFastDecay`
follows; the `L^∞` window is attained by a tuple. -/
theorem fastDecay_of_diamInf_instance :
    ∃ n : ℕ, deltaVec n ≠ 0 ∧
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
      EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 1 (deltaVec n) := by
  have hx10 : (10 : ℝ) ≤ 2 * (((9 : ℕ) : ℝ) + 1) := by norm_num
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 9 hx10
  have hL1 : (1 : ℝ) ≤ ((sz0.L 9 : ℕ) : ℝ) := by linarith [L_ge_four 9]
  have hx : ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * (((9 : ℕ) : ℝ) + 1) := by
    have h := W_rpow_fifth 9 hx10
    have h1 : ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW.le (by norm_num)
    linarith
  refine ⟨9, deltaVec_ne 9, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := window_linf 9 (w := ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 10 : ℝ)) hx
    exact ⟨b, hb⟩
  · refine fastDecay_of_diamInf (d := 3) (by norm_num) hL1 (g := sz0.lam 9) (s := 0)
      (W := ((sz0.W 9 : ℕ) : ℝ)) (ε := 1 / 5) (τ' := 1 / 10) (D := 1) (δ := 0) hdW
      (Real.rpow_nonneg (by linarith) _) ?_
    intro b hb
    have hpos : 0 < ellT (sz0.L 9) (sz0.lam 9) 0 * ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 10 : ℝ) :=
      mul_pos (ellT_pos hL1) (Real.rpow_pos_of_pos (by linarith) _)
    rw [deltaVec_zero_of_window 9 hpos hb, norm_zero]

/-! ### Instances of targets 5a, 5b: a non-zero sum-zero tensor with a small support -/

/-- `e = (1, 1, 1)`. -/
private def ev (n : ℕ) : Zd 3 (sz0.L n) := fun _ => ((1 : ℕ) : ZMod (sz0.L n))

private theorem zdist_one (n : ℕ) : zdist (sz0.L n) ((1 : ℕ) : ZMod (sz0.L n)) = 1 := by
  have hL : sz0.L n = 4 * (n + 1) := rfl
  have hv : (((1 : ℕ) : ZMod (sz0.L n))).val = 1 := by
    rw [ZMod.val_natCast, hL]
    exact Nat.mod_eq_of_lt (by omega)
  unfold zdist
  rw [hv, hL]
  omega

private theorem ev_ne (n : ℕ) : ev n ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 : zdist (sz0.L n) ((1 : ℕ) : ZMod (sz0.L n)) = zdist (sz0.L n) 0 := by
    simp only [ev, Pi.zero_apply] at h0
    rw [h0]
  rw [zdist_one, zdist_zero] at h1
  exact absurd h1 (by norm_num)

private theorem zdistInf_ev_le (n : ℕ) : zdistInf 3 (sz0.L n) (ev n) ≤ 1 :=
  Finset.sup_le fun i _ => (zdist_one n).le

private theorem zdistInf_neg_ev_le (n : ℕ) : zdistInf 3 (sz0.L n) (-ev n) ≤ 1 := by
  refine Finset.sup_le fun i _ => ?_
  simp only [Pi.neg_apply, zdist_neg]
  exact (zdist_one n).le

/-- The second support point `(0, e, 0, 0)`. -/
private def b2 (n : ℕ) : Fin (3 + 1) → Zd 3 (sz0.L n) := fun i => if i = 1 then ev n else 0

private theorem b2_ne (n : ℕ) : b2 n ≠ 0 := by
  intro h
  have := congrFun h 1
  simp only [b2, ite_true, Pi.zero_apply] at this
  exact ev_ne n this

private theorem b2_zero (n : ℕ) : b2 n 0 = 0 := by simp [b2]

private theorem diam_b2_le (n : ℕ) : STdiamInf (b2 n) ≤ 1 := by
  refine Finset.sup_le fun p _ => ?_
  by_cases h1 : p.1 = 1 <;> by_cases h2 : p.2 = 1
  · simp [b2, h1, h2, zdistInf]
  · simpa [b2, h1, h2] using zdistInf_ev_le n
  · simpa [b2, h1, h2] using zdistInf_neg_ev_le n
  · simp [b2, h1, h2, zdistInf]

/-- The non-zero sum-zero tensor `X = 1_{b = 0} - 1_{b = (0, e, 0, 0)}` (first coordinates agree, support of
`L^∞`-spread `≤ 1`). -/
def Xsz (n : ℕ) : (Fin (3 + 1) → Zd 3 (sz0.L n)) → ℂ :=
  fun b => (if b = 0 then 1 else 0) - (if b = b2 n then 1 else 0)

theorem Xsz_sumZero (n : ℕ) : EKSumZero (Xsz n) := by
  intro i₀ hi x
  have hi0 : i₀ = 0 := Fin.ext (by simpa using hi)
  subst hi0
  unfold Xsz
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Finset.mem_filter, b2_zero]

theorem Xsz_ne (n : ℕ) : Xsz n ≠ 0 := by
  intro h
  have := congrFun h 0
  have hb : (0 : Fin (3 + 1) → Zd 3 (sz0.L n)) ≠ b2 n := fun h' => b2_ne n h'.symm
  simp [Xsz, hb] at this

private theorem Xsz_norm (n : ℕ) (b : Fin (3 + 1) → Zd 3 (sz0.L n)) : ‖Xsz n b‖ ≤ 1 := by
  have hb : (0 : Fin (3 + 1) → Zd 3 (sz0.L n)) ≠ b2 n := fun h' => b2_ne n h'.symm
  unfold Xsz
  by_cases h1 : b = 0
  · subst h1; simp [hb]
  · by_cases h2 : b = b2 n
    · subst h2; simp [h1]
    · simp [h1, h2]

private theorem Xsz_small (n : ℕ) {b : Fin (3 + 1) → Zd 3 (sz0.L n)} (hb : Xsz n b ≠ 0) :
    STdiamInf b ≤ 1 := by
  by_cases h1 : b = 0
  · subst h1; rw [diam_zero]; norm_num
  · by_cases h2 : b = b2 n
    · subst h2; exact diam_b2_le n
    · exact absurd (by simp [Xsz, h1, h2]) hb

/-- The class `altClsQN` of `X` at `δ = 0`, every `i`, radius `τ' = 1/10` (`W^{τ'} ≥ 3 > 1 ≥ diam_∞` of the
support, `ℓ ≥ 1`), for `x = 2(n+1) ≥ 10`. -/
private theorem Xsz_cls (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) (u : ℕ → ℝ) (i : ℕ) :
    altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 10) 2 u i 0 (Xsz n) := by
  obtain ⟨hW, -, -, -, -, hW3, -⟩ := numeric n hx
  refine ⟨Xsz_sumZero n, Real.rpow_nonneg (by linarith) _, fun b hb => ?_⟩
  by_contra hne
  have hne' : Xsz n b ≠ 0 := by
    intro h; apply hne; rw [h]; simp
  have hs := Xsz_small n hne'
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by linarith [L_ge_four n]
  have h1 : (1 : ℝ) ≤ ellT (sz0.L n) (sz0.lam n) (u i) := one_le_ellT hL1
  have h2 : ((STdiamInf b : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hs
  nlinarith

/-- **Instance of target 5a** (`hker_altQN`) at `d = 3`, `k = 4`, `Λ_g = 1`, `κ' = 1/2`, `K = 2`, `L = L_n`,
`g = lam_n`, `W = W_n`, `ε = 1/5`, `τ' = 1/10`, `D = 2`, `(s, t) = (0, 1/2)`, `E = 0`, **every** `σ` (so the
alternating `σ = (+,-,+,-)` and the non-alternating `σ = (+,+,+,+)`), the non-zero sum-zero tensor `X = Xsz`
(`M = 1`, `δ = 0`), at an `n` with `x = 2(n+1) ≥ 10`: every hypothesis is discharged. -/
theorem hker_altQN_instance :
    ∃ n : ℕ, Xsz n ≠ 0 ∧ (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
      ∀ (σ : Fin (3 + 1) → Bool) (a : Fin (3 + 1) → Zd 3 (sz0.L n)),
        ‖Ugen 3 (sz0.L n) (sz0.lam n) 0 σ 0 (1 / 2) (Xsz n) a‖ ≤
          ((sz0.W n : ℕ) : ℝ) ^ (qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * (1 / 5 : ℝ)) *
              (((sz0.lam n) ^ 2 + |1 - 0|) / ((sz0.lam n) ^ 2 + |1 - 1 / 2|)) ^ (3 + 1) * 1 +
            ((sz0.W n : ℕ) : ℝ) ^ qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * 0 := by
  have hx10 : (10 : ℝ) ≤ 2 * (((9 : ℕ) : ℝ) + 1) := by norm_num
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 9 hx10
  have hx : ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * (((9 : ℕ) : ℝ) + 1) := by
    have h := W_rpow_fifth 9 hx10
    have h1 : ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W 9 : ℕ) : ℝ) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW.le (by norm_num)
    linarith
  refine ⟨9, Xsz_ne 9, window_linf 9 hx, fun σ a => ?_⟩
  have hL4 := L_ge_four 9
  have hg0 := lam_pos_n 9
  have hg1 := lam_le_one 9
  refine hker_altQN (d := 3) (k := 4) 1 (1 / 2) 2 (by norm_num) (by norm_num) one_pos (by norm_num)
    (by norm_num) (sz0.three_le_L 9) hg0 hg1 hW (by norm_num) (by norm_num) hWε hlog hLK hdW
    (D := 2) (by norm_num) (s := 0) (t := 1 / 2) le_rfl (by norm_num) ?_ ?_ (E := 0) (by norm_num)
    mE_zero_im_ge σ (Xsz 9) (M := 1) (δ := 0) zero_le_one le_rfl (Real.rpow_nonneg (by linarith) _)
    (Xsz_norm 9) (Xsz_sumZero 9) ?_ a
  · have : ((sz0.lam 9) ^ 2) / ((sz0.L 9 : ℕ) : ℝ) ^ 2 ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (sz0.lam 9)]
    linarith
  · calc (((sz0.W 9 : ℕ) : ℝ))⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hW2
      _ = (1 - 1 / 2) / (1 - 0) := by norm_num
  · intro b hb
    have := (Xsz_cls 9 hx10 (fun _ => 0) 0).2.2 b hb
    simpa using this

/-- **Instance of target 5b** (`alt_hkerQN`, the field `hker` of `GridAssemblyHypN`) at the same data, on the grid
`u_i = i/2`, `K = 1` (`u_0 = 0`, `u_1 = 1/2`), every `σ`, every `i ≤ m ≤ 1`, the class `altClsQN` of `Xsz` at
`δ = 0` and `M = 1`. -/
theorem alt_hkerQN_instance :
    ∃ n : ℕ, Xsz n ≠ 0 ∧ ∀ (σ : Fin (3 + 1) → Bool) (i m : ℕ), i ≤ m → m ≤ 1 →
      ∀ a : Fin (3 + 1) → Zd 3 (sz0.L n),
        ‖Ugen 3 (sz0.L n) (sz0.lam n) 0 σ ((fun j : ℕ => (j : ℝ) / 2) i) ((fun j : ℕ => (j : ℝ) / 2) m)
            (Xsz n) a‖ ≤
          kappaAltQN 3 (3 + 1) 1 (1 / 2) 2 (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5)
              (fun j : ℕ => (j : ℝ) / 2) i m * 1 +
            epsAltQN 3 (3 + 1) 1 (1 / 2) 2 ((sz0.W n : ℕ) : ℝ) i m * 0 := by
  have hx10 : (10 : ℝ) ≤ 2 * (((9 : ℕ) : ℝ) + 1) := by norm_num
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 9 hx10
  refine ⟨9, Xsz_ne 9, fun σ i m him hm1 a => ?_⟩
  have hL4 := L_ge_four 9
  have hg0 := lam_pos_n 9
  have hg1 := lam_le_one 9
  refine alt_hkerQN (d := 3) (k := 4) 1 (1 / 2) 2 (by norm_num) (by norm_num) one_pos (by norm_num)
    (by norm_num) (sz0.three_le_L 9) hg0 hg1 hW (by norm_num) (by norm_num) hWε hlog hLK hdW
    (Dc := 2) (by norm_num) (Kg := 1) (u := fun j : ℕ => (j : ℝ) / 2) (fun i _ => by positivity)
    (fun i m him _ => by
      have : (i : ℝ) ≤ m := by exact_mod_cast him
      linarith) ?_ ?_ (E := 0) (by norm_num) mE_zero_im_ge σ i m him hm1 (Xsz 9) 1 0 zero_le_one le_rfl
    (Xsz_norm 9) (Xsz_cls 9 hx10 _ i) a
  · have : ((sz0.lam 9) ^ 2) / ((sz0.L 9 : ℕ) : ℝ) ^ 2 ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (sz0.lam 9)]
    norm_num
    linarith
  · calc (((sz0.W 9 : ℕ) : ℝ))⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hW2
      _ = (1 - ((1 : ℕ) : ℝ) / 2) / (1 - ((0 : ℕ) : ℝ) / 2) := by norm_num

/-- The two sign vectors of the instances: `σ = (+,-,+,-)` is alternating, `σ = (+,+,+,+)` is not. -/
theorem sigma_alt_and_nonalt :
    STAlternating sigma4 ∧ ¬ STAlternating (fun _ : Fin (3 + 1) => true) := by
  refine ⟨sigma4_alternating, fun h => ?_⟩
  have := h 0
  simp at this



/-! ### Instance of target 6: the initial-term class at `M = 0 ∈ GoodSetN`, eventually in `n` -/

/-- `0 ∈ GoodSetN` at `E = 0`, `u = 0`, `k = 4` with the levels `(Γ, Λ, Φ) = (4, 100, 1)`
(`Γ² Λ = 1600 ≥ 4 · 2^8`), every `τ'`, `D'`. -/
private theorem zero_mem_inst (n : ℕ) (hlam1 : sz0.lam n ≤ 1) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 τ' D' := by
  refine zero_mem_goodSetN_of_levels sz0 n (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  have h1 : (1 + sz0.lam n ^ 2) ≤ 2 := by nlinarith [sq_nonneg (sz0.lam n), lam_pos_n n]
  have h2 : (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 2 ^ (2 * (3 + 1)) :=
    pow_le_pow_left₀ (by positivity) h1 _
  push_cast
  calc 4 * (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 4 * 2 ^ (2 * (3 + 1)) := by gcongr
    _ ≤ 4 * (4 * 100) := by norm_num

/-- **The crude sup** `‖(𝓛-𝒦)_{0,σ}(0)‖ ≤ W^7` at `E = 0`, `u = 0`, `M = 0`, `k = 4`, from the eventual bound of
`exists_norm_Kcal_le_win` on `𝒦` and `norm_loopFine_crudeN` (`≤ 1 + 16 N ≤ 1 + 16 W^6`, `N = (W L)^3 ≤ W^6`,
`W ≥ 17`). -/
private theorem crude_sup (n : ℕ) (hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ))
    (hn1 : ∀ w ∈ Set.Icc (0 : ℝ) ((fun _ : ℕ => (1 / 2 : ℝ)) n), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
      2 ≤ J.length → J.length ≤ 4 →
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹) ^ 4)
    (σ : Fin (3 + 1) → Bool) :
    ‖fun a => sz0.STLKM n 0 0 0 σ a‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
  have hWpos : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  have e : sz0.STLKM n 0 0 0 σ a =
      loopFine 3 (sz0.L n) (sz0.W n) (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n))
        (Idx 3 (sz0.L n) (sz0.W n)) ℂ) (zt 0 0) σ a - sz0.STKloop n 0 0 σ a := rfl
  rw [e]
  have h1 := norm_loopFine_crudeN sz0 n (E := 0) (by norm_num) Matrix.isHermitian_zero (u := 0)
    (by norm_num) (ℓ := 4) (by norm_num) σ a
  rw [etaT_zero_zero, inv_one, one_pow] at h1
  have hJ : sz0.STKloop n 0 0 σ a = KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) 0 (loopOf σ a) := rfl
  have h2 := hn1 0 ⟨le_rfl, by norm_num⟩ (loopOf σ a) (by simp [LoopIdx.WF, loopOf])
    (by simp [LoopIdx.length, loopOf]) (by simp [LoopIdx.length, loopOf])
  have hη : etaT (E0 n) 0 = 1 := etaT_zero_zero
  have hη' : etaT (E0 n) (1 / 2) = 1 / 2 := etaT_zero_half
  simp only [hη', Real.rpow_one] at h2
  have hsize : ((sz0.size n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by exact_mod_cast sz0_size_le_W_pow n
  rw [hJ]
  have h3 : ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) 0 (loopOf σ a)‖ ≤
      16 * ((sz0.W n : ℕ) : ℝ) ^ 6 := by
    refine h2.trans ?_
    have : ((1 / 2 : ℝ)⁻¹) ^ 4 = 16 := by norm_num
    rw [this]
    nlinarith [hsize]
  have h4 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h4]
  have h5 : (17 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ 6 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    have : ((sz0.W n : ℕ) : ℝ) ^ 7 = ((sz0.W n : ℕ) : ℝ) ^ 6 * ((sz0.W n : ℕ) : ℝ) := by ring
    rw [this]
    nlinarith [pow_pos hWpos 6]
  have h6 : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := one_le_pow₀ (by linarith)
  calc _ ≤ ‖loopFine 3 (sz0.L n) (sz0.W n) (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n))
        (Idx 3 (sz0.L n) (sz0.W n)) ℂ) (zt 0 0) σ a‖ +
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) 0 (loopOf σ a)‖ := norm_sub_le _ _
    _ ≤ 1 + 16 * ((sz0.W n : ℕ) : ℝ) ^ 6 := add_le_add h1 h3
    _ ≤ _ := by linarith

/-- **Instance of target 6a** (`goodSetN_A0clsQN`) at `sz0`, `d = 3`, `m = 3` (`k = 4`), `K = 2`, the merged
mollifier (`C = (1 + 40·9)·6^9`, `c = 1/2`), `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `D' = 3`, `Dc = 2`, `E = 0`,
`u_i = 0`, `M = 0 ∈ GoodSetN` with the levels `(4, 100, 1)`, every `σ`, at an `n` with `W_n ≥ W₀` (the threshold
of `Qop_fastDecay`).  The crude sup `‖(𝓛-𝒦)_{0,σ}(0)‖ ≤ W^7` is derived from `exists_norm_Kcal_le_win` and
`norm_loopFine_crudeN` (`≤ 1 + 16 N ≤ 1 + 16 W^6`, `N = (W L)^3 ≤ W^6`), with `sz0.STKbound E0` from the proved
`stKbound_holds` (`Loop/KLFinal.lean:243`, `κ = 1`, `gmax = 10`): no hypothesis is left open.  The `L^∞` window
`ℓ_0 W^{ε'}` is attained by a tuple. -/
theorem goodSetN_A0clsQN_instance :
    ∃ n : ℕ,
      (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
        sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) 3 ∧
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
      ∀ σ : Fin (3 + 1) → Bool,
        altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 2 (fun _ => 0) 0
          (2 * ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)))
          (STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0
            (fun a => sz0.STLKM n 0 0 0 σ a)) := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  set W₀ : ℝ := QDriftA_W0 3 3 2 Cmol3 (1 / 2) 7 (1 / 5) 3 with hW₀def
  have hKev := exists_norm_Kcal_le_win sz0 sz0_tendsto E0 hKb (fun _ => by norm_num)
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) 4 1 one_pos
  obtain ⟨n, hn1, hn2⟩ := (hKev.and (Filter.eventually_ge_atTop ⌈max W₀ 17⌉₊)).exists
  have hn : max W₀ 17 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  have hx : max W₀ 17 ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW : 2 * ((n : ℝ) + 1) ≤ ((sz0.W n : ℕ) : ℝ) := by
    rw [(sz0_facts n).1]
    exact le_self_pow₀ (by linarith) (by norm_num)
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hWx : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := W_rpow_fifth n hx10
  have hWpos : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith
  have hlam1 := lam_le_one n
  have hcrude := crude_sup n hW17 hn1
  have hDD : 2 * ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    have h : ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) =
        ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hWpos]; norm_num
    rw [h, Real.rpow_neg_one]
    have h1 : 2 * ((sz0.W n : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hWpos]; linarith
    have h2 : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hWpos.le _
    calc 2 * (((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((sz0.W n : ℕ) : ℝ)⁻¹)
        = (2 * ((sz0.W n : ℕ) : ℝ)⁻¹) * ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := by ring
      _ ≤ 1 * ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := by gcongr
      _ = _ := one_mul _
  refine ⟨n, zero_mem_inst n hlam1 _ _, ?_, fun σ => ?_⟩
  · obtain ⟨b, hb⟩ := window_linf n (w := ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ)) hWx.le
    exact ⟨b, hb⟩
  · exact goodSetN_A0clsQN sz0 (le_refl 3) 3 2 Cmol3 (1 / 2) 7 (1 / 5) 3 (by positivity)
      (by norm_num) (by norm_num) (n := n) (E := 0) (Γ := 4) (Λ := 100) (Φ := 1) (τ' := 1 / 10)
      (Dc := 2) (u := fun _ => 0) (i := 0) hW0W hLK hdW hDD (lam_pos_n n) le_rfl (by norm_num)
      (zero_mem_inst n hlam1 _ _) (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n))
      (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) σ (hcrude σ)

/-- **Instance of target 6b** (`alt_hA0clsQN`) on the walk with `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4` (so `H_0 = 0`,
`u_0 = 0`), `n` large, the stopping time `τ ≡ 1` (`0 < τ`, and `H_0 ∈ GoodSetN` for `j < τ`), levels `(4, 100, 1)`,
the merged mollifier, `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `D' = 3`, `Dc = 2`, every `σ` and every path `ω`: the
`𝒬`-process `A^Q_0 = aTrueQN … 0 ω` is in the class `altClsQN … 0` (the same data and the same proof of the crude
sup as `goodSetN_A0clsQN_instance`; no hypothesis is left open). -/
theorem alt_hA0clsQN_instance :
    ∃ n : ℕ, ∀ (σ : Fin (3 + 1) → Bool) (ω : PathΩ sz0), 0 < (fun _ : PathΩ sz0 => 1) ω →
      altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 2
        (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n) 0
        (2 * ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)))
        (aTrueQN sz0 E0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n
          (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ 0 ω) := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  set W₀ : ℝ := QDriftA_W0 3 3 2 Cmol3 (1 / 2) 7 (1 / 5) 3 with hW₀def
  have hKev := exists_norm_Kcal_le_win sz0 sz0_tendsto E0 hKb (fun _ => by norm_num)
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) 4 1 one_pos
  obtain ⟨n, hn1, hn2⟩ := (hKev.and (Filter.eventually_ge_atTop ⌈max W₀ 17⌉₊)).exists
  have hn : max W₀ 17 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  have hx : max W₀ 17 ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW : 2 * ((n : ℝ) + 1) ≤ ((sz0.W n : ℕ) : ℝ) := by
    rw [(sz0_facts n).1]
    exact le_self_pow₀ (by linarith) (by norm_num)
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hWpos : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith
  have hlam1 := lam_le_one n
  have hDD : 2 * ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    have h : ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) =
        ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hWpos]; norm_num
    rw [h, Real.rpow_neg_one]
    have h1 : 2 * ((sz0.W n : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hWpos]; linarith
    have h2 : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hWpos.le _
    calc 2 * (((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((sz0.W n : ℕ) : ℝ)⁻¹)
        = (2 * ((sz0.W n : ℕ) : ℝ)⁻¹) * ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := by ring
      _ ≤ 1 * ((sz0.W n : ℕ) : ℝ) ^ (-(2 : ℝ)) := by gcongr
      _ = _ := one_mul _
  refine ⟨n, fun σ ω hω => ?_⟩
  have hp0 : pathH sz0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n 0 ω = 0 :=
    azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ n rfl ω
  refine alt_hA0clsQN sz0 (le_refl 3) 3 2 Cmol3 (1 / 2) 7 (1 / 5) 3 (by positivity) (by norm_num)
    (by norm_num) (n := n) σ E0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) (fun _ => 4)
    (fun _ => 100) (fun _ => 1) (1 / 10) 2 (fun _ => 1)
    (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) hW0W hLK hdW hDD (lam_pos_n n) le_rfl
    (by norm_num)
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) ?_ ?_ ω hω
  · intro ω' j hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ n rfl ω', ST_gridTime_zero]
    exact zero_mem_inst n hlam1 _ _
  · intro ω' _
    have e : AvecN sz0 E0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n 0 σ ω' =
        fun a => sz0.STLKM n 0 0 0 σ a := by
      funext a
      simp only [AvecN]
      rw [ST_gridTime_zero, azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ n rfl ω']
    rw [e]
    exact crude_sup n hW17 hn1 σ

end QDriftAInst

end RBM.Ind

end
