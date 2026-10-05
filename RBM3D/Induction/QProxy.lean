/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QGridA
import RBM3D.Induction.QopNorm
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Induction.NQGood2
import RBM3D.Evolution.SumDecayZero

/-!
# The martingale part of the `𝒬`-process at `d ≥ 3` (stochastic layer ST-3, S3-14)

Ticket T2194 (with its amend 1).  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`
(`3_5:line`): `Def:QtPt` (`3_5:1204`), `lem_+Q` (`3_5:1284-1289`), `int_K-L+Q` (`3_5:1337-1346`,
last term), `(eq:alternatecase1)` (`3_5:1687`), `lem:sum_decay` (`3_5:1629-1665`).  Port of RBM2D
`Induction/AltProxyQ.lean` at `c9a24cf` (cited `AltProxyQ:<line>`), re-derived for `d ≥ 3`: tensors
of `m + 1` indices on `Zd d L`, the merged `STQop` with an abstract mollifier family `ϑ`
(`‖ϑ‖ ≤ C (ℓ_t^d)^{-m} e^{-c S/ℓ_t}`, not `≤ 1`), the pair kernel from EK-4 instead of Case 5 of
the `d = 2` evolution kernel.  **Every statement is generic in the stopping time / set family
(`τ`, `G`) and in the mollifier family `ϑ`; none carries a level of the current length**
(DECISIONS §62 (4)): the only level that occurs is the (D4) level `Γ(ΓΛ)B_u^{2k}/η_u` of `GoodSetN`.

## What is here (namespace `RBM.Ind`)

* §1 the vocabulary `qqTensorN` (`(𝒬_t ⊗ 𝒬̄_t)𝒜`), `qvFormQN`, `zVecQN`, `yVecQN` (the check
  file §2, verbatim).
* §2-§4 linearity of `STQop` and the transposed weights `κ'_c = κ_c - Σ_{b : b₀ = c₀} κ_b ϑ_u(b)`
  (private `qProxy_wts`, `qProxy_sum_Qop`, `qProxy_sum_qq`); **`martIncQN_ae_eq`**
  (`martIncQN = zVecQN + yVecQN` a.e.); **`qv_at_propagatorQ`** (the merged `qvPropagatedN` at
  `κ'`); **`qqTensorN_sumZero`** (`𝒫 ∘ 𝒬_t = 0` in each copy, `EKSumZero`).
* §5 **`azumaSubGQ_ugenN`** and **`azumaSubGQ_gridExitN`**: the sub-Gaussian input of the
  `𝒬`-process for ANY stopping family `τ` with sets `G`, and at the exit time of ANY measurable
  family `G` (RBM2D `azumaSubGQ_goodExit`, which hard-wires `goodExitTauN` at one level `Φ`, is
  not ported: paper-delta `T2194a`).
* §6 the constants `qProxyCn` (`C_n` of `lem_+Q`), `qProxyCQ = 2 C_n + 2`, `qProxy4C` (`C₄` of
  EK-4), `qProxyW0` (the threshold `W₀` of the decay clause of `lem_+Q`), extracted once as
  `nqGood1C`.
* §7 **`qqTensorBoundsN`**, the two-copy `lem_+Q` (new mathematics): `‖(𝒬⊗𝒬̄)T‖_∞ ≤ W^{2C_nε} M_ee +
  W^{-D+C_Q}`, the slice decay in `b'` at `D - C_Q`, the block decay in `b` at `W^{-D+C_Q}` (the
  factor `(2 + M_ee)` of the ticket is not needed, `T2194c`).  No concatenated window: inner copy
  slice by slice, a spread block makes the whole slice small.
* §8 **`ugenPairQN_le_of_bounds`**: the pair kernel `(𝒰_σ ⊗ 𝒰_σ̄) ∘ T` from EK-4
  (`ekSumDecay2_holds`) for every `σ` (`T2194b`): stage 1 on the `b'`-block, stage 2 on the
  `b`-block, far level `W^k δ'`.
* §9 **`qvFormQN_le_of_bounds`**, **`qvFormQN_le_of_goodSetN`**: the closed-form majorant
  `κ₄(κ₄ M_Q + W^{C₄} δ_Q) + W^{C₄} W^k δ_Q`, `M_Q = W^{2C_nε} M_ee + W^{-D+C_Q}`,
  `δ_Q = W^{-D+C_Q}`, `κ₄ = W^{C₄ε} r_{u,w}^k`; in 6b `M_ee = Γ(ΓΛ)B_u^{2k}/η_u` and `δ = W^{-D}`
  from clauses (D4), (Vb); `Φ` is free.
* §10 **`yMomentsQUnifN`**: the uniform `Y` moments of `yVecQN`,
  `C_P = 11 + (4(m+1)+4) max 0 (1-τ') + 2m + 2` (`T2194d`; needs `0 ≤ c`, amend 1); the body is
  the private `qProxy_yMomentsQPos` with `P > 0`.
* §11 compiled nonempty instances (namespace `QProxyInst`).

Every unpinned helper is `private` or prefixed `qProxy` / `QProxy`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Green

/-! ## 1. The vocabulary (target 1; the check file §2, verbatim) -/

/-- `(𝒬_t ⊗ 𝒬̄_t) 𝒜 = Σ_{c,c'} Qmat_t(b,c) conj(Qmat_t(b',c')) 𝒜(c,c')` (RBM2D `qqTensorN`, `AltProxyQ:93`),
for the merged `STQop` with an abstract mollifier family `ϑ`, tensors of `m + 1` indices. -/
def qqTensorN {d L m : ℕ} [NeZero L] (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (A : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ) (b b' : Fin (m + 1) → Zd d L) : ℂ :=
  STQop (d := d) ϑ t
    (fun c => starRingEnd ℂ (STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) b')) b

/-- The merged `qvFormN` (`GridAssemblyN.lean:105`) with `𝓔 ⊗ 𝓔` (`STeeM`) replaced by
`(𝒬_v ⊗ 𝒬̄_v)(𝓔 ⊗ 𝓔)` (RBM2D `qvFormQN`, `AltProxyQ:98`). -/
noncomputable def qvFormQN {d : ℕ} (sz : Sizes d) (n : ℕ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (E v w : ℝ) (σ : Fin (m + 1) → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)) : ℝ :=
  (∑ b : Fin (m + 1) → Zd d (sz.L n), ∑ b' : Fin (m + 1) → Zd d (sz.L n),
    (∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) v w
        (a i) (b i)) *
      (starRingEnd ℂ) (∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n)
        (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b' i)) *
      qqTensorN ϑ v (fun c c' => sz.STeeM n E v M σ c c') b b').re

/-- The first-chaos part of the `𝒬`-martingale increment, `𝒬_{u_{j+1}} ZvecN` (RBM2D `zVecQN`, `AltProxyQ:107`). -/
noncomputable def zVecQN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n (j + 1)) (ZvecN sz E s t K n j σ ω)

/-- The second-order part, `𝒬_{u_{j+1}} YvecN` (RBM2D `yVecQN`, `AltProxyQ:112`). -/
noncomputable def yVecQN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n (j + 1)) (YvecN sz E s t K n j σ ω)

/-! ## 2. Linearity of `𝒬_t` and the transposed weights (RBM2D `AltProxyQ:122-213`) -/

section QopAlg

variable {d L m : ℕ} [NeZero L]

private theorem qProxy_Qop_finset_sum {ι : Type*} (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (s : Finset ι) (F : ι → (Fin (m + 1) → Zd d L) → ℂ) (a : Fin (m + 1) → Zd d L) :
    STQop (d := d) ϑ t (fun c => ∑ i ∈ s, F i c) a = ∑ i ∈ s, STQop (d := d) ϑ t (F i) a := by
  unfold STQop STPsum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_comm]

private theorem qProxy_Qop_sub (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (A B : (Fin (m + 1) → Zd d L) → ℂ) (a : Fin (m + 1) → Zd d L) :
    STQop (d := d) ϑ t (fun c => A c - B c) a = STQop (d := d) ϑ t A a - STQop (d := d) ϑ t B a := by
  unfold STQop STPsum
  rw [Finset.sum_sub_distrib]
  ring

private theorem qProxy_Qop_add (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (A B : (Fin (m + 1) → Zd d L) → ℂ) (a : Fin (m + 1) → Zd d L) :
    STQop (d := d) ϑ t (fun c => A c + B c) a = STQop (d := d) ϑ t A a + STQop (d := d) ϑ t B a := by
  unfold STQop STPsum
  rw [Finset.sum_add_distrib]
  ring

private theorem qProxy_Qop_zero (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (a : Fin (m + 1) → Zd d L) :
    STQop (d := d) ϑ t (fun _ => (0 : ℂ)) a = 0 := by
  simp [STQop, STPsum]

/-- The transposed weights: `Σ_b κ_b (𝒬_t F)_b = Σ_c κ'_c F_c` with
`κ'_c = κ_c - Σ_{b : b₀ = c₀} κ_b ϑ_{t,b}` (i.e. `κ'_c = Σ_b κ_b Qmat_t(b, c)`). -/
private def qProxy_wts (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (κ : (Fin (m + 1) → Zd d L) → ℂ) (c : Fin (m + 1) → Zd d L) : ℂ :=
  κ c - ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c 0), κ b * ϑ t b

private theorem qProxy_sum_Qop (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (κ F : (Fin (m + 1) → Zd d L) → ℂ) :
    ∑ b, κ b * STQop (d := d) ϑ t F b = ∑ c, qProxy_wts ϑ t κ c * F c := by
  have key : ∑ b : Fin (m + 1) → Zd d L, κ b * (STPsum (d := d) F (b 0) * ϑ t b) =
      ∑ c : Fin (m + 1) → Zd d L,
        (∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c 0), κ b * ϑ t b) * F c := by
    have h1 : ∀ b : Fin (m + 1) → Zd d L, κ b * (STPsum (d := d) F (b 0) * ϑ t b) =
        ∑ c : Fin (m + 1) → Zd d L, if c 0 = b 0 then κ b * ϑ t b * F c else 0 := by
      intro b
      unfold STPsum
      rw [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> ring
    have h2 : ∀ c : Fin (m + 1) → Zd d L,
        (∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c 0), κ b * ϑ t b) * F c =
        ∑ b : Fin (m + 1) → Zd d L, if c 0 = b 0 then κ b * ϑ t b * F c else 0 := by
      intro c
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    simp only [h1, h2]
    exact Finset.sum_comm
  unfold STQop qProxy_wts
  simp only [mul_sub, Finset.sum_sub_distrib, sub_mul]
  rw [key]

/-- The double form: `Σ_{b,b'} κ_b conj(κ_{b'}) (𝒬⊗𝒬̄ 𝒜)_{b,b'} = Σ_{c,c'} κ'_c conj(κ'_{c'}) 𝒜_{c,c'}`. -/
private theorem qProxy_sum_qq (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (κ : (Fin (m + 1) → Zd d L) → ℂ)
    (A : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ) :
    ∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * qqTensorN ϑ t A b b' =
      ∑ c, ∑ c', qProxy_wts ϑ t κ c * starRingEnd ℂ (qProxy_wts ϑ t κ c') * A c c' := by
  have h1 : ∀ b' : Fin (m + 1) → Zd d L, ∑ b, κ b * qqTensorN ϑ t A b b' =
      ∑ c, qProxy_wts ϑ t κ c *
        starRingEnd ℂ (STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) b') := fun b' =>
    qProxy_sum_Qop ϑ t κ _
  have h2 : ∀ c : Fin (m + 1) → Zd d L,
      ∑ b', κ b' * STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) b' =
      ∑ c', qProxy_wts ϑ t κ c' * starRingEnd ℂ (A c c') := fun c =>
    qProxy_sum_Qop ϑ t κ _
  calc ∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * qqTensorN ϑ t A b b'
      = ∑ b', starRingEnd ℂ (κ b') * ∑ b, κ b * qqTensorN ϑ t A b b' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ b', starRingEnd ℂ (κ b') * ∑ c, qProxy_wts ϑ t κ c *
          starRingEnd ℂ (STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) b') := by
        simp only [h1]
    _ = ∑ c, qProxy_wts ϑ t κ c * starRingEnd ℂ
          (∑ b', κ b' * STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) b') := by
        simp only [Finset.mul_sum, map_sum, map_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c => ?_
        intro _
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring
    _ = ∑ c, ∑ c', qProxy_wts ϑ t κ c * starRingEnd ℂ (qProxy_wts ϑ t κ c') * A c c' := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [h2 c, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [map_mul, Complex.conj_conj]
        ring

end QopAlg

/-! ## 3. Target 2: `martIncQN = zVecQN + yVecQN` -/

/-- **Target 2 (`martIncQN_ae_eq`)**: a.e., the martingale increment of the `𝒬`-process is `𝒬_{u_{j+1}}` of
the first-chaos part plus `𝒬_{u_{j+1}}` of the remainder, `martIncQN_j = zVecQN_j + yVecQN_j` (any `ϑ`).
Proof: `QGridA_condExp_aTrueQN` (`𝔼[·|F_j]` commutes with `𝒬_{u_{j+1}}`), linearity of `STQop`, and
`YvecN = martIncN - ZvecN`.  RBM2D `martIncQN_ae_eq` (`AltProxyQ:227`). -/
theorem martIncQN_ae_eq {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hj1 : gridTime s t K n (j + 1) < 1) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∀ᵐ ω ∂(pathP sz), martIncQN sz E s t K n ϑ σ j ω a =
      zVecQN sz E s t K n j ϑ σ ω a + yVecQN sz E s t K n j ϑ σ ω a := by
  filter_upwards [QGridA_condExp_aTrueQN sz E s t K n j hE hj1 ϑ σ a] with ω h
  have h1 : (fun c => ZvecN sz E s t K n j σ ω c + YvecN sz E s t K n j σ ω c) =
      fun c => AvecN sz E s t K n (j + 1) σ ω c -
        (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' c | filt sz j] ω := by
    funext c
    simp only [YvecN, martIncN]
    ring
  have h2 := qProxy_Qop_add ϑ (gridTime s t K n (j + 1)) (ZvecN sz E s t K n j σ ω)
    (YvecN sz E s t K n j σ ω) a
  have h3 := qProxy_Qop_sub ϑ (gridTime s t K n (j + 1)) (AvecN sz E s t K n (j + 1) σ ω)
    (fun c => (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' c | filt sz j] ω) a
  unfold zVecQN yVecQN
  rw [← h2, h1, h3]
  unfold martIncQN
  rw [h]
  rfl

/-! ## 4. Target 3: the variance identity of the propagated `𝒬`-family, and `𝒫 ∘ 𝒬_t = 0` in each copy -/

/-- The variance identity for an arbitrary weight vector `κ` (RBM2D `AltProxyQ_qv_aux`, `AltProxyQ:258`). -/
private theorem qProxy_qv_aux {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    {m : ℕ} (hm : 1 ≤ m) (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (κ : (Fin (m + 1) → Zd d (sz.L n)) → ℂ) :
    ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
        ‖∑ b : Fin (m + 1) → Zd d (sz.L n), κ b *
          STQop (d := d) ϑ u (fun b'' => loopDerivN d (sz.L n) (sz.W n) E u M
            (coordinateMatrix d (sz.L n) (sz.W n) c) σ b'') b‖ ^ 2 ≤
      ((m + 1 : ℕ) : ℝ) * (∑ b : Fin (m + 1) → Zd d (sz.L n), ∑ b' : Fin (m + 1) → Zd d (sz.L n),
        κ b * (starRingEnd ℂ) (κ b') * qqTensorN ϑ u (fun c c' => sz.STeeM n E u M σ c c') b b').re := by
  have h := qvPropagatedN d sz n E hE u hu0 hu1 M hM (m + 1) (by omega) σ (qProxy_wts ϑ u κ)
  have hLHS : ∀ c : CoordF d (sz.L n) (sz.W n), ∑ b : Fin (m + 1) → Zd d (sz.L n), κ b *
      STQop (d := d) ϑ u (fun b'' => loopDerivN d (sz.L n) (sz.W n) E u M
        (coordinateMatrix d (sz.L n) (sz.W n) c) σ b'') b =
      ∑ b : Fin (m + 1) → Zd d (sz.L n), qProxy_wts ϑ u κ b *
        loopDerivN d (sz.L n) (sz.W n) E u M (coordinateMatrix d (sz.L n) (sz.W n) c) σ b :=
    fun c => qProxy_sum_Qop ϑ u κ _
  rw [qProxy_sum_qq]
  simp only [hLHS]
  exact h

/-- **Target 3a (`qv_at_propagatorQ`)**: the merged `qvPropagatedN` at the transposed weights
`κ'_c = Σ_b κ_b Qmat_u(b, c)` of `𝒬_u`: `Σ_c gvar_c ‖Σ_b κ_b (𝒬_u ∂_c 𝓛)_b‖² ≤ (m+1) · qvFormQN` (any `ϑ`,
any `w`).  RBM2D `qv_at_propagatorQ` (`AltProxyQ:281`). -/
theorem qv_at_propagatorQ {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (hE : |E| < 2) (u w : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
        ‖∑ b : Fin (m + 1) → Zd d (sz.L n),
          (∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) u w
            (a i) (b i)) *
          STQop (d := d) ϑ u (fun b'' => loopDerivN d (sz.L n) (sz.W n) E u M
            (coordinateMatrix d (sz.L n) (sz.W n) c) σ b'') b‖ ^ 2 ≤
      ((m + 1 : ℕ) : ℝ) * qvFormQN sz n ϑ E u w σ M a :=
  qProxy_qv_aux sz n E hE u hu0 hu1 M hM hm ϑ σ
    (fun b => ∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) u w
      (a i) (b i))

/-- **Target 3b (`qqTensorN_sumZero`)**: `(𝒬_t ⊗ 𝒬̄_t) 𝒜` is sum-zero in each block (`𝒫 ∘ 𝒬_t = 0`,
`QopAlgebra_Psum_Qop`, in each copy; linearity of `STQop` and of complex conjugation for the second
block), for every `𝒜`, given `Σ_{a₂..a_n} ϑ_{t,a} = 1`; RBM2D `doubleSumZero_qqTensorN` (`AltProxyQ:303`) in
the form EK-4 consumes (`EKSumZero`). -/
theorem qqTensorN_sumZero {d L m : ℕ} [NeZero L] (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (hϑ : ∀ a₁ : Zd d L,
      ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ t a = 1)
    (A : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ) :
    (∀ b' : Fin (m + 1) → Zd d L, EKSumZero (fun b => qqTensorN ϑ t A b b')) ∧
      (∀ b : Fin (m + 1) → Zd d L, EKSumZero (fun b' => qqTensorN ϑ t A b b')) := by
  have hi0 : ∀ i₀ : Fin (m + 1), i₀.val = 0 → i₀ = 0 := fun i₀ h => Fin.ext (by simpa using h)
  refine ⟨fun b' i₀ hi x => ?_, fun b i₀ hi x => ?_⟩
  · rw [hi0 i₀ hi]
    exact QopAlgebra_Psum_Qop (d := d) ϑ hϑ
      (fun c => starRingEnd ℂ (STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) b')) x
  · rw [hi0 i₀ hi]
    set F : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ := fun a' c =>
      starRingEnd ℂ (STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (A c c')) a') with hF
    have h0 : ∀ c : Fin (m + 1) → Zd d L,
        ∑ a' ∈ Finset.univ.filter (fun a' : Fin (m + 1) → Zd d L => a' 0 = x), F a' c = 0 := by
      intro c
      simp only [hF]
      rw [← map_sum]
      have h := QopAlgebra_Psum_Qop (d := d) ϑ hϑ (fun c' => starRingEnd ℂ (A c c')) x
      unfold STPsum at h
      rw [h, map_zero]
    have h1 := qProxy_Qop_finset_sum ϑ t
      (Finset.univ.filter (fun a' : Fin (m + 1) → Zd d L => a' 0 = x)) F b
    have h2 : (fun c => ∑ a' ∈ Finset.univ.filter (fun a' : Fin (m + 1) → Zd d L => a' 0 = x),
        F a' c) = fun _ => (0 : ℂ) := funext h0
    rw [h2, qProxy_Qop_zero] at h1
    exact h1.symm


/-! ## 5. Target 7: the sub-Gaussian input for the first-chaos part of the `𝒬`-increment -/

section GridArith

private theorem qProxy_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem qProxy_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ : 0 ≤ gridStep s t K n := qProxy_gridStep_nonneg hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) * gridStep s t K n := mul_nonneg (Nat.cast_nonneg _) hΔ
  linarith

/-- `u_j ≤ t n` for `j ≤ K n` (`K n ≠ 0`). -/
private theorem qProxy_gridTime_le (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    {j : ℕ} (hj : j ≤ K n) (hK : K n ≠ 0) : gridTime s t K n j ≤ t n := by
  have hΔ : 0 ≤ gridStep s t K n := qProxy_gridStep_nonneg hst
  have hlast := gridTime_last s t K n hK
  have hle : gridTime s t K n j ≤ gridTime s t K n (K n) := by
    unfold gridTime
    have : (j : ℝ) ≤ (K n : ℝ) := Nat.cast_le.2 hj
    nlinarith
  linarith

end GridArith

section AzumaQ

/-- **Target 7a (`azumaSubGQ_ugenN`)**: the merged `azumaProxy_subG_ugen` for `zVecQN` and `qvFormQN`, generic in
the stopping family `τ` and the sets `G` (no `AzumaSubGN` hypothesis: the merged `azumaSubGN` is used).  The
propagated `𝒬 Z` is `Σ_c κ'_c ZfamN(loop family)_c` pointwise (`qProxy_sum_Qop`), then `azumaSubGN` at the
weights `κ'` and the variance identity `qv_at_propagatorQ`.  What remains for a consumer is the deterministic
majorant `hQ` of `Δ · (m + 1) · qvFormQN` on `G j`.  RBM2D `azumaSubGQ_ugen` (`AltProxyQ:972`). -/
theorem azumaSubGQ_ugenN {d : ℕ} (sz : Sizes d) {E s t : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n m : ℕ) (hm : 1 ≤ m) (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (τ : PathΩ sz → ℕ)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
    (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (hG : ∀ ω j, j < τ ω → pathH sz s t K n j ω ∈ G j)
    (p : ℕ) (hp : p ≤ K n) (a : Fin (m + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s t K n * (((m + 1 : ℕ) : ℝ) * qvFormQN sz n ϑ (E n) (gridTime s t K n (j + 1))
        (gridTime s t K n p) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz (E n) σ (gridTime s t K n) τ (fun j ω => zVecQN sz E s t K n j ϑ σ ω) p a j Q := by
  have hKn : K n ≠ 0 := by omega
  have hu0 : 0 ≤ gridTime s t K n (j + 1) :=
    qProxy_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (qProxy_gridTime_le s t K n (hst n) (show j + 1 ≤ K n by omega) hKn).trans_lt (ht1 n)
  have hΔ : 0 ≤ gridStep s t K n := qProxy_gridStep_nonneg (hst n)
  set κ : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b => ∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n)
    (cycProd (fun i => mSigma (E n) (σ i)) i) (gridTime s t K n (j + 1)) (gridTime s t K n p)
    (a i) (b i) with hκ
  have hΦ : ∀ b, HermTestFun sz n (loopFamN sz E s t K n j σ b) := fun b =>
    (hermTestFunLoopN sz (m + 1) n (E n) (gridTime s t K n (j + 1)) (hE n) hu0 hu1 σ b).1
  have hcomb : ∀ ω' : PathΩ sz,
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n p)
        (zVecQN sz E s t K n j ϑ σ ω') a =
      ∑ c, qProxy_wts ϑ (gridTime s t K n (j + 1)) κ c *
        ZfamN sz s t K n j (loopFamN sz E s t K n j σ) ω' c := by
    intro ω'
    exact qProxy_sum_Qop ϑ (gridTime s t K n (j + 1)) κ (ZvecN sz E s t K n j σ ω')
  have hz := azumaSubGN sz s t K n (loopFamN sz E s t K n j σ) hΦ
    (qProxy_wts ϑ (gridTime s t K n (j + 1)) κ) τ G hτ hG j Q (fun M hMG hMH => by
      have h3 := qv_at_propagatorQ sz n (E n) (hE n) (gridTime s t K n (j + 1))
        (gridTime s t K n p) hu0 hu1 M hMH m hm ϑ σ a
      have h4 : ∀ c : CoordF d (sz.L n) (sz.W n),
          ∑ b, qProxy_wts ϑ (gridTime s t K n (j + 1)) κ b *
              dirDerivN (loopFamN sz E s t K n j σ b) M (coordinateMatrix d (sz.L n) (sz.W n) c) =
            ∑ b : Fin (m + 1) → Zd d (sz.L n), κ b * STQop (d := d) ϑ (gridTime s t K n (j + 1))
              (fun b'' => loopDerivN d (sz.L n) (sz.W n) (E n) (gridTime s t K n (j + 1)) M
                (coordinateMatrix d (sz.L n) (sz.W n) c) σ b'') b := fun c =>
        (qProxy_sum_Qop ϑ (gridTime s t K n (j + 1)) κ _).symm
      simp only [h4]
      exact (mul_le_mul_of_nonneg_left h3 hΔ).trans (hQ M hMG hMH))
  have hfun : (fun ω' : PathΩ sz => Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1))
      (gridTime s t K n p) (zVecQN sz E s t K n j ϑ σ ω') a) =
      fun ω => ∑ b, qProxy_wts ϑ (gridTime s t K n (j + 1)) κ b *
        ZfamN sz s t K n j (loopFamN sz E s t K n j σ) ω b := funext hcomb
  unfold SubGaussStopN
  rw [hfun]
  exact hz

/-- **Target 7b (`azumaSubGQ_gridExitN`)**: `azumaSubGQ_ugenN` at the exit time `gridExitTauN … G` of ANY
measurable family `G` (the membership hypothesis is `mem_of_lt_gridExitTauN`, the measurability hypothesis
`gridExitTauN_measurableSet`).  It replaces RBM2D `azumaSubGQ_goodExit` (`AltProxyQ:1027`), which hard-wires
`goodExitTauN` at one level `Φ` of `GoodSetN` (paper-delta candidate `T2194a`): here no level occurs. -/
theorem azumaSubGQ_gridExitN {d : ℕ} (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n m : ℕ) (hm : 1 ≤ m) (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
    (hG : ∀ j, MeasurableSet (G j))
    (p : ℕ) (hp : p ≤ K n) (a : Fin (m + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s v K n * (((m + 1 : ℕ) : ℝ) * qvFormQN sz n ϑ (E n) (gridTime s v K n (j + 1))
        (gridTime s v K n p) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz (E n) σ (gridTime s v K n) (gridExitTauN sz s v K n G)
      (fun j ω => zVecQN sz E s v K n j ϑ σ ω) p a j Q :=
  azumaSubGQ_ugenN sz hE hs0 hsv hv1 n m hm ϑ σ (gridExitTauN sz s v K n G) G
    (fun j => gridExitTauN_measurableSet hG j) (fun ω j hj => mem_of_lt_gridExitTauN hj) p hp a j hj
    Q hQ

end AzumaQ


/-! ## 6. The constants of `lem_+Q` and of EK-4 (extracted once, as `nqGood1C`) -/

section Constants

/-- **The constant `C_n(d, m, Λ_g, K, C, c)` of `lem_+Q`** (`(normQA)`, `3_5:1284-1289`; `stQopNorm_holds`),
chosen once for all `L, g, W, ε, D`; `1` outside the range of the pin.  It depends on `(d, m, Λ_g, K, C, c)`
only (the proof of `stQopNorm_holds` has `C_n = C + 2 d m + K m`). -/
def qProxyCn (d m : ℕ) (Λg K C c : ℝ) : ℝ :=
  if h : 3 ≤ d ∧ 0 < Λg ∧ 0 < K ∧ 0 < C ∧ 0 < c then
    Classical.choose (stQopNorm_holds d h.1 m Λg K C c h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 1

/-- **`C_Q = 2 C_n + 2`**: the additive exponent of the two-copy `lem_+Q` (`qqTensorBoundsN`). -/
def qProxyCQ (d m : ℕ) (Λg K C c : ℝ) : ℝ := 2 * qProxyCn d m Λg K C c + 2

/-- **The constant `C₄(d, k, Λ_g, κ', K)` of EK-4** (`ekSumDecay2_holds`, `lem:sum_decay` `(sum_res_2)`),
chosen once for all `L, g, W, ε, D`; `1` outside the range of the pin. -/
def qProxy4C (d k : ℕ) (Λg κ' K : ℝ) : ℝ :=
  if h : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' ∧ 0 < K then
    Classical.choose (ekSumDecay2_holds d k Λg κ' (prop5Decay_holds d Λg) (prop5Short_holds d Λg κ')
      (prop6Diff1_holds d Λg κ' (1 / 2)) h.1 h.2.1 h.2.2.1 h.2.2.2.1 K h.2.2.2.2)
  else 1

/-- **The threshold `W₀(d, m, Λ_g, K, C, c, C₀, ε, D)` of the decay clause of `lem_+Q`**
(`stQop_sub_fastDecay`, applied once at `(C₀ + C_n + 1, ε, D - C_n)`), at least `2`; `2` outside the range. -/
def qProxyW0 (d m : ℕ) (Λg K C c C₀ ε D : ℝ) : ℝ :=
  if h : 0 < C ∧ 0 < c ∧ 0 < ε then
    max 2 (Classical.choose (stQop_sub_fastDecay d m K C c (C₀ + qProxyCn d m Λg K C c + 1) ε
      (D - qProxyCn d m Λg K C c) h.1 h.2.1 h.2.2))
  else 2

theorem qProxyCn_pos {d : ℕ} (hd : 3 ≤ d) (m : ℕ) {Λg K C c : ℝ} (hΛ : 0 < Λg) (hK : 0 < K)
    (hC : 0 < C) (hc : 0 < c) : 0 < qProxyCn d m Λg K C c := by
  have h : 3 ≤ d ∧ 0 < Λg ∧ 0 < K ∧ 0 < C ∧ 0 < c := ⟨hd, hΛ, hK, hC, hc⟩
  unfold qProxyCn
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec (stQopNorm_holds d hd m Λg K C c hΛ hK hC hc)).1

theorem qProxy4C_pos {d k : ℕ} (hd : 3 ≤ d) (hk : 2 ≤ k) {Λg κ' K : ℝ} (hΛ : 0 < Λg)
    (hκ' : 0 < κ') (hK : 0 < K) : 0 < qProxy4C d k Λg κ' K := by
  have h : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' ∧ 0 < K := ⟨hd, hk, hΛ, hκ', hK⟩
  unfold qProxy4C
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec (ekSumDecay2_holds d k Λg κ' (prop5Decay_holds d Λg)
    (prop5Short_holds d Λg κ') (prop6Diff1_holds d Λg κ' (1 / 2)) hd hk hΛ hκ' K hK)).1

theorem qProxyCQ_pos {d : ℕ} (hd : 3 ≤ d) (m : ℕ) {Λg K C c : ℝ} (hΛ : 0 < Λg) (hK : 0 < K)
    (hC : 0 < C) (hc : 0 < c) : 0 < qProxyCQ d m Λg K C c := by
  have := qProxyCn_pos hd m hΛ hK hC hc
  unfold qProxyCQ
  linarith

theorem qProxyW0_ge_two (d m : ℕ) (Λg K C c C₀ ε D : ℝ) : 2 ≤ qProxyW0 d m Λg K C c C₀ ε D := by
  unfold qProxyW0
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- The one-copy bound `(normQA)` at the constant `qProxyCn` (the spec of `stQopNorm_holds`). -/
private theorem qProxyCn_spec {d : ℕ} (hd : 3 ≤ d) (m : ℕ) {Λg K C c : ℝ} (hΛ : 0 < Λg) (hK : 0 < K)
    (hC : 0 < C) (hc : 0 < c) :
    ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λg →
      ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → (L : ℝ) ^ d ≤ W ^ K →
      haveI : NeZero L := ⟨by omega⟩
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ 𝒜 : (Fin (m + 1) → Zd d L) → ℂ, EKFastDecay g t W ε D 𝒜 →
        ‖STQop (d := d) ϑ t 𝒜‖ ≤ W ^ (qProxyCn d m Λg K C c * ε) * ‖𝒜‖ +
          W ^ (-D + qProxyCn d m Λg K C c) := by
  have h : 3 ≤ d ∧ 0 < Λg ∧ 0 < K ∧ 0 < C ∧ 0 < c := ⟨hd, hΛ, hK, hC, hc⟩
  unfold qProxyCn
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec (stQopNorm_holds d hd m Λg K C c hΛ hK hC hc)).2

/-- The decay clause at the threshold `qProxyW0` (the spec of `stQop_sub_fastDecay`). -/
private theorem qProxyW0_spec {d : ℕ} (m : ℕ) {Λg K C c C₀ ε D : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) :
    ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g →
      ∀ W : ℝ, qProxyW0 d m Λg K C c C₀ ε D ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      haveI : NeZero L := ⟨by omega⟩
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ,
        ‖A‖ ≤ W ^ (C₀ + qProxyCn d m Λg K C c + 1) →
        EKFastDecay g t W ε (D - qProxyCn d m Λg K C c) (A - STQop (d := d) ϑ t A) := by
  have h : 0 < C ∧ 0 < c ∧ 0 < ε := ⟨hC, hc, hε⟩
  intro L hL g hg W hW hLK
  have hW' : Classical.choose (stQop_sub_fastDecay d m K C c (C₀ + qProxyCn d m Λg K C c + 1) ε
      (D - qProxyCn d m Λg K C c) hC hc hε) ≤ W := by
    refine le_trans ?_ hW
    unfold qProxyW0
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact le_max_right _ _
  exact (Classical.choose_spec (stQop_sub_fastDecay d m K C c (C₀ + qProxyCn d m Λg K C c + 1) ε
    (D - qProxyCn d m Λg K C c) hC hc hε)).2 L hL g hg W hW' hLK

/-- The spec of EK-4 at the constant `qProxy4C` (`ekSumDecay2_holds`). -/
private theorem qProxy4C_spec {d k : ℕ} (hd : 3 ≤ d) (hk : 2 ≤ k) {Λg κ' K : ℝ} (hΛ : 0 < Λg)
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

end Constants


/-! ## 7. Target 4: the two-copy `lem_+Q`

New mathematics (the paper has only the one-copy `lem_+Q`, `3_5:1284-1289`; RBM2D `qqTensorBoundsN`,
`AltProxyQ:711`, uses a concatenated window `3ρ` that is not needed here).  Inner copy, slice by slice
(`stQopNorm_holds`, `EKFastDecay` of `c' ↦ conj T_{c,c'}` from the far clause (Vb) of `GoodSetN`); a spread `c`
makes the whole slice `≤ W^{-D}`; the decay of `𝒬A = A - (A - 𝒬A)` is `stQop_sub_fastDecay` (threshold
`qProxyW0`). -/

section TwoCopy

private theorem qProxy_diam_append_right {d L k : ℕ} (b b' : Fin k → Zd d L) :
    STdiamInf b' ≤ STdiamInf (Fin.append b b') := by
  refine Finset.sup_le fun p _ => ?_
  have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) =>
      zdistInf d L (Fin.append b b' q.1 - Fin.append b b' q.2))
      (Finset.mem_univ (Fin.natAdd k p.1, Fin.natAdd k p.2))
  rw [Fin.append_right, Fin.append_right] at h
  exact h

private theorem qProxy_diam_append_left {d L k : ℕ} (b b' : Fin k → Zd d L) :
    STdiamInf b ≤ STdiamInf (Fin.append b b') := by
  refine Finset.sup_le fun p _ => ?_
  have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) =>
      zdistInf d L (Fin.append b b' q.1 - Fin.append b b' q.2))
      (Finset.mem_univ (Fin.castAdd k p.1, Fin.castAdd k p.2))
  rw [Fin.append_left, Fin.append_left] at h
  exact h

/-- A tuple with `ℓ¹`-spread `≥ W^ε ℓ_s` has `L^∞`-diameter `≥ ℓ_s W^{τ'}` once `d W^{τ'} ≤ W^ε`
(`zdistD ≤ d · zdistInf`; the conversion of the window of `GoodSetN` to the window of `EKFastDecay`). -/
private theorem qProxy_spread_diam {d L k : ℕ} (hd : 0 < d) (hL : 1 ≤ (L : ℝ)) {g s W ε τ' : ℝ}
    (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (b : Fin k → Zd d L)
    (hb : ∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (b i - b j) : ℝ)) :
    ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) := by
  obtain ⟨i, j, hij⟩ := hb
  have hell : 0 < ellT L g s := ellT_pos hL
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (zdistD d L (b i - b j) : ℝ) ≤ (d : ℝ) * (STdiamInf b : ℝ) := by
    have h2 := zdistD_le_mul_zdistInf d L (b i - b j)
    have h3 : zdistInf d L (b i - b j) ≤ STdiamInf b :=
      Finset.le_sup (f := fun p : Fin k × Fin k => zdistInf d L (b p.1 - b p.2))
        (Finset.mem_univ (i, j))
    exact_mod_cast h2.trans (Nat.mul_le_mul_left d h3)
  have h4 := mul_le_mul_of_nonneg_left hdW hell.le
  have h5 : (d : ℝ) * (ellT L g s * W ^ τ') ≤ (d : ℝ) * (STdiamInf b : ℝ) := by
    calc (d : ℝ) * (ellT L g s * W ^ τ') = ellT L g s * ((d : ℝ) * W ^ τ') := by ring
      _ ≤ ellT L g s * W ^ ε := h4
      _ = W ^ ε * ellT L g s := by ring
      _ ≤ _ := hij
      _ ≤ _ := h1
  exact le_of_mul_le_mul_left h5 hd0

/-- `2 W^a ≤ W^{a+1}` for `W ≥ 2`. -/
private theorem qProxy_two_le {W : ℝ} (hW : 2 ≤ W) (a : ℝ) : 2 * W ^ a ≤ W ^ (a + 1) := by
  have hW0 : 0 < W := by linarith
  rw [Real.rpow_add hW0, Real.rpow_one]
  have := Real.rpow_pos_of_pos hW0 a
  nlinarith

/-- `W^a (1 + W) ≤ W^{a+2}` and `W^a (2 + W) ≤ W^{a+2}` for `W ≥ 2`. -/
private theorem qProxy_add_two_le {W : ℝ} (hW : 2 ≤ W) (a : ℝ) (e : ℝ) (he : e ≤ 2) (he0 : 0 ≤ e) :
    W ^ a * (e + W) ≤ W ^ (a + 2) := by
  have hW0 : 0 < W := by linarith
  have h2 : W ^ (a + 2) = W ^ a * W ^ 2 := by
    rw [Real.rpow_add hW0, Real.rpow_two]
  rw [h2]
  have := Real.rpow_pos_of_pos hW0 a
  refine mul_le_mul_of_nonneg_left ?_ this.le
  nlinarith


/-- **Target 4 (`qqTensorBoundsN`): the two-copy `lem_+Q`** for `d ≥ 3`, `m ≥ 1`.  Constants: `C_n = qProxyCn`
(`d, m, Λ_g, K, C, c`), `C_Q = qProxyCQ = 2 C_n + 2`, `W₀ = qProxyW0` (`d, m, Λ_g, K, C, c, C₀, ε, D`), all before
`L, g, W`.  For `STMollifierProps g C c ϑ`, `L^d ≤ W^K`, `4 ≤ W^ε`, `d W^{τ'} ≤ W^ε`, `W ≥ W₀`, and a tensor `T`
with `‖T‖_∞ ≤ M_ee ≤ W^{C₀}` and `‖T_{b,b'}‖ ≤ W^{-D}` whenever `ℓ_t W^{τ'} ≤ diam_∞(b ⧺ b')` (the form (Vb) of
`GoodSetN`), `D > C_n + 2`:
(i) `‖(𝒬_t ⊗ 𝒬̄_t) T‖_∞ ≤ W^{2 C_n ε} M_ee + W^{-D + C_Q}`;
(ii) for each `b`, `b' ↦ ((𝒬_t ⊗ 𝒬̄_t) T)_{b,b'}` is `EKFastDecay g t W ε (D - C_Q)`;
(iii) for each `b'`, `|((𝒬_t ⊗ 𝒬̄_t) T)_{b,b'}| ≤ W^{-D+C_Q}` whenever `b` has `ℓ¹`-spread `≥ W^ε ℓ_t`
(block decay in `b`, uniform in `b'`; the ticket's factor `(2 + M_ee)` is not needed, paper-delta `T2194c`). -/
theorem qqTensorBoundsN {d m : ℕ} (hd : 3 ≤ d) (Λg K C c : ℝ) (hΛ : 0 < Λg) (hK : 0 < K)
    (hC : 0 < C) (hc : 0 < c) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg)
    {W ε τ' C₀ D : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε)
    (hLK : (L : ℝ) ^ d ≤ W ^ K) (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hC₀ : 0 ≤ C₀)
    (hD : qProxyCn d m Λg K C c + 2 < D) (hW₀ : qProxyW0 d m Λg K C c C₀ ε D ≤ W)
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (hϑ : STMollifierProps (d := d) g C c ϑ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (T : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ) {Mee : ℝ} (hMee : Mee ≤ W ^ C₀)
    (hT : ∀ b b', ‖T b b'‖ ≤ Mee)
    (hTfar : ∀ b b' : Fin (m + 1) → Zd d L,
      ellT L g t * W ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) → ‖T b b'‖ ≤ W ^ (-D)) :
    (∀ b b' : Fin (m + 1) → Zd d L, ‖qqTensorN ϑ t T b b'‖ ≤
        W ^ (2 * qProxyCn d m Λg K C c * ε) * Mee + W ^ (-D + qProxyCQ d m Λg K C c)) ∧
    (∀ b : Fin (m + 1) → Zd d L,
      EKFastDecay g t W ε (D - qProxyCQ d m Λg K C c) (fun b' => qqTensorN ϑ t T b b')) ∧
    (∀ b' b : Fin (m + 1) → Zd d L,
      (∃ i j, W ^ ε * ellT L g t ≤ (zdistD d L (b i - b j) : ℝ)) →
        ‖qqTensorN ϑ t T b b'‖ ≤ W ^ (-D + qProxyCQ d m Λg K C c)) := by
  set Cn := qProxyCn d m Λg K C c with hCn
  have hCn0 : 0 < Cn := qProxyCn_pos hd m hΛ hK hC hc
  have hnorm := qProxyCn_spec hd m hΛ hK hC hc
  have hdec := qProxyW0_spec (d := d) (Λg := Λg) (K := K) (C₀ := C₀) (D := D) (ε := ε) m hC hc hε0
  have hW2 : 2 ≤ W := (qProxyW0_ge_two d m Λg K C c C₀ ε D).trans hW₀
  have hW0 : 0 < W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hD1 : 1 < D := by linarith
  have hMee0 : 0 ≤ Mee := (norm_nonneg _).trans (hT (fun _ => 0) (fun _ => 0))
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  set X : ℝ := W ^ (Cn * ε) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hW0.le _
  have hXle : X ≤ W ^ Cn := Real.rpow_le_rpow_of_exponent_le hW.le (by nlinarith)
  have hQ1 : ∀ D' : ℝ, 1 < D' → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, EKFastDecay g t W ε D' A →
      ‖STQop (d := d) ϑ t A‖ ≤ X * ‖A‖ + W ^ (-D' + Cn) := fun D' hD' A hA =>
    hnorm L hL g hg hgΛ W ε D' hW hε0 hε1 hD' hWε hLK ϑ hϑ t ht0 ht1 A hA
  -- the slices of the inner copy
  have hSnorm : ∀ c : Fin (m + 1) → Zd d L,
      ‖(fun c' => starRingEnd ℂ (T c c'))‖ ≤ Mee := fun c =>
    (pi_norm_le_iff_of_nonneg hMee0).mpr fun c' => by simpa using hT c c'
  have hSfast : ∀ c : Fin (m + 1) → Zd d L,
      EKFastDecay g t W ε D (fun c' => starRingEnd ℂ (T c c')) := by
    intro c c' hc'
    have h1 := qProxy_spread_diam (by omega) hL1 hdW c' hc'
    have h2 : ellT L g t * W ^ τ' ≤ (STdiamInf (Fin.append c c') : ℝ) :=
      h1.trans (by exact_mod_cast qProxy_diam_append_right c c')
    simpa using hTfar c c' h2
  have hSall : ∀ c : Fin (m + 1) → Zd d L,
      (∃ i j, W ^ ε * ellT L g t ≤ (zdistD d L (c i - c j) : ℝ)) → ∀ c', ‖T c c'‖ ≤ W ^ (-D) := by
    intro c hc c'
    have h1 := qProxy_spread_diam (by omega) hL1 hdW c hc
    exact hTfar c c' (h1.trans (by exact_mod_cast qProxy_diam_append_left c c'))
  set B : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ := fun c b' =>
    starRingEnd ℂ (STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c')) b') with hB
  have hqq : ∀ b b', qqTensorN ϑ t T b b' = STQop (d := d) ϑ t (fun c => B c b') b :=
    fun b b' => rfl
  have hBnorm : ∀ c b', ‖B c b'‖ = ‖STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c')) b'‖ := by
    intro c b'
    simp [hB]
  have hWC : 0 ≤ X * Mee + W ^ (-D + Cn) := by positivity
  -- every entry of `B`
  have hBall : ∀ c b', ‖B c b'‖ ≤ X * Mee + W ^ (-D + Cn) := by
    intro c b'
    rw [hBnorm]
    calc _ ≤ ‖STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c'))‖ := norm_le_pi_norm _ b'
      _ ≤ X * ‖(fun c' => starRingEnd ℂ (T c c'))‖ + W ^ (-D + Cn) := hQ1 D hD1 _ (hSfast c)
      _ ≤ _ := by gcongr; exact hSnorm c
  -- a spread `c` makes the whole slice small
  have hBspread : ∀ c : Fin (m + 1) → Zd d L,
      (∃ i j, W ^ ε * ellT L g t ≤ (zdistD d L (c i - c j) : ℝ)) →
      ∀ b', ‖B c b'‖ ≤ 2 * W ^ (-D + Cn) := by
    intro c hc b'
    rw [hBnorm]
    have hSe : ‖(fun c' => starRingEnd ℂ (T c c'))‖ ≤ W ^ (-D) :=
      (pi_norm_le_iff_of_nonneg hWD).mpr fun c' => by simpa using hSall c hc c'
    have hfast' : EKFastDecay g t W ε D (fun c' => starRingEnd ℂ (T c c')) := fun a _ => by
      simpa using hSall c hc a
    calc _ ≤ ‖STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c'))‖ := norm_le_pi_norm _ b'
      _ ≤ X * ‖(fun c' => starRingEnd ℂ (T c c'))‖ + W ^ (-D + Cn) := hQ1 D hD1 _ hfast'
      _ ≤ X * W ^ (-D) + W ^ (-D + Cn) := by gcongr
      _ ≤ W ^ Cn * W ^ (-D) + W ^ (-D + Cn) := by gcongr
      _ = 2 * W ^ (-D + Cn) := by
          rw [← Real.rpow_add hW0, add_comm Cn (-D)]
          ring
  have hD₁ : 1 < D - Cn - 1 := by linarith
  have hsup : ∀ b', ‖(fun c => B c b')‖ ≤ X * Mee + W ^ (-D + Cn) := fun b' =>
    (pi_norm_le_iff_of_nonneg hWC).mpr fun c => hBall c b'
  -- the outer copy decays at `D - C_n - 1`
  have hFfast : ∀ b', EKFastDecay g t W ε (D - Cn - 1) (fun c => B c b') := by
    intro b' c hc
    calc ‖B c b'‖ ≤ 2 * W ^ (-D + Cn) := hBspread c hc b'
      _ ≤ W ^ (-D + Cn + 1) := qProxy_two_le hW2 _
      _ = W ^ (-(D - Cn - 1)) := by congr 1; ring
  have hCQ : qProxyCQ d m Λg K C c = 2 * Cn + 2 := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- (i)
    intro b b'
    rw [hqq]
    have hV : 0 ≤ W ^ (-D + 2 * Cn) := Real.rpow_nonneg hW0.le _
    calc ‖STQop (d := d) ϑ t (fun c => B c b') b‖ ≤ ‖STQop (d := d) ϑ t (fun c => B c b')‖ :=
          norm_le_pi_norm _ b
      _ ≤ X * ‖(fun c => B c b')‖ + W ^ (-(D - Cn - 1) + Cn) := hQ1 _ hD₁ _ (hFfast b')
      _ ≤ X * (X * Mee + W ^ (-D + Cn)) + W ^ (-(D - Cn - 1) + Cn) := by gcongr; exact hsup b'
      _ = (X * X) * Mee + (X * W ^ (-D + Cn) + W ^ (-(D - Cn - 1) + Cn)) := by ring
      _ ≤ W ^ (2 * Cn * ε) * Mee + W ^ (-D + (2 * Cn + 2)) := by
          have hXX : X * X = W ^ (2 * Cn * ε) := by
            rw [hX, ← Real.rpow_add hW0]; congr 1; ring
          rw [hXX]
          gcongr
          have h1 : X * W ^ (-D + Cn) ≤ W ^ (-D + 2 * Cn) := by
            calc X * W ^ (-D + Cn) ≤ W ^ Cn * W ^ (-D + Cn) := by gcongr
              _ = W ^ (-D + 2 * Cn) := by rw [← Real.rpow_add hW0]; congr 1; ring
          have h2 : W ^ (-(D - Cn - 1) + Cn) = W ^ (-D + 2 * Cn) * W := by
            rw [← Real.rpow_add_one hW0.ne']; congr 1; ring
          calc X * W ^ (-D + Cn) + W ^ (-(D - Cn - 1) + Cn)
              ≤ W ^ (-D + 2 * Cn) + W ^ (-D + 2 * Cn) * W := by rw [h2]; gcongr
            _ = W ^ (-D + 2 * Cn) * (1 + W) := by ring
            _ ≤ W ^ (-D + 2 * Cn + 2) := qProxy_add_two_le hW2 _ 1 (by norm_num) (by norm_num)
            _ = W ^ (-D + (2 * Cn + 2)) := by congr 1; ring
      _ = _ := by rw [hCQ]
  · -- (ii)
    intro b b' hb'
    change ‖qqTensorN ϑ t T b b'‖ ≤ _
    rw [hqq]
    have hall : ∀ c, ‖B c b'‖ ≤ 2 * W ^ (-D + Cn) := by
      intro c
      rw [hBnorm]
      have hs1 : ‖(starRingEnd ℂ) (T c b')‖ ≤ W ^ (-D) := hSfast c b' hb'
      have hAc : ‖(fun c' => starRingEnd ℂ (T c c'))‖ ≤ W ^ (C₀ + Cn + 1) :=
        (hSnorm c).trans (hMee.trans (Real.rpow_le_rpow_of_exponent_le hW.le (by linarith)))
      have hdc := hdec L hL g hg W hW₀ hLK ϑ hϑ t ht0 ht1 _ hAc b' hb'
      have heq : STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c')) b' =
          starRingEnd ℂ (T c b') - ((fun c' => starRingEnd ℂ (T c c')) -
            STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c'))) b' := by simp
      rw [heq]
      calc ‖starRingEnd ℂ (T c b') - ((fun c' => starRingEnd ℂ (T c c')) -
            STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c'))) b'‖
          ≤ ‖(starRingEnd ℂ) (T c b')‖ + ‖((fun c' => starRingEnd ℂ (T c c')) -
            STQop (d := d) ϑ t (fun c' => starRingEnd ℂ (T c c'))) b'‖ := norm_sub_le _ _
        _ ≤ W ^ (-D) + W ^ (-(D - Cn)) := add_le_add hs1 hdc
        _ ≤ W ^ (-D + Cn) + W ^ (-D + Cn) := by
            gcongr
            · exact hW.le
            · linarith
            · exact hW.le
            · linarith
        _ = 2 * W ^ (-D + Cn) := by ring
    have hF'fast : EKFastDecay g t W ε (D - Cn - 1) (fun c => B c b') := by
      intro c _
      calc ‖B c b'‖ ≤ 2 * W ^ (-D + Cn) := hall c
        _ ≤ W ^ (-D + Cn + 1) := qProxy_two_le hW2 _
        _ = W ^ (-(D - Cn - 1)) := by congr 1; ring
    have hsup' : ‖(fun c => B c b')‖ ≤ 2 * W ^ (-D + Cn) :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr hall
    calc ‖STQop (d := d) ϑ t (fun c => B c b') b‖ ≤ ‖STQop (d := d) ϑ t (fun c => B c b')‖ :=
          norm_le_pi_norm _ b
      _ ≤ X * ‖(fun c => B c b')‖ + W ^ (-(D - Cn - 1) + Cn) := hQ1 _ hD₁ _ hF'fast
      _ ≤ X * (2 * W ^ (-D + Cn)) + W ^ (-(D - Cn - 1) + Cn) := by gcongr
      _ ≤ W ^ (-(D - (2 * Cn + 2))) := by
          have h1 : X * (2 * W ^ (-D + Cn)) ≤ 2 * W ^ (-D + 2 * Cn) := by
            calc X * (2 * W ^ (-D + Cn)) ≤ W ^ Cn * (2 * W ^ (-D + Cn)) := by gcongr
              _ = 2 * W ^ (-D + 2 * Cn) := by
                  rw [← mul_assoc, mul_comm (W ^ Cn) 2, mul_assoc, ← Real.rpow_add hW0]
                  congr 2; ring
          have h2 : W ^ (-(D - Cn - 1) + Cn) = W ^ (-D + 2 * Cn) * W := by
            rw [← Real.rpow_add_one hW0.ne']; congr 1; ring
          calc X * (2 * W ^ (-D + Cn)) + W ^ (-(D - Cn - 1) + Cn)
              ≤ 2 * W ^ (-D + 2 * Cn) + W ^ (-D + 2 * Cn) * W := by rw [h2]; gcongr
            _ = W ^ (-D + 2 * Cn) * (2 + W) := by ring
            _ ≤ W ^ (-D + 2 * Cn + 2) := qProxy_add_two_le hW2 _ 2 (by norm_num) (by norm_num)
            _ = W ^ (-(D - (2 * Cn + 2))) := by congr 1; ring
      _ = W ^ (-(D - qProxyCQ d m Λg K C c)) := by rw [hCQ]
  · -- (iii)
    intro b' b hb
    rw [hqq]
    set F : (Fin (m + 1) → Zd d L) → ℂ := fun c => B c b' with hF
    have hX1 : 0 ≤ X * Mee := mul_nonneg hX0 hMee0
    have hFsup : ‖F‖ ≤ W ^ (C₀ + Cn + 1) := by
      refine (hsup b').trans ?_
      have h1 : X * Mee ≤ W ^ (Cn + C₀) := by
        calc X * Mee ≤ W ^ Cn * W ^ C₀ := mul_le_mul hXle hMee hMee0 (Real.rpow_nonneg hW0.le _)
          _ = W ^ (Cn + C₀) := by rw [← Real.rpow_add hW0]
      have h2 : W ^ (-D + Cn) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hW.le (by linarith)
      have h3 : 1 ≤ W ^ (Cn + C₀) := Real.one_le_rpow hW.le (by linarith)
      calc X * Mee + W ^ (-D + Cn) ≤ W ^ (Cn + C₀) + 1 := add_le_add h1 h2
        _ ≤ 2 * W ^ (Cn + C₀) := by linarith
        _ ≤ W ^ (Cn + C₀ + 1) := qProxy_two_le hW2 _
        _ = W ^ (C₀ + Cn + 1) := by congr 1; ring
    have hdF := hdec L hL g hg W hW₀ hLK ϑ hϑ t ht0 ht1 F hFsup b hb
    have hFb : ‖F b‖ ≤ 2 * W ^ (-D + Cn) := hBspread b hb b'
    have heq : STQop (d := d) ϑ t F b = F b - (F - STQop (d := d) ϑ t F) b := by simp
    rw [heq]
    calc ‖F b - (F - STQop (d := d) ϑ t F) b‖ ≤ ‖F b‖ + ‖(F - STQop (d := d) ϑ t F) b‖ :=
          norm_sub_le _ _
      _ ≤ 2 * W ^ (-D + Cn) + W ^ (-(D - Cn)) := add_le_add hFb hdF
      _ = 3 * W ^ (-D + Cn) := by
          have : -(D - Cn) = -D + Cn := by ring
          rw [this]; ring
      _ ≤ W ^ (-D + (2 * Cn + 2)) := by
          have h2 : W ^ (-D + (2 * Cn + 2)) = W ^ (-D + Cn) * W ^ (Cn + 2) := by
            rw [← Real.rpow_add hW0]; congr 1; ring
          rw [h2]
          have h3 : (3 : ℝ) ≤ W ^ (Cn + 2) := by
            have h4 : W ^ (2 : ℝ) ≤ W ^ (Cn + 2) :=
              Real.rpow_le_rpow_of_exponent_le hW.le (by linarith)
            have h5 : W ^ (2 : ℝ) = W * W := by rw [Real.rpow_two]; ring
            have h7 : (4 : ℝ) ≤ W * W := by nlinarith [mul_self_nonneg (W - 2)]
            calc (3 : ℝ) ≤ 4 := by norm_num
              _ ≤ W * W := h7
              _ = W ^ (2 : ℝ) := h5.symm
              _ ≤ W ^ (Cn + 2) := h4
          have h6 := Real.rpow_pos_of_pos hW0 (-D + Cn)
          nlinarith
      _ = W ^ (-D + qProxyCQ d m Λg K C c) := by rw [hCQ]

end TwoCopy


/-! ## 8. Target 5: the pair kernel from EK-4

Stage 1 acts on the `b'`-block (`σ̄ = !σ`, `EKSumZero` of the slice `b' ↦ T_{b,b'}`), stage 2 on the `b`-block
(`σ`, on `b ↦ (𝒰_σ̄ T_{b,·})(a)`, which is sum-zero because the `b`-fibre sum commutes with `𝒰_σ̄`).  No
alternation of `σ` is used: EK-4 (`ekSumDecay2_holds`) holds for every `σ` (paper-delta candidate `T2194b`; the
RBM2D proof used Case 5 of the `d = 2` evolution kernel with the concatenated window `3ρ`, alternating `σ` only). -/

section PairKernel

/-- **`hker` for sum-zero tensors, `d ≥ 3`** (the analogue of `hker_of_case1N` for EK-4 instead of EK-6): for
every `σ`, `0 ≤ s ≤ t ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-t)/(1-s)`, `κ' ≤ Im m(E)`, `log L ≤ W^ε`, `L^d ≤ W^K`, the kernel
`𝒰_{s,t,σ}` maps a sum-zero tensor of sup-norm `≤ M`, which is `≤ δ ≤ W^{-D}` (`D > 1`) off the window
`ℓ¹`-spread `< W^ε ℓ_s`, to `W^{C₄ε} ((g²+|1-s|)/(g²+|1-t|))^k M + W^{C₄} δ`, `C₄ = qProxy4C d k Λ_g κ' K`. -/
private theorem qProxy_hker {d k : ℕ} (Λg κ' K : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg)
    (hκ' : 0 < κ') (hK : 0 < K) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g)
    (hgΛ : g ≤ Λg) {W ε D : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε)
    (hlog : Real.log L ≤ W ^ ε) (hLK : (L : ℝ) ^ d ≤ W ^ K) (hD : 1 < D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2)
    (hWt : W⁻¹ ≤ (1 - t) / (1 - s)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im)
    {σ : Fin k → Bool} (X : (Fin k → Zd d L) → ℂ) (hz : EKSumZero X) {M δ : ℝ} (hM : 0 ≤ M)
    (hδ : 0 ≤ δ) (hδD : δ ≤ W ^ (-D)) (hXM : ∀ b, ‖X b‖ ≤ M)
    (hXcls : ∀ b : Fin k → Zd d L,
      (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (b i - b j) : ℝ)) → ‖X b‖ ≤ δ)
    (a : Fin k → Zd d L) :
    ‖Ugen d L g E σ s t X a‖ ≤
      W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * M +
        W ^ qProxy4C d k Λg κ' K * δ := by
  set C : ℝ := qProxy4C d k Λg κ' K with hC
  have hEK := qProxy4C_spec hd hk hΛ hκ' hK
  have hW0 : (0 : ℝ) < W := by linarith
  have hr : 0 ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k :=
    mul_nonneg (Real.rpow_nonneg hW0.le _) (by positivity)
  have hX : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr hXM
  have hat : ∀ D'' : ℝ, 1 < D'' → δ ≤ W ^ (-D'') → ‖Ugen d L g E σ s t X a‖ ≤
      W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * M + W ^ (-D'' + C) := by
    intro D'' hD'' hδD''
    have hfast : EKFastDecay g s W ε D'' X := fun b hb => (hXcls b hb).trans hδD''
    have h := hEK L hL g hg hgΛ W ε D'' hW hε0 hε1 hD'' hWε hlog hLK s t hs hst ht hWt (mE E)
      (norm_mE hE) hκm σ X hfast hz
    have h2 : ‖Ugen d L g E σ s t X a‖ ≤ ‖UN d L g (EKsgn (mE E) σ) s t X‖ :=
      norm_le_pi_norm (UN d L g (EKsgn (mE E) σ) s t X) a
    calc ‖Ugen d L g E σ s t X a‖ ≤ ‖UN d L g (EKsgn (mE E) σ) s t X‖ := h2
      _ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k * ‖X‖ +
          W ^ (-D'' + C) := h
      _ ≤ _ := by gcongr
  rcases hδ.eq_or_lt with h0 | hpos
  · -- `δ = 0`: let `D'' → ∞`
    subst h0
    rw [mul_zero, add_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    set D'' : ℝ := max 2 (C - Real.logb W η) with hD''
    have hD1 : 1 < D'' := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have h1 := hat D'' hD1 (Real.rpow_nonneg hW0.le _)
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
    have h1 := hat D'' (by linarith) hWD''.symm.le
    rw [Real.rpow_add hW0, hWD''] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring

/-- **Target 5 (`ugenPairQN_le_of_bounds`): the pair kernel `(𝒰_σ ⊗ 𝒰_σ̄) ∘ T` at `(a, a)` from EK-4**, for
EVERY `σ`, `d ≥ 3`, `k ≥ 2`: a tensor `T_{b,b'}` that is sum-zero in each block (`EKSumZero`), with
`‖T_{b,b'}‖ ≤ M'` and, at one level `δ' ≤ W^{-D₂}` (`D₂ > k + 1`), the slice decay (`b'` spread) and the block
decay (`b` spread) in the `ℓ¹`-window of `EKFastDecay` at the time `s`:
`‖(𝒰_{s,t,σ} ⊗ 𝒰_{s,t,σ̄}) ∘ T (a,a)‖ ≤ κ₄ (κ₄ M' + W^{C₄} δ') + W^{C₄} (W^k δ')`,
`κ₄ = W^{C₄ ε} ((g²+|1-s|)/(g²+|1-t|))^k`, `C₄ = qProxy4C d k Λ_g κ' K`.  Stage 1 on the `b'`-block (`σ̄`), stage 2
on the `b`-block (`σ`) with far level `W^k δ'` (`norm_UN_apply_le`, `(1-s)/(1-t) ≤ W`).  The pattern of
`nqGood1_ugenPairN_le_of_bounds` (`NQGood1.lean:431`) with EK-4 in place of EK-6. -/
theorem ugenPairQN_le_of_bounds {d k : ℕ} (Λg κ' K : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg)
    (hκ' : 0 < κ') (hK : 0 < K) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g)
    (hgΛ : g ≤ Λg) {W ε D₂ : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε)
    (hlog : Real.log L ≤ W ^ ε) (hLK : (L : ℝ) ^ d ≤ W ^ K) (hD : (k : ℝ) + 1 < D₂)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2)
    (hWt : W⁻¹ ≤ (1 - t) / (1 - s)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im)
    {σ : Fin k → Bool} (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) {M' δ' : ℝ} (hδ : 0 ≤ δ')
    (hδD : δ' ≤ W ^ (-D₂)) (hT : ∀ b b', ‖T b b'‖ ≤ M')
    (hz1 : ∀ b' : Fin k → Zd d L, EKSumZero (fun b => T b b'))
    (hz2 : ∀ b : Fin k → Zd d L, EKSumZero (fun b' => T b b'))
    (hslice : ∀ b b' : Fin k → Zd d L,
      (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (b' i - b' j) : ℝ)) → ‖T b b'‖ ≤ δ')
    (hblock : ∀ b b' : Fin k → Zd d L,
      (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (b i - b j) : ℝ)) → ‖T b b'‖ ≤ δ')
    (a : Fin k → Zd d L) :
    ‖UgenPairN d L g E σ s t T a‖ ≤
      (W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k) *
          ((W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k) * M' +
            W ^ qProxy4C d k Λg κ' K * δ') +
        W ^ qProxy4C d k Λg κ' K * (W ^ k * δ') := by
  set C : ℝ := qProxy4C d k Λg κ' K with hCdef
  have hW0 : 0 < W := by linarith
  have hD1 : 1 < D₂ := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hs1 : s < 1 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      positivity
    linarith
  have ht1 : t < 1 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      positivity
    linarith
  rw [nqGood1_UgenPairN_eq_Ugen]
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hT (fun _ => 0) (fun _ => 0))
  set κ1 : ℝ := W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k with hκ1
  have hκ10 : 0 ≤ κ1 := mul_nonneg (Real.rpow_nonneg hW0.le _) (by positivity)
  have hWC0 : 0 ≤ W ^ C := Real.rpow_nonneg hW0.le _
  -- stage 1: the `b'`-block, for every `b`
  have hstage1 : ∀ b : Fin k → Zd d L,
      ‖Ugen d L g E (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ κ1 * M' + W ^ C * δ' := by
    intro b
    exact qProxy_hker Λg κ' K hd hk hΛ hκ' hK hL hg hgΛ hW hε0 hε1 hWε hlog hLK hD1 hs hst ht hWt hE
      hκm (fun b' => T b b') (hz2 b) hM'0 hδ hδD (fun b' => hT b b')
      (fun b' hb' => hslice b b' hb') a
  -- the far decay of the stage-1 output
  have hP : (1 - s) / (1 - t) ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hP0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  have hstage1far : ∀ b : Fin k → Zd d L,
      (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (b i - b j) : ℝ)) →
      ‖Ugen d L g E (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ W ^ k * δ' := by
    intro b hb
    have hT' : ‖(fun b' => T b b')‖ ≤ δ' :=
      (pi_norm_le_iff_of_nonneg hδ).mpr fun b' => hblock b b' hb
    have h1 := norm_UN_apply_le (d := d) (L := L) (g := g) hL
      (m := fun i => mSigma E (!σ i)) (fun i => norm_mSigma hE _) hs hst ht1
      (fun b' => T b b') a
    calc _ ≤ ((1 - s) / (1 - t)) ^ k * ‖(fun b' => T b b')‖ := h1
      _ ≤ W ^ k * δ' := by gcongr
  have hδ2 : W ^ k * δ' ≤ W ^ (-(D₂ - k)) := by
    calc W ^ k * δ' ≤ W ^ k * W ^ (-D₂) := by gcongr
      _ = W ^ (-(D₂ - k)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hW0]
          congr 1; ring
  -- the stage-1 output is sum-zero in `b`
  have hY0 : EKSumZero (fun b : Fin k → Zd d L =>
      Ugen d L g E (fun i => !σ i) s t (fun b' => T b b') a) := by
    intro i₀ hi x
    unfold Ugen UN
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [← Finset.mul_sum, hz1 b' i₀ hi x, mul_zero]
  have hstage2 := qProxy_hker Λg κ' K hd hk hΛ hκ' hK hL hg hgΛ hW hε0 hε1 hWε hlog hLK
    (D := D₂ - k) (by linarith) hs hst ht hWt hE hκm (σ := σ)
    (fun b => Ugen d L g E (fun i => !σ i) s t (fun b' => T b b') a) hY0
    (M := κ1 * M' + W ^ C * δ') (δ := W ^ k * δ')
    (add_nonneg (mul_nonneg hκ10 hM'0) (mul_nonneg hWC0 hδ))
    (mul_nonneg (pow_nonneg hW0.le _) hδ) hδ2 hstage1 hstage1far a
  calc _ ≤ _ := hstage2
    _ = _ := by ring

end PairKernel


/-! ## 9. Target 6: the quadratic-variation majorant of `qvFormQN` -/

section QVBound

section ConjKernel

variable {d L : ℕ} [NeZero L] {g : ℝ}

private theorem qProxy_SB_conj (a b : Zd d L) :
    (starRingEnd ℂ) (SB d L g a b) = SB d L g a b := by
  rw [SB_apply, sbKernel_eq_ofReal, Complex.conj_ofReal]

/-- `Θ_{conj ξ} = conj Θ_ξ` entrywise (copy of the private `nqGood1_Theta_star`). -/
private theorem qProxy_Theta_star (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g (star ξ) a b = star (Theta d L g ξ a b) := by
  have hξ' : ‖star ξ‖ < 1 := by rwa [norm_star]
  have hmul : (Theta d L g ξ).map (starRingEnd ℂ) * (1 - star ξ • SB d L g) = 1 := by
    have h := congrArg (fun A : Matrix (Zd d L) (Zd d L) ℂ => A.map (starRingEnd ℂ))
      (Theta_mul_of_three_le (d := d) (g := g) hL hξ)
    simp only [Matrix.map_mul] at h
    have h1 : (1 - ξ • SB d L g).map (starRingEnd ℂ) = 1 - star ξ • SB d L g := by
      ext x y
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul, qProxy_SB_conj]
      split_ifs <;> simp
    rw [h1] at h
    rw [h]
    ext x y
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have key := eq_Theta_of_mul d L g (norm_SB d L g hL) hξ' hmul
  have := congrFun (congrFun key a) b
  simpa using this.symm

/-- `conj (uKer μ v w) = uKer (conj μ) v w` for real `v, w` (copy of the private `nqGood1_conj_uKer`). -/
private theorem qProxy_conj_uKer (hL : 3 ≤ L) {μ : ℂ} {v w : ℝ} (hξ : ‖(w : ℂ) * μ‖ < 1)
    (x y : Zd d L) :
    (starRingEnd ℂ) (uKer d L g μ v w x y) = uKer d L g ((starRingEnd ℂ) μ) v w x y := by
  have hT := qProxy_Theta_star (d := d) (L := L) (g := g) hL hξ
  have hw : star ((w : ℂ) * μ) = (w : ℂ) * (starRingEnd ℂ) μ := by
    simp [Complex.conj_ofReal]
  rw [hw] at hT
  unfold uKer
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
      map_mul, qProxy_SB_conj, Complex.conj_ofReal]
    split_ifs <;> simp
  · exact (hT z y).symm ▸ rfl

private theorem qProxy_mSigma_not (E : ℝ) (s : Bool) :
    mSigma E (!s) = (starRingEnd ℂ) (mSigma E s) := by
  cases s <;> simp [mSigma]

end ConjKernel

/-- **`qvFormQN` is the real part of the pair kernel `𝒰_σ ⊗ 𝒰_σ̄` applied to `(𝒬 ⊗ 𝒬̄)(𝓔 ⊗ 𝓔)`**: the
conjugate of the slotwise kernel of `σ` is the slotwise kernel of `σ̄` (`m(σ̄) = conj m(σ)`, `S^{(B)}` real).
The `qqTensorN` form of `qvFormN_eq_re_UgenPairN` (`NQGood1.lean:230`); RBM2D `AltProxyQ_qvFormQN_eq_re`
(`AltProxyQ:852`). -/
private theorem qProxy_qvFormQN_eq_re {d : ℕ} (sz : Sizes d) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) {E : ℝ} (hE : |E| ≤ 2) {v w : ℝ} (hw : |w| < 1)
    (σ : Fin (m + 1) → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    qvFormQN sz n ϑ E v w σ M a =
      (UgenPairN d (sz.L n) (sz.lam n) E σ v w
        (qqTensorN ϑ v (fun c c' => sz.STeeM n E v M σ c c')) a).re := by
  unfold qvFormQN UgenPairN
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : (starRingEnd ℂ) (∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n)
      (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b' i)) =
      ∏ i : Fin (m + 1), uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (!σ i)) i) v w
        (a i) (b' i) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hn : ‖(w : ℂ) * cycProd (fun i => mSigma E (σ i)) i‖ < 1 := by
      rw [cycProd, norm_mul, norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul, mul_one,
        Complex.norm_real]
      simpa using hw
    rw [qProxy_conj_uKer (sz.three_le_L n) hn]
    congr 1
    simp only [cycProd, map_mul, ← qProxy_mSigma_not]
  rw [hconj]

/-- **Target 6a (`qvFormQN_le_of_bounds`)**: the closed-form majorant of the variance form of the `𝒬`-process from
bounds on `𝓔 ⊗ 𝓔` at the time `v` (`‖STeeM‖ ≤ M_ee ≤ W^{C₀}`, and `≤ W^{-D}` when `ℓ_v W^{τ'} ≤ diam_∞(b ⧺ b')`),
for EVERY `σ` (EK-4 needs no alternation), `m ≥ 1`, `k = m + 1`:
`qvFormQN_{v,w,σ}(M)(a) ≤ κ₄ (κ₄ M_Q + W^{C₄} δ_Q) + W^{C₄} (W^k δ_Q)`,
`κ₄ = W^{C₄ ε} ((g²+|1-v|)/(g²+|1-w|))^k`, `M_Q = W^{2 C_n ε} M_ee + W^{-D+C_Q}`, `δ_Q = W^{-D+C_Q}`
(`C_n = qProxyCn`, `C_Q = qProxyCQ`, `C₄ = qProxy4C`; the ticket's `δ_Q = W^{-D+C_Q}(2 + M_ee)` is not needed,
`T2194c`).  Route: `qvFormQN = Re 𝒰_σ⊗𝒰_σ̄ ((𝒬⊗𝒬̄)(𝓔⊗𝓔))` (`qProxy_qvFormQN_eq_re`), `Re ≤ ‖·‖`, the two-copy
`lem_+Q` (`qqTensorBoundsN`), the block sum-zero property (`qqTensorN_sumZero`) and the EK-4 pair kernel
(`ugenPairQN_le_of_bounds`).  Needs `D > m + 2 + C_Q`.  RBM2D `qvFormQN_le_of_bounds` (`AltProxyQ:882`). -/
theorem qvFormQN_le_of_bounds {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (Λg κ' K C c : ℝ)
    (hΛ : 0 < Λg) (hκ' : 0 < κ') (hK : 0 < K) (hC : 0 < C) (hc : 0 < c)
    (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg)
    {ε τ' C₀ D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hC₀ : 0 ≤ C₀)
    (hD : (m : ℝ) + 2 + qProxyCQ d m Λg K C c < D)
    (hW₀ : qProxyW0 d m Λg K C c C₀ ε D ≤ ((sz.W n : ℕ) : ℝ))
    {ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - v)) {E : ℝ} (hE : |E| ≤ 2)
    (hκm : κ' ≤ (mE E).im) {σ : Fin (m + 1) → Bool}
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {Mee : ℝ}
    (hMee : Mee ≤ ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hT : ∀ b b' : Fin (m + 1) → Zd d (sz.L n), ‖sz.STeeM n E v M σ b b'‖ ≤ Mee)
    (hTfar : ∀ b b' : Fin (m + 1) → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) →
        ‖sz.STeeM n E v M σ b b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    qvFormQN sz n ϑ E v w σ M a ≤
      (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) *
          ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) *
        ((((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) *
            ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) *
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d m Λg K C c * ε) * Mee +
            ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) +
          ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1) Λg κ' K *
            ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) +
        ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1) Λg κ' K *
          (((sz.W n : ℕ) : ℝ) ^ (m + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) := by
  have hL3 := sz.three_le_L n
  have hLpos : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hgL : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have hw1 : w < 1 := by linarith
  have hCQ0 : 0 < qProxyCQ d m Λg K C c := qProxyCQ_pos hd m hΛ hK hC hc
  have hCn0 : 0 < qProxyCn d m Λg K C c := qProxyCn_pos hd m hΛ hK hC hc
  have hCQ : qProxyCQ d m Λg K C c = 2 * qProxyCn d m Λg K C c + 2 := rfl
  have hDn : qProxyCn d m Λg K C c + 2 < D := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hv1 : v < 1 := by linarith
  obtain ⟨hi, hii, hiii⟩ := qqTensorBoundsN hd Λg K C c hΛ hK hC hc hL3 hg hgΛ hW hε0 hε1 hWε hLK hdW
    hC₀ hDn hW₀ hϑ hv0 hv1 (fun b b' => sz.STeeM n E v M σ b b') hMee hT hTfar
  obtain ⟨hz1, hz2⟩ := qqTensorN_sumZero ϑ v (hϑ.1 v) (fun c c' => sz.STeeM n E v M σ c c')
  rw [qProxy_qvFormQN_eq_re sz n ϑ hE (abs_lt.2 ⟨by linarith, hw1⟩) σ M a]
  refine (Complex.re_le_norm _).trans ?_
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  exact ugenPairQN_le_of_bounds Λg κ' K hd (by omega) hΛ hκ' hK hL3 hg hgΛ hW hε0 hε1 hWε hlog hLK
    (D₂ := D - qProxyCQ d m Λg K C c) (by push_cast; linarith) hv0 hvw hwL hWt hE hκm
    (fun b b' => qqTensorN ϑ v (fun c c' => sz.STeeM n E v M σ c c') b b')
    (δ' := ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c))
    (Real.rpow_nonneg hW0.le _) (le_of_eq (by congr 1; ring)) hi hz1 hz2
    (fun b b' hb' => by
      have h := hii b b' hb'
      rw [show -(D - qProxyCQ d m Λg K C c) = -D + qProxyCQ d m Λg K C c by ring] at h
      exact h)
    (fun b b' hb => hiii b' b hb) a

/-- **Target 6b (`qvFormQN_le_of_goodSetN`)**: 6a on the good set at the time `u` of the good set: for
`M ∈ GoodSetN n E u (m+1) Γ Λ Φ τ' D`, clauses (D4) and (Vb) give `M_ee = Γ(ΓΛ)B_u^{2k}/η_u` and `δ = W^{-D}`.
**`Φ` is arbitrary and absent from the right side** (only the membership uses it; the level of the current
length plays no role here, DECISIONS §62 (4)).  RBM2D `qvFormQN_le_of_goodSet` (`AltProxyQ:933`);
pattern `qvFormN_le_of_goodSetN` (`NQGood1.lean:551`). -/
theorem qvFormQN_le_of_goodSetN {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (Λg κ' K C c : ℝ)
    (hΛ : 0 < Λg) (hκ' : 0 < κ') (hK : 0 < K) (hC : 0 < C) (hc : 0 < c)
    (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg)
    {ε τ' C₀ D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hC₀ : 0 ≤ C₀)
    (hD : (m : ℝ) + 2 + qProxyCQ d m Λg K C c < D)
    (hW₀ : qProxyW0 d m Λg K C c C₀ ε D ≤ ((sz.W n : ℕ) : ℝ))
    {ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    {u w : ℝ} (hu0 : 0 ≤ u) (huw : u ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - u)) {E : ℝ} (hE : |E| ≤ 2)
    (hκm : κ' ≤ (mE E).im) {σ : Fin (m + 1) → Bool} {Γ Λ Φ : ℝ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D)
    (hMee : Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1)) / etaT E u) ≤ ((sz.W n : ℕ) : ℝ) ^ C₀)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    qvFormQN sz n ϑ E u w σ M a ≤
      (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) *
          ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) *
        ((((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) *
            ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) *
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d m Λg K C c * ε) *
              (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1)) / etaT E u)) +
            ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) +
          ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1) Λg κ' K *
            ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) +
        ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1) Λg κ' K *
          (((sz.W n : ℕ) : ℝ) ^ (m + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) := by
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := hM
  exact qvFormQN_le_of_bounds hd hm Λg κ' K C c hΛ hκ' hK hC hc sz n hg hgΛ hW hε0 hε1 hWε hlog hLK
    hdW hC₀ hD hW₀ hϑ hu0 huw hwL hWt hE hκm M hMee (fun b b' => hD4 σ b b')
    (fun b b' hfar => hVb σ b b' hfar) a

end QVBound


/-! ## 10. Target 8: the `Y` moments of the `𝒬`-increment -/

section YQ

private theorem qProxy_card_filter {d L m : ℕ} [NeZero L] (x : Zd d L) :
    (((Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = x)).card : ℕ) : ℝ) =
      ((L : ℝ) ^ d) ^ m := by
  have h : (Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = x)).card =
      Fintype.card (Fin m → Zd d L) := by
    rw [← Finset.card_univ (α := Fin m → Zd d L)]
    refine Finset.card_bij' (fun a _ => Fin.tail a) (fun y _ => Fin.cons x y) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro y _; simp
    · intro a ha
      have ha0 : a 0 = x := (Finset.mem_filter.1 ha).2
      rw [← ha0]; exact Fin.cons_self_tail a
    · intro y _; simp
  rw [h, Fintype.card_fun, Fintype.card_fin, card_Zd]
  push_cast
  rfl

/-- From `STMollifierProps`: `‖ϑ_t‖ ≤ C` on `[0, 1)` (`ℓ_t ≥ 1`, `c ≥ 0`, `C ≥ 0`); copy of the private
`QGridA_vartheta_sup` (`QGridA.lean:1943`). -/
private theorem qProxy_vartheta_sup {d m L : ℕ} [NeZero L] (hL : 1 ≤ L) {g C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 ≤ c) {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ}
    (hϑ : STMollifierProps (d := d) g C c ϑ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Fin (m + 1) → Zd d L) : ‖ϑ t a‖ ≤ C := by
  have h := hϑ.2.1 t ht0 ht1 a
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast hL)
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le zero_lt_one hℓ1
  have h1 : (((ellT L g t) ^ d)⁻¹) ^ m ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 (by positivity)) (inv_le_one_of_one_le₀ (one_le_pow₀ hℓ1))
  have h2 : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
      (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have hs : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have : 0 ≤ c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) :=
      mul_nonneg hc hs
    rw [neg_mul]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ0.le
  refine h.trans ?_
  calc C * (((ellT L g t) ^ d)⁻¹) ^ m * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
        (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) ≤ C * 1 * 1 := by
        gcongr
    _ = C := by ring

/-- The transposed weights have `ℓ¹` norm at most `1 + C (L^d)^m` times that of `κ` (`‖ϑ‖ ≤ C`, and every `b`
lies in the `(L^d)^m` fibres `{c : c₀ = b₀}`): the kernel row sum of `𝒬_u` (RBM2D `AltProxyQ_sum_norm_wts_le`,
`AltProxyQ:1053`, with `‖ϑ‖ ≤ 1` replaced by `‖ϑ‖ ≤ C` at `d ≥ 3`: paper-delta candidate `T2194d`). -/
private theorem qProxy_sum_norm_wts_le {d m L : ℕ} [NeZero L] (hL : 1 ≤ L) {g C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ}
    (hϑ : STMollifierProps (d := d) g C c ϑ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (κ : (Fin (m + 1) → Zd d L) → ℂ) :
    ∑ c', ‖qProxy_wts ϑ t κ c'‖ ≤ (1 + C * ((L : ℝ) ^ d) ^ m) * ∑ b, ‖κ b‖ := by
  have h1 : ∀ c' : Fin (m + 1) → Zd d L, ‖qProxy_wts ϑ t κ c'‖ ≤
      ‖κ c'‖ + C * ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0), ‖κ b‖ := by
    intro c'
    unfold qProxy_wts
    calc ‖κ c' - ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0),
          κ b * ϑ t b‖ ≤ ‖κ c'‖ + ‖∑ b ∈ Finset.univ.filter
          (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0), κ b * ϑ t b‖ := norm_sub_le _ _
      _ ≤ ‖κ c'‖ + C * ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0),
            ‖κ b‖ := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (qProxy_vartheta_sup hL hC hc hϑ ht0 ht1 b)
            (norm_nonneg _)
  have h2 : ∑ c' : Fin (m + 1) → Zd d L,
      ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0), ‖κ b‖ =
      ((L : ℝ) ^ d) ^ m * ∑ b, ‖κ b‖ := by
    have h3 : ∀ c' : Fin (m + 1) → Zd d L,
        ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0), ‖κ b‖ =
        ∑ b : Fin (m + 1) → Zd d L, if c' 0 = b 0 then ‖κ b‖ else 0 := by
      intro c'
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun b _ => if_congr eq_comm rfl rfl
    simp only [h3]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, qProxy_card_filter]
  calc ∑ c', ‖qProxy_wts ϑ t κ c'‖ ≤ ∑ c' : Fin (m + 1) → Zd d L, (‖κ c'‖ +
        C * ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0), ‖κ b‖) :=
        Finset.sum_le_sum fun c' _ => h1 c'
    _ = ∑ c', ‖κ c'‖ + C * ∑ c' : Fin (m + 1) → Zd d L,
        ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) → Zd d L => b 0 = c' 0), ‖κ b‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (1 + C * ((L : ℝ) ^ d) ^ m) * ∑ b, ‖κ b‖ := by rw [h2]; ring

/-- `𝒬_u` of a strongly measurable family is strongly measurable (`𝒬_u` is a continuous linear map of the
finite-dimensional space of tensors). -/
private theorem qProxy_stronglyMeasurable_yVecQN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)
    (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => yVecQN sz E s t K n j ϑ σ ω) := by
  have hcont : Continuous (fun A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ =>
      STQop (d := d) ϑ (gridTime s t K n (j + 1)) A) := by
    refine continuous_pi fun a => ?_
    unfold STQop STPsum
    exact (continuous_apply a).sub
      ((continuous_finsetSum _ fun c _ => continuous_apply c).mul continuous_const)
  exact hcont.comp_stronglyMeasurable (gridAsm_stronglyMeasurable_YvecN sz E s t K n j σ)

open scoped Matrix.Norms.L2Operator in
/-- **Item 8 with an explicit strictly positive level** (the body of `yMomentsQUnifN`, private as RBM2D
`AltProxyQ_yMomentsQPos`, `AltProxyQ:1137`): the statement of `yMomentsQUnifN` with `0 < P`; the instance of
`yMomentsQUnifN` (`QProxyInst.yMomentsQUnifN_instance_pos`) uses it to exhibit `P > 0`. -/
private theorem qProxy_yMomentsQPos {d : ℕ} (sz : Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ) :
    0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.SizeTendsto → sz.RangeCond τ' t →
    ∀ (m : ℕ) (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), 0 < C → 0 ≤ c →
      (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → ∀ σ : Fin (m + 1) → Bool,
      ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
        ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 < P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
          ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
            YMomentBoundsN sz (E n) σ (gridTime s t K n) τ (K n)
              (fun j ω => yVecQN sz E s t K n j (ϑ n) σ ω)
              (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2) := by
  intro hκ hE hs0 hst ht1 hsize hrange m C c ϑ hC hc hϑ σ
  have hc0 : 0 < Real.sqrt (κ * (4 - κ)) / 2 := AzumaProxyN_c0_pos_pub hκ (hE 0)
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0def
  set θ : ℝ := max 0 (1 - τ') with hθdef
  have hθ0 : 0 ≤ θ := le_max_left _ _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  refine ⟨11 + (4 * ((m + 1 : ℕ) : ℝ) + 4) * θ + 2 * m + 2, by positivity, ?_⟩
  intro K hK
  have hbig := hsize.eventually (eventually_ge_atTop
    (max (1 + C) (2000 * (2 ^ (m + 1) * (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) *
      (c0⁻¹) ^ (m + 1 + 2)) ^ 2)))
  filter_upwards [hrange, hbig] with n hR hN
  have hN1' : 1 + C ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hbig' : 2000 * (2 ^ (m + 1) * (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) *
      (c0⁻¹) ^ (m + 1 + 2)) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hN
  have hΘ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := Real.one_le_rpow hN1 hθ0
  have hΘ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := by positivity
  set Smax : ℝ := (2 * ((sz.size n : ℕ) : ℝ) ^ θ) ^ (m + 1) with hSmax
  set C2 : ℝ := (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ)
    * (((sz.size n : ℕ) : ℝ) ^ θ / c0) ^ (m + 1 + 2) with hC2def
  have hS0 : 0 < Smax := by positivity
  have hC20 : 0 < C2 := by
    have : (0 : ℝ) < (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega) (by omega)
    positivity
  have hLN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have hL0 : 0 < sz.L n := by have := sz.three_le_L n; omega
    have h : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    exact_mod_cast h
  set Lm : ℝ := 1 + C * (((sz.L n : ℕ) : ℝ) ^ d) ^ m with hLm
  have hLm0 : 0 < Lm := by positivity
  have hLmN : Lm ≤ ((sz.size n : ℕ) : ℝ) ^ (m + 1) := by
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d) ^ m ≤ ((sz.size n : ℕ) : ℝ) ^ m :=
      pow_le_pow_left₀ (by positivity) hLN m
    have h2 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ m := one_le_pow₀ hN1
    calc Lm ≤ ((sz.size n : ℕ) : ℝ) ^ m + C * ((sz.size n : ℕ) : ℝ) ^ m := by
          rw [hLm]; gcongr
      _ = (1 + C) * ((sz.size n : ℕ) : ℝ) ^ m := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ m := by gcongr
      _ = ((sz.size n : ℕ) : ℝ) ^ (m + 1) := by ring
  set Smax' : ℝ := Lm * Smax with hSmax'
  have hS0' : 0 < Smax' := by positivity
  refine ⟨2000 * (Smax' * C2) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8, by positivity, ?_, ?_⟩
  · -- `P ≤ N^{C_P}`
    have hP0 := AzumaProxyN_P_le_pub (m + 1) hc0 hθ0 hN1 hbig'
    have hpow : Lm ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * m + 2) := by
      calc Lm ^ 2 ≤ (((sz.size n : ℕ) : ℝ) ^ (m + 1)) ^ 2 := pow_le_pow_left₀ hLm0.le hLmN 2
        _ = ((sz.size n : ℕ) : ℝ) ^ (2 * m + 2) := by rw [← pow_mul]; ring_nf
    calc 2000 * (Smax' * C2) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8
        = Lm ^ 2 * (2000 * (Smax * C2) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 8) := by
          rw [hSmax']; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * m + 2) *
          ((sz.size n : ℕ) : ℝ) ^ (11 + (4 * ((m + 1 : ℕ) : ℝ) + 4) * θ) :=
          mul_le_mul hpow hP0 (by positivity) (by positivity)
      _ = ((sz.size n : ℕ) : ℝ) ^ (11 + (4 * ((m + 1 : ℕ) : ℝ) + 4) * θ + 2 * m + 2) := by
          rw [← Real.rpow_natCast ((sz.size n : ℕ) : ℝ) (2 * m + 2), ← Real.rpow_add hN0]
          congr 1
          push_cast
          ring
  · intro τ hτ
    refine ⟨fun j => qProxy_stronglyMeasurable_yVecQN sz E s t K n j (ϑ n) σ, ?_⟩
    intro p hp b j hjp
    have hj : j + 1 ≤ K n := by omega
    have hEn : |E n| < 2 := by have := hE n; linarith
    have hv0 : 0 ≤ gridTime s t K n (j + 1) := qProxy_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
    have hvt : gridTime s t K n (j + 1) ≤ t n := qProxy_gridTime_le s t K n (hst n) hj (hK n)
    have hv1 : gridTime s t K n (j + 1) < 1 := hvt.trans_lt (ht1 n)
    have hw0 : 0 ≤ gridTime s t K n p := qProxy_gridTime_nonneg s t K n (hs0 n) (hst n) p
    have hwt : gridTime s t K n p ≤ t n := qProxy_gridTime_le s t K n (hst n) hp (hK n)
    have hw1 : gridTime s t K n p < 1 := hwt.trans_lt (ht1 n)
    set κb : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b' => ∏ i : Fin (m + 1), uKer d (sz.L n)
      (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i) (gridTime s t K n (j + 1))
      (gridTime s t K n p) (b i) (b' i) with hκb
    have hUrow : ∑ b', ‖κb b'‖ ≤ Smax := by
      refine (AzumaProxyN_rowsum_Ugen_pub (sz.three_le_L n) hEn.le σ hv0 hv1 hw0 hw1 b).trans ?_
      have h1 : (1 - gridTime s t K n p)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τ') :=
        AzumaProxyN_inv_one_sub_le_pub hwt hN0 hR
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (1 - τ') ≤ ((sz.size n : ℕ) : ℝ) ^ θ :=
        Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) (m + 1)
    have hrow : ∑ c', ‖qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb c'‖ ≤ Smax' :=
      (qProxy_sum_norm_wts_le (by have := sz.three_le_L n; omega) hC.le hc (hϑ n) hv0 hv1 κb).trans
        (mul_le_mul_of_nonneg_left hUrow hLm0.le)
    have hC2' : ∀ (a : Fin (m + 1) → Zd d (sz.L n))
        (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
        y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN sz E s t K n j σ a)) M y y‖ ≤
          C2 * ‖y‖ ^ 2 := by
      intro a M y hM hy
      have hη := AzumaProxyN_etaT_inv_le_pub (κ := κ) (E := E n)
        (u := gridTime s t K n (j + 1)) (t := t n) (τ' := τ') (N := ((sz.size n : ℕ) : ℝ)) hκ
        (hE n) hvt hN0 hR
      have hη' : (etaT (E n) (gridTime s t K n (j + 1)))⁻¹
          ≤ ((sz.size n : ℕ) : ℝ) ^ θ / c0 :=
        hη.trans (by
          gcongr
          exact le_max_right _ _)
      have h := (hermTestFunLoopN sz (m + 1) n (E n) (gridTime s t K n (j + 1)) hEn hv0 hv1 σ a).2
        M y hM hy
      refine h.trans ?_
      have hle : (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ)
          * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1 + 2) ≤ C2 := by
        rw [hC2def]
        have hη0 : 0 ≤ (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ := by
          have := etaT_pos hEn hv1
          positivity
        have := pow_le_pow_left₀ hη0 hη' (m + 1 + 2)
        have hpos : 0 ≤ (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left this hpos |>.trans (le_of_eq (by ring))
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hcomb : ∀ ω' : PathΩ sz,
        Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n p)
          (yVecQN sz E s t K n j (ϑ n) σ ω') b =
        ∑ c', qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb c' *
          YvecN sz E s t K n j σ ω' c' := fun ω' =>
      qProxy_sum_Qop (ϑ n) (gridTime s t K n (j + 1)) κb (YvecN sz E s t K n j σ ω')
    have hpt : ∀ ω, stoppedEdgeN sz (E n) σ (gridTime s t K n) (gridTime s t K n p) τ
        (fun j ω => yVecQN sz E s t K n j (ϑ n) σ ω) b j ω =
        AzumaProxyN_stopW sz E s t K n j σ
          (qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb) τ ω := by
      intro ω
      unfold stoppedEdgeN AzumaProxyN_stopW
      by_cases h : ω ∈ {ω' | j < τ ω'}
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
        exact hcomb ω
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    have h8 := AzumaProxyN_YfieldsW sz E s t K n j hEn (hs0 n) (hst n) (ht1 n) hj σ
      (qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb) hS0'.le hC20.le hrow hC2' le_rfl τ hτ
    simp only [hpt]
    exact h8

/-- **Target 8 (`yMomentsQUnifN`)**: the `𝒬`-analogue of the merged `yMomentsUnifN` (`AzumaProxyN2.lean:915`) for a
mollifier family `ϑ n` with constants `C > 0`, `c ≥ 0` (every consumer has `c = 1/2`).  **Explicit witness**
`C_P = 11 + (4 (m+1) + 4) · max 0 (1 - τ') + 2 m + 2` (the constant of the merged `yMomentsUnifN` at `k = m + 1`
plus `2 m + 2` for the kernel row-sum factor `1 + C (L^d)^m ≤ N^{m+1}` of `𝒬_u`, squared in `P`; paper-delta
candidate `T2194d`), chosen before the grid `K`; for `N = size n ≥ max (1 + C) (2000 (2^k k (k+1) c₀^{-(k+2)})²)`
and the range condition, `P = 2000 (S' C₂)² N⁸` with `S' = (1 + C (L^d)^m)(2 Θ)^k`, `C₂ = k (k+1) N (Θ/c₀)^{k+2}`,
`Θ = N^{max 0 (1-τ')}`.  Route: the stopped propagated increment `1_{j<τ} (𝒰 𝒬_{u_{j+1}} Y_j)_b` is
`1_{j<τ} Σ_c κ'_c (Y_j)_c` with the transposed weights `κ'` (`qProxy_sum_Qop`); then the merged
`AzumaProxyN_YfieldsW`.  RBM2D `yMomentsQUnifN` (`AltProxyQ:1272`). -/
theorem yMomentsQUnifN {d : ℕ} (sz : Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ) :
    0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.SizeTendsto → sz.RangeCond τ' t →
    ∀ (m : ℕ) (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), 0 < C → 0 ≤ c →
      (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → ∀ σ : Fin (m + 1) → Bool,
      ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
        ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
          ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
            YMomentBoundsN sz (E n) σ (gridTime s t K n) τ (K n)
              (fun j ω => yVecQN sz E s t K n j (ϑ n) σ ω)
              (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2) := by
  intro hκ hE hs0 hst ht1 hsize hrange m C c ϑ hC hc hϑ σ
  obtain ⟨C_P, hC_P, h⟩ := qProxy_yMomentsQPos sz κ τ' E s t hκ hE hs0 hst ht1 hsize hrange m C c ϑ
    hC hc hϑ σ
  refine ⟨C_P, hC_P, fun K hK => ?_⟩
  filter_upwards [h K hK] with n ⟨P, hP, hPN, hτ⟩
  exact ⟨P, hP.le, hPN, hτ⟩

end YQ

/-! ## 11. Compiled nonempty instances (namespace `QProxyInst`)

Data of `QGridACheck` and `AzumaProxyNInst` on the merged `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`lam_n = (2(n+1))^{-6}`; at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`): the alternating signs
`σ = QGridACheck.sigma4` (`m = 3`, four indices) and the merged mollifier `QopAlgebra_mollifier`
(`QGridACheck.moll` at `n = 0`).  Items 1, 5, 6 at `n = 0` (items 5, 6 on the grid `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4`);
item 2 at a non-scalar Hermitian `M`; item 3 at the delta tensor; item 4: target 5 at `L = 5`, `W = 25`; targets 4,
6a, 6b at `sz0` for an `n` with `W_n ≥ W₀ = qProxyW0` (taken from `exists_nat_ge`: the threshold is the theorem's
own, no property of `C_n`, `C₄`, `W₀` beyond their specs is used), with `ε = 1/5`, `τ' = 1/10` so that both windows
fit in the torus. -/

namespace QProxyInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst RBM.Ind.GridDriftNCheck
  RBM.Ind.QGridACheck RBM.Ind.AzumaProxyNInst

/-! ### Item 1: `martIncQN_ae_eq` -/

theorem martIncQN_ae_eq_instance (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    ∀ᵐ ω ∂(pathP sz0), martIncQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω a =
      zVecQN sz0 E0 s0 t0 K0 0 0 moll sigma4 ω a + yVecQN sz0 E0 s0 t0 K0 0 0 moll sigma4 ω a :=
  martIncQN_ae_eq sz0 E0 s0 t0 K0 0 0 (by norm_num [E0]) (by rw [data.2.2]; norm_num) moll sigma4 a

/-! ### Item 2: `qv_at_propagatorQ` at a non-scalar Hermitian `M` -/

/-- The non-scalar Hermitian matrix `X_{(0,0,true)}`. -/
abbrev Mx : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ :=
  coordinateMatrix 3 (sz0.L 0) (sz0.W 0)
    ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true)

theorem qv_at_propagatorQ_instance (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ) *
        ‖∑ b : Fin (3 + 1) → Zd 3 (sz0.L 0),
          (∏ i : Fin (3 + 1), uKer 3 (sz0.L 0) (sz0.lam 0)
            (cycProd (fun i => mSigma (1 / 2) (sigma4 i)) i) (1 / 3) (1 / 2) (a i) (b i)) *
          STQop (d := 3) moll (1 / 3) (fun b'' => loopDerivN 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 3) Mx
            (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c) sigma4 b'') b‖ ^ 2 ≤
      ((3 + 1 : ℕ) : ℝ) * qvFormQN sz0 0 moll (1 / 2) (1 / 3) (1 / 2) sigma4 Mx a :=
  qv_at_propagatorQ sz0 0 (1 / 2) (by norm_num [abs_of_pos]) (1 / 3) (1 / 2) (by norm_num)
    (by norm_num) Mx (coordinateMatrix_isHermitian 3 (sz0.L 0) (sz0.W 0) _) 3 (by norm_num) moll
    sigma4 a

/-! ### Item 3: `qqTensorN_sumZero` at the delta tensor and the merged mollifier -/

/-- The delta tensor `1_{(0,0)}` on `(Fin (m + 1) → Z_L^d)²` (nonzero, not sum-zero). -/
def deltaTensor {d L : ℕ} (m : ℕ) : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ :=
  fun c c' => if c = 0 ∧ c' = 0 then 1 else 0

/-- The delta tensor `𝒜 = 1_{(0,0)}` on `(Fin 2 → Z_5^3)²`. -/
abbrev Adelta : (Fin (1 + 1) → Zd 3 5) → (Fin (1 + 1) → Zd 3 5) → ℂ := deltaTensor 1

theorem Adelta_ne : Adelta ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [Adelta, deltaTensor] at this

/-- `𝒜` itself is not sum-zero (in the first block, at `b' = 0`): the conclusion of `qqTensorN_sumZero` is a
property of `𝒬 ⊗ 𝒬̄ 𝒜`, not of `𝒜`. -/
theorem Adelta_not_sumZero : ¬ EKSumZero (fun b => Adelta b 0) := by
  intro h
  have h1 := h 0 rfl 0
  simp [Adelta, deltaTensor] at h1

theorem qqTensorN_sumZero_instance (t : ℝ) :
    (∀ b', EKSumZero (fun b => qqTensorN (QopAlgebra_mollifier 3 5 1 1) t Adelta b b')) ∧
      (∀ b, EKSumZero (fun b' => qqTensorN (QopAlgebra_mollifier 3 5 1 1) t Adelta b b')) :=
  qqTensorN_sumZero (QopAlgebra_mollifier 3 5 1 1) t
    ((QopAlgebra_mollifier_props 3 5 1 (by norm_num) one_pos).1 t) Adelta

/-! ### Item 5: the sub-Gaussian input (grid `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4`, `E ≡ 1/2`, `n = 0`) -/

/-- **Instance of `azumaSubGQ_ugenN`**: for every target time `p ∈ (0, 4]` and label `a`, with `τ ≡ K 0 = 4`
(`{j < τ}` is the whole space), `G 0 = {0}` (`H_0 = 0`, `s ≡ 0`) and `G j = {Hermitian}`, and `Q` the exact
variance form at `M = 0`; every hypothesis of the theorem is discharged. -/
theorem azumaSubGQ_ugenN_instance (p : ℕ) (hp : p ≤ Kg 0) (hp0 : 0 < p)
    (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    SubGaussStopN sz0 (Einst 0) sigma4 (gridTime sInst vg Kg 0) (fun _ => Kg 0)
      (fun j ω => zVecQN sz0 Einst sInst vg Kg 0 j moll sigma4 ω) p a 0
      (Real.toNNReal (gridStep sInst vg Kg 0 * (((3 + 1 : ℕ) : ℝ) *
        qvFormQN sz0 0 moll (Einst 0) (gridTime sInst vg Kg 0 (0 + 1)) (gridTime sInst vg Kg 0 p)
          sigma4 0 a))) := by
  refine azumaSubGQ_ugenN sz0 Einst_abs_lt sInst_nonneg sInst_le_vg vg_lt_one 0 3 (by norm_num) moll
    sigma4 (fun _ => Kg 0) (fun j M => M.IsHermitian ∧ (j = 0 → M = 0))
    (fun j => MeasurableSet.const _)
    (fun ω j hj => ⟨pathH_isHermitian sz0 sInst vg Kg 0 j ω, fun hj0 => by
      subst hj0
      exact azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg 0 rfl ω⟩) p hp a 0 hp0 _
    (fun M hM _ => ?_)
  rw [hM.2 rfl]
  exact Real.le_coe_toNNReal _

/-- **Instance of `azumaSubGQ_gridExitN`** at the exit time of the good sets `GoodSetN … u_j` (measurable by
`measurableGoodSetN`), any levels `Γ Λ Φ` and exponents `τ' D'`; the deterministic majorant `hQ` stays a
hypothesis (the work of the Step 3 tickets S3-15/S3-18, as in the merged `azumaSubGN_goodExit_instance`). -/
theorem azumaSubGQ_gridExitN_instance (Γ Λ Φ τ' D' : ℝ) (p : ℕ) (hp : p ≤ Kg 0)
    (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < p) (Q : ℝ≥0)
    (hQ : ∀ M ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) (3 + 1) Γ Λ Φ τ' D',
      M.IsHermitian → gridStep sInst vg Kg 0 * (((3 + 1 : ℕ) : ℝ) * qvFormQN sz0 0 moll (Einst 0)
        (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 p) sigma4 M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz0 (Einst 0) sigma4 (gridTime sInst vg Kg 0)
      (gridExitTauN sz0 sInst vg Kg 0 (fun j =>
        sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) (3 + 1) Γ Λ Φ τ' D'))
      (fun j ω => zVecQN sz0 Einst sInst vg Kg 0 j moll sigma4 ω) p a j Q :=
  azumaSubGQ_gridExitN sz0 Einst_abs_lt sInst_nonneg sInst_le_vg vg_lt_one 0 3 (by norm_num) moll
    sigma4 (fun j => sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) (3 + 1) Γ Λ Φ τ' D')
    (fun j => measurableGoodSetN 3 sz0 0 _ _ _ _ _ _ _ _) p hp a j hj Q hQ

/-- **Instance of `azumaSubGQ_gridExitN` with `hQ` discharged**: the family `G j = {0}` (measurable) and `Q` the
exact variance form at `M = 0`. -/
theorem azumaSubGQ_gridExitN_instance_zero (p : ℕ) (hp : p ≤ Kg 0)
    (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < p) :
    SubGaussStopN sz0 (Einst 0) sigma4 (gridTime sInst vg Kg 0)
      (gridExitTauN sz0 sInst vg Kg 0 (fun _ =>
        ({0} : Set (Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ))))
      (fun j ω => zVecQN sz0 Einst sInst vg Kg 0 j moll sigma4 ω) p a j
      (Real.toNNReal (gridStep sInst vg Kg 0 * (((3 + 1 : ℕ) : ℝ) *
        qvFormQN sz0 0 moll (Einst 0) (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 p)
          sigma4 0 a))) :=
  azumaSubGQ_gridExitN sz0 Einst_abs_lt sInst_nonneg sInst_le_vg vg_lt_one 0 3 (by norm_num) moll
    sigma4 (fun _ => {0}) (fun _ => measurableSet_singleton 0) p hp a j hj _
    (fun M hM _ => by
      rw [Set.mem_singleton_iff.1 hM]
      exact Real.le_coe_toNNReal _)

/-! ### Item 6: `yMomentsQUnifN` with `P > 0` -/

/-- `RangeCond` at the instance: `N^{-1+1/2} ≤ 1 - 1/32` for `N ≥ 4` (copy of the private
`azumaProxy2_rangeCond_vg`). -/
private theorem rangeCond_vg : sz0.RangeCond (1 / 2) vg := by
  filter_upwards [sz0_tendsto.eventually_ge_atTop (4 : ℝ)] with n hn
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h := Real.rpow_le_rpow_of_nonpos h4 hn (show (-1 + (1 / 2 : ℝ)) ≤ 0 by norm_num)
  have h2 : (4 : ℝ) ^ (-1 + (1 / 2 : ℝ)) = 1 / 2 := by
    rw [show (-1 + (1 / 2 : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h3 : (1 : ℝ) - vg n = 31 / 32 := by norm_num [vg]
  rw [h3]
  linarith

private theorem Kg_ne_zero : ∀ n, Kg n ≠ 0 := fun n => by simp [Kg]

private theorem gridStep_pos (n : ℕ) : 0 < gridStep sInst vg Kg n := by
  unfold gridStep
  exact div_pos (by norm_num [vg, sInst]) (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Kg_ne_zero n)))

private theorem lam_pos_n (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

/-- **Instance of `yMomentsQUnifN` with `P > 0`** (`m = 3`, every `σ`, `ϑ_n = QopAlgebra_mollifier`, `C = (1 + 40·9)·6^9`,
`c = 1/2`): `C_P` before the grid `K = Kg`, applied at a concrete `n` from the eventual filter, with the stopping
time `τ ≡ K n` and the window `Δ > 0`; the level `P` is the explicit positive one (`qProxy_yMomentsQPos`). -/
theorem yMomentsQUnifN_instance_pos (σ : Fin (3 + 1) → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 < P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => yVecQN sz0 Einst sInst vg Kg n j
          (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := qProxy_yMomentsQPos sz0 1 (1 / 2) Einst sInst vg one_pos
    (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one sz0_tendsto rangeCond_vg 3
    ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1 / 2)
    (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) (by positivity) (by norm_num)
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, gridStep_pos n,
    hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩

/-- **Instance of `yMomentsQUnifN`** itself (the public statement, `0 ≤ P`). -/
theorem yMomentsQUnifN_instance (σ : Fin (3 + 1) → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => yVecQN sz0 Einst sInst vg Kg n j
          (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsQUnifN sz0 1 (1 / 2) Einst sInst vg one_pos
    (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one sz0_tendsto rangeCond_vg 3
    ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1 / 2)
    (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) (by positivity) (by norm_num)
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, gridStep_pos n,
    hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩

/-! ### Item 4: targets 4-6 (`qqTensorBoundsN`, `ugenPairQN_le_of_bounds`, `qvFormQN_le_of_bounds`,
`qvFormQN_le_of_goodSetN`) -/

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

private theorem diam_append_zero {d L k : ℕ} :
    STdiamInf (Fin.append (0 : Fin k → Zd d L) (0 : Fin k → Zd d L)) = 0 := by
  have h : ∀ i, Fin.append (0 : Fin k → Zd d L) (0 : Fin k → Zd d L) i = 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  unfold STdiamInf
  refine (Finset.sup_eq_bot_iff _ _).2 fun p _ => ?_
  simp [h, zdistInf]

/-! #### Target 5 at `d = 3`, `k = 2`, `L = 5`, `g = 1/2`, `W = 25` -/

/-- `e = (1,0,0) ∈ Z_5^3`. -/
private abbrev e5 : Zd 3 5 := ![1, 0, 0]

/-- The sum-zero vector `w = 1_{(0,0)} - 1_{(0,e)}` on `(Z_5^3)²` (first coordinate fixed). -/
def w5 : (Fin 2 → Zd 3 5) → ℂ := fun b =>
  (if b = ![0, 0] then 1 else 0) - (if b = ![0, e5] then 1 else 0)

private theorem zero_ne_e5 : (0 : Zd 3 5) ≠ e5 := by
  intro h
  have := congrFun h 0
  simp only [e5, Pi.zero_apply, Matrix.cons_val_zero] at this
  exact absurd this (by decide)

private theorem b1_ne_b2 : (![0, 0] : Fin 2 → Zd 3 5) ≠ ![0, e5] := by
  intro h
  exact zero_ne_e5 (congrFun h 1)

private theorem zdistD_e5 : zdistD 3 5 e5 = 1 := by
  unfold zdistD
  simp only [zdist, e5, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    ZMod.val_zero, tsub_zero, zero_le, inf_of_le_left, add_zero, Matrix.cons_val]
  decide

theorem w5_sumZero : EKSumZero w5 := by
  intro i₀ hi x
  have hi0 : i₀ = 0 := Fin.ext (by simpa using hi)
  subst hi0
  unfold w5
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Finset.mem_filter]

private theorem w5_b1 : w5 ![0, 0] = 1 := by
  simp only [w5, b1_ne_b2, ↓reduceIte]
  norm_num

theorem w5_ne : w5 ≠ 0 := by
  intro h
  have := congrFun h ![0, 0]
  simp only [w5, b1_ne_b2, ↓reduceIte, Pi.zero_apply] at this
  norm_num at this

private theorem w5_norm (b : Fin 2 → Zd 3 5) : ‖w5 b‖ ≤ 1 := by
  by_cases h1 : b = ![0, 0]
  · subst h1
    simp only [w5, b1_ne_b2, ↓reduceIte]
    norm_num
  · by_cases h2 : b = ![0, e5]
    · subst h2
      simp only [w5, h1, ↓reduceIte]
      norm_num
    · simp only [w5, h1, h2, ↓reduceIte]
      norm_num

private theorem w5_small (b : Fin 2 → Zd 3 5) (hb : w5 b ≠ 0) :
    ∀ i j : Fin 2, (zdistD 3 5 (b i - b j) : ℝ) ≤ 1 := by
  have hb' : b = ![0, 0] ∨ b = ![0, e5] := by
    by_contra h
    rw [not_or] at h
    apply hb
    simp only [w5, h.1, h.2, ↓reduceIte]
    norm_num
  rcases hb' with rfl | rfl
  · simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp
  · simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp
    · have : (![0, e5] : Fin 2 → Zd 3 5) 0 - (![0, e5] : Fin 2 → Zd 3 5) 1 = -e5 := by simp
      rw [this, zdistD_neg, zdistD_e5]; norm_num
    · have : (![0, e5] : Fin 2 → Zd 3 5) 1 - (![0, e5] : Fin 2 → Zd 3 5) 0 = e5 := by simp
      rw [this, zdistD_e5]; norm_num
    · simp

/-- The pair tensor `T = w ⊗ w` (sum-zero in each block, supported on tuples of spread `≤ 1`). -/
def T5 : (Fin 2 → Zd 3 5) → (Fin 2 → Zd 3 5) → ℂ := fun b b' => w5 b * w5 b'

theorem T5_ne : T5 ≠ 0 := by
  intro h
  have := congrFun (congrFun h ![0, 0]) ![0, 0]
  simp only [T5, w5_b1, Pi.zero_apply] at this
  norm_num at this

private theorem rpow25 : (25 : ℝ) ^ (1 / 2 : ℝ) = 5 := by
  rw [← Real.sqrt_eq_rpow, show (25 : ℝ) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

private theorem ellT_five_le : ellT 5 (1 / 2) (1 / 2) ≤ 1 := by
  unfold ellT
  refine (min_le_left _ _).trans (max_le ?_ le_rfl)
  rw [div_le_one (Real.sqrt_pos.2 (by rw [abs_of_pos (by norm_num)]; norm_num))]
  exact (Real.le_sqrt' (by norm_num : (0 : ℝ) < 1 / 2)).2
    (by rw [abs_of_pos (by norm_num)]; norm_num)

private theorem zdistD_222 : zdistD 3 5 (![2, 2, 2] : Zd 3 5) = 6 := by
  unfold zdistD
  simp only [zdist, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  decide

/-- The `ℓ¹` window of the instance (`W^ε ℓ_s = 5`) is attained: the tuple `(0, (2,2,2))` has `ℓ¹`-spread `6`. -/
private theorem window_five :
    ∃ b : Fin 2 → Zd 3 5, ∃ i j,
      (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ) := by
  refine ⟨![0, ![2, 2, 2]], 1, 0, ?_⟩
  have h1 : (![0, ![2, 2, 2]] : Fin 2 → Zd 3 5) 1 - (![0, ![2, 2, 2]] : Fin 2 → Zd 3 5) 0 =
      ![2, 2, 2] := by simp
  rw [h1, zdistD_222, rpow25]
  have := ellT_five_le
  push_cast
  nlinarith

/-- **Instance of `ugenPairQN_le_of_bounds`** (target 5): `d = 3`, `k = 2`, `L = 5`, `g = 1/2`, `Λ_g = 1`,
`κ' = 1/2`, `K = 2`, `W = 25`, `ε = 1/2` (`W^ε = 5 ≤ 6`, the `ℓ¹`-diameter of the torus: the window is attained),
`D₂ = 4 > k + 1`, `s = 1/2 < t = 9/10`, `E = 0` (`Im m = 1`), `σ = (+,-)`, the nonzero tensor `T = w ⊗ w`,
sum-zero in each block, `M' = 1`, `δ' = 0` (the decay clauses hold because the support has `ℓ¹`-spread `≤ 1 < 5 ≤
W^ε ℓ_s`): every hypothesis is discharged. -/
theorem ugenPairQN_le_of_bounds_instance (a : Fin 2 → Zd 3 5) :
    (∃ b : Fin 2 → Zd 3 5, ∃ i j,
      (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ)) ∧
    ‖UgenPairN 3 5 (1 / 2) 0 ![true, false] (1 / 2) (9 / 10) T5 a‖ ≤
      (25 ^ (qProxy4C 3 2 1 (1 / 2) 2 * (1 / 2 : ℝ)) *
          (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2) *
        ((25 ^ (qProxy4C 3 2 1 (1 / 2) 2 * (1 / 2 : ℝ)) *
            (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2) * 1 +
          25 ^ qProxy4C 3 2 1 (1 / 2) 2 * 0) +
        25 ^ qProxy4C 3 2 1 (1 / 2) 2 * (25 ^ 2 * 0) := by
  have hW5 : (4 : ℝ) ≤ (25 : ℝ) ^ (1 / 2 : ℝ) := by rw [rpow25]; norm_num
  have hlog : Real.log ((5 : ℕ) : ℝ) ≤ (25 : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((5 : ℕ) : ℝ) by norm_num)
    rw [rpow25]
    push_cast at this ⊢
    linarith
  have hLK : ((5 : ℕ) : ℝ) ^ 3 ≤ (25 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; norm_num
  have hz1 : ∀ b' : Fin 2 → Zd 3 5, EKSumZero (fun b => T5 b b') := by
    intro b' i₀ hi x
    have h := w5_sumZero i₀ hi x
    simp only [T5, ← Finset.sum_mul, h, zero_mul]
  have hz2 : ∀ b : Fin 2 → Zd 3 5, EKSumZero (fun b' => T5 b b') := by
    intro b i₀ hi x
    have h := w5_sumZero i₀ hi x
    simp only [T5, ← Finset.mul_sum, h, mul_zero]
  have hT : ∀ b b' : Fin 2 → Zd 3 5, ‖T5 b b'‖ ≤ 1 := fun b b' => by
    unfold T5
    rw [norm_mul]
    calc ‖w5 b‖ * ‖w5 b'‖ ≤ 1 * 1 := mul_le_mul (w5_norm b) (w5_norm b') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hspread : ∀ b : Fin 2 → Zd 3 5,
      (∃ i j, (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ)) →
        w5 b = 0 := by
    intro b ⟨i, j, hij⟩
    by_contra hne
    have h1 := w5_small b hne i j
    have h2 : (1 : ℝ) ≤ ellT 5 (1 / 2) (1 / 2) := one_le_ellT (by norm_num)
    rw [rpow25] at hij
    nlinarith
  have hslice : ∀ b b' : Fin 2 → Zd 3 5,
      (∃ i j, (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b' i - b' j) : ℝ)) →
        ‖T5 b b'‖ ≤ 0 := by
    intro b b' hb'
    simp [T5, hspread b' hb']
  have hblock : ∀ b b' : Fin 2 → Zd 3 5,
      (∃ i j, (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ)) →
        ‖T5 b b'‖ ≤ 0 := by
    intro b b' hb
    simp [T5, hspread b hb]
  refine ⟨window_five, ?_⟩
  exact ugenPairQN_le_of_bounds (d := 3) (k := 2) 1 (1 / 2) 2 (by norm_num) le_rfl one_pos
    (by norm_num) two_pos (L := 5) (by norm_num) (g := 1 / 2) (by norm_num) (by norm_num) (W := 25)
    (ε := 1 / 2) (D₂ := 4) (by norm_num) (by norm_num) (by norm_num) hW5 hlog hLK (by norm_num)
    (s := 1 / 2) (t := 9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (E := 0)
    (by norm_num) mE_zero_im_ge (σ := ![true, false]) T5 (M' := 1) (δ' := 0) le_rfl
    (Real.rpow_nonneg (by norm_num) _) hT hz1 hz2 hslice hblock a

/-! #### Targets 4, 6a, 6b at `sz0`, `d = 3`, `m = 3`, `E = 0`, `t = u = 0`, large `n`

`x = 2(n+1)`, `W = x^5`, `L = 2x`, `lam = x^{-6}`; `ε = 1/5` (`W^ε = x`, below the `ℓ¹`-diameter `3x` of the torus),
`τ' = 1/10` (`W^{τ'} = √x ≤ x`, below the `L^∞`-diameter `x`): the windows of the decay clauses are attained by
the tuples of `farb`. -/

private theorem sz0_facts (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 ∧
      ((sz0.L n : ℕ) : ℝ) = 2 * (2 * ((n : ℝ) + 1)) ∧
      sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := by
  refine ⟨?_, ?_, rfl⟩
  · simp [sz0]
  · simp [sz0]; ring

private theorem lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1)

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

/-- The `L^∞` window is attained: `diam_∞ (0 ⧺ b') ≥ x ≥ ℓ_0 w`. -/
private theorem window_linf (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b b' : Fin (3 + 1) → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) 0 * w ≤ (STdiamInf (Fin.append b b') : ℝ) := by
  refine ⟨0, farb n, ?_⟩
  have h := Finset.le_sup (f := fun q : Fin (3 + 1 + (3 + 1)) × Fin (3 + 1 + (3 + 1)) =>
      zdistInf 3 (sz0.L n) (Fin.append (0 : Fin (3 + 1) → Zd 3 (sz0.L n)) (farb n) q.1 -
        Fin.append (0 : Fin (3 + 1) → Zd 3 (sz0.L n)) (farb n) q.2))
    (Finset.mem_univ (Fin.natAdd (3 + 1) 1, Fin.natAdd (3 + 1) 0))
  rw [Fin.append_right, Fin.append_right] at h
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistInf_farv] at h
  have h2 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (STdiamInf (Fin.append (0 : Fin (3 + 1) → Zd 3 (sz0.L n))
      (farb n)) : ℝ) := by exact_mod_cast h
  rw [ellT_sz0]
  push_cast at h2
  linarith

/-- `B_{0} = W^{-d} B_{0,0} ≤ 1` at `u = 0` (`W ≥ 2`). -/
private theorem Bctl_zero_le (n : ℕ) (hW : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ)) : sz0.Bctl n 0 ≤ 1 := by
  unfold Sizes.Bctl Bparam
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one, sub_zero, abs_one]
  have hL : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    have := sz0.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz0.L n)
  have h1 : (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 1 / 8 := by
    have : (8 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 3 := by nlinarith [sq_nonneg ((sz0.W n : ℝ))]
    calc (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 8⁻¹ := inv_anti₀ (by norm_num) this
      _ = 1 / 8 := by norm_num
  have h2 : (sz0.lam n ^ 2 + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (sz0.lam n)])
  have h3 : (((sz0.L n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have h4 : 0 ≤ (sz0.lam n ^ 2 + 1)⁻¹ + (((sz0.L n : ℕ) : ℝ) ^ 3)⁻¹ := by positivity
  calc (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * ((sz0.lam n ^ 2 + 1)⁻¹ + (((sz0.L n : ℕ) : ℝ) ^ 3)⁻¹)
      ≤ (1 / 8) * (1 + 1) := by gcongr
    _ ≤ 1 := by norm_num

/-- The constant of the mollifier of `QopAlgebra_mollifier_props` at `d = 3`, `m = 3`. -/
private noncomputable abbrev Cmol3 : ℝ := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)

/-- The constants `C_n`, `C_Q` of the instance. -/
private noncomputable abbrev Cn3 : ℝ := qProxyCn 3 3 1 2 Cmol3 (1 / 2)
private noncomputable abbrev CQ3 : ℝ := qProxyCQ 3 3 1 2 Cmol3 (1 / 2)

/-- The decay exponent `D = C_Q + 6 > m + 2 + C_Q` of the instance. -/
private noncomputable def Dq : ℝ := CQ3 + 6

/-- The threshold `W₀` of the instance (`d = 3`, `m = 3`, `Λ_g = 1`, `K = 2`, `C₀ = 4`, `ε = 1/5`, `D = Dq`). -/
private noncomputable def R0 : ℝ := qProxyW0 3 3 1 2 Cmol3 (1 / 2) 4 (1 / 5) Dq

/-- All the numeric hypotheses of targets 4 and 6 at `sz0`, `n` with `2 (n + 1) ≥ max W₀ 10`, `ε = 1/5`,
`τ' = 1/10`, `K = 2`, `C₀ = 4`, `u = 0`, `w = 1/2`, `E = 0`. -/
private theorem sz0_numeric (n : ℕ) (hx : max R0 10 ≤ 2 * ((n : ℝ) + 1)) :
    1 < ((sz0.W n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    Real.log ((sz0.L n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ) ∧
    ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    R0 ≤ ((sz0.W n : ℕ) : ℝ) ∧ 0 < sz0.lam n ∧ sz0.lam n ≤ 1 ∧
    (1 / 2 : ℝ) ≤ 1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ∧
    (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (1 - 1 / 2) / (1 - 0) ∧
    4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0) ≤ ((sz0.W n : ℕ) : ℝ) ^ (4 : ℝ) := by
  obtain ⟨hW, hL, hlam⟩ := sz0_facts n
  set x : ℝ := 2 * ((n : ℝ) + 1) with hxdef
  have hx10 : 10 ≤ x := (le_max_right _ _).trans hx
  have hxR : R0 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxW : ((sz0.W n : ℕ) : ℝ) = x ^ 5 := hW
  have hx5 : 10 ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx10 5
  have h3 : (10 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx10 3
  have h7 : (10 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx10 7
  have h20 : (10 : ℝ) ^ 20 ≤ x ^ 20 := pow_le_pow_left₀ (by norm_num) hx10 20
  have hW2 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by rw [hxW]; nlinarith
  have hlam0 : 0 < sz0.lam n := lam_pos_n n
  have hlam1 : sz0.lam n ≤ 1 := lam_le_one n
  have hW15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  refine ⟨by rw [hxW]; nlinarith, ?_, ?_, ?_, ?_, ?_, hlam0, hlam1, ?_, ?_, ?_⟩
  · rw [hW15]; linarith
  · rw [hW15, hL, Real.log_mul (by norm_num) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x by linarith)
    have h2 := Real.log_two_lt_d9
    linarith
  · rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * 2 = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hL]
    have h10 : x ^ 10 = x ^ 3 * x ^ 7 := by ring
    have h8 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h7 (pow_nonneg hx0 3)]
  · rw [hW15, hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    have hs3 : (3 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
    push_cast
    nlinarith
  · rw [hxW]
    exact hxR.trans (le_self_pow₀ hx1 (by norm_num))
  · have hL4 : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by rw [hL]; linarith
    rw [le_sub_comm, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (sz0.lam n)]
  · calc (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hW2
      _ = (1 - 1 / 2) / (1 - 0) := by norm_num
  · rw [etaT_zero_zero, div_one, hxW, rpow_pow5 hx0, show (5 : ℝ) * 4 = ((20 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    have hB1 := Bctl_zero_le n hW2
    have hB0 : 0 ≤ sz0.Bctl n 0 := (STBctl_pos sz0 n (by norm_num)).le
    have hB8 : (sz0.Bctl n 0) ^ (2 * (3 + 1)) ≤ 1 := pow_le_one₀ hB0 hB1
    nlinarith

/-- The closed form of `qvFormQN_le_of_bounds` at the data of the instance (`v = u = 0`, `w = 1/2`, `m = 3`,
`Λ_g = 1`, `κ' = 1/2`, `K = 2`, `ε = 1/5`, `D = Dq`). -/
private noncomputable def bdQ (n : ℕ) (Mee : ℝ) : ℝ :=
  (((sz0.W n : ℕ) : ℝ) ^ (qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * (1 / 5 : ℝ)) *
      ((sz0.lam n ^ 2 + |1 - 0|) / (sz0.lam n ^ 2 + |1 - 1 / 2|)) ^ (3 + 1)) *
    ((((sz0.W n : ℕ) : ℝ) ^ (qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * (1 / 5 : ℝ)) *
        ((sz0.lam n ^ 2 + |1 - 0|) / (sz0.lam n ^ 2 + |1 - 1 / 2|)) ^ (3 + 1)) *
      (((sz0.W n : ℕ) : ℝ) ^ (2 * Cn3 * (1 / 5 : ℝ)) * Mee + ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) +
      ((sz0.W n : ℕ) : ℝ) ^ qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) +
    ((sz0.W n : ℕ) : ℝ) ^ qProxy4C 3 (3 + 1) 1 (1 / 2) 2 *
      (((sz0.W n : ℕ) : ℝ) ^ (3 + 1) * ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3))

private theorem hD_inst : ((3 : ℕ) : ℝ) + 2 + CQ3 < Dq := by
  unfold Dq
  push_cast
  linarith

/-- `0 ∈ GoodSetN` at `u = 0` with the levels `Γ = 4`, `Λ = 100`, `Φ = 1` (`Γ² Λ = 1600 ≥ 4 · 2^8`). -/
private theorem zero_mem_inst (n : ℕ) (hlam1 : sz0.lam n ≤ 1) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) Dq := by
  refine zero_mem_goodSetN_of_levels sz0 n (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  have h1 : (1 + sz0.lam n ^ 2) ≤ 2 := by nlinarith [sq_nonneg (sz0.lam n), lam_pos_n n]
  have h2 : (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 2 ^ (2 * (3 + 1)) :=
    pow_le_pow_left₀ (by positivity) h1 _
  push_cast
  calc 4 * (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 4 * 2 ^ (2 * (3 + 1)) := by gcongr
    _ ≤ 4 * (4 * 100) := by norm_num

/-- `n` large enough for all of `sz0_numeric` and the windows. -/
private theorem exists_big_n : ∃ n : ℕ, max R0 10 ≤ 2 * ((n : ℝ) + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max R0 10)
  exact ⟨n, by have := Nat.cast_nonneg (α := ℝ) n; linarith⟩

/-- `W^{τ'} ≤ x` and `W^ε ≤ x` at `τ' = 1/10`, `ε = 1/5`. -/
private theorem W_rpow_le_x (n : ℕ) (hx : max R0 10 ≤ 2 * ((n : ℝ) + 1)) :
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * ((n : ℝ) + 1) ∧
      ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
  obtain ⟨-, -, -, -, h3, -⟩ := sz0_numeric n hx
  obtain ⟨hW, -, -⟩ := sz0_facts n
  have hx10 : 10 ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ 2 * ((n : ℝ) + 1) := by linarith
  have h15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := by
    rw [hW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  have hpos : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by positivity) _
  refine ⟨?_, h15.le⟩
  push_cast at h3
  linarith

/-- **Instance of `qvFormQN_le_of_goodSetN`** (target 6b) at `sz0`, `d = 3`, `m = 3` (`k = 4`), `σ = (+,-,+,-)`,
`Λ_g = 1`, `κ' = 1/2`, `K = 2`, the merged mollifier (`C = (1 + 40·9)·6^9`, `c = 1/2`), `ε = 1/5`, `τ' = 1/10`,
`C₀ = 4`, `D = C_Q + 6`, `E = 0`, `u = 0`, `w = 1/2`, `H = 0 ∈ GoodSetN` with the levels `(Γ, Λ, Φ) = (4, 100, 1)`,
at an `n` with `W_n ≥ W₀` (`qProxyW0`): every hypothesis is discharged; `Φ` is arbitrary (here `1`).  The far clause
(Vb) is exercised: there is a pair `(b, b')` with `ℓ_0 W^{τ'} ≤ diam_∞(b ⧺ b')` (the window fits in the torus). -/
theorem qvFormQN_le_of_goodSetN_instance :
    ∃ n : ℕ,
      (∃ b b' : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf (Fin.append b b') : ℝ)) ∧
      ∀ a : Fin (3 + 1) → Zd 3 (sz0.L n),
        qvFormQN sz0 n (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 0 (1 / 2) sigma4 0 a ≤
          bdQ n (4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) := by
  obtain ⟨n, hx⟩ := exists_big_n
  obtain ⟨hWx, -⟩ := W_rpow_le_x n hx
  refine ⟨n, window_linf n hWx, fun a => ?_⟩
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW₀, hlam0, hlam1, hwL, hWt, hMee⟩ := sz0_numeric n hx
  exact qvFormQN_le_of_goodSetN (d := 3) (m := 3) (by norm_num) (by norm_num) 1 (1 / 2) 2 Cmol3
    (1 / 2) one_pos (by norm_num) two_pos (by positivity) (by norm_num) sz0 n hlam0 hlam1
    (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 4) (D := Dq) hW (by norm_num) (by norm_num) hWε hlog hLK hdW
    (by norm_num) hD_inst hW₀
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) hlam0) (u := 0) (w := 1 / 2) le_rfl
    (by norm_num) hwL hWt (E := 0) (by norm_num) mE_zero_im_ge (σ := sigma4) (Γ := 4) (Λ := 100)
    (Φ := 1) (zero_mem_inst n hlam1) hMee a

/-- **Instance of `qvFormQN_le_of_bounds`** (target 6a) at the same data: the bounds on `𝓔 ⊗ 𝓔` are the clauses
(D4) and (Vb) of the membership `0 ∈ GoodSetN`; `M_ee = 4 (4 · 100) B_0^8 / η_0`. -/
theorem qvFormQN_le_of_bounds_instance :
    ∃ n : ℕ,
      (∃ b b' : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf (Fin.append b b') : ℝ)) ∧
      ∀ a : Fin (3 + 1) → Zd 3 (sz0.L n),
        qvFormQN sz0 n (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 0 (1 / 2) sigma4 0 a ≤
          bdQ n (4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) := by
  obtain ⟨n, hx⟩ := exists_big_n
  obtain ⟨hWx, -⟩ := W_rpow_le_x n hx
  refine ⟨n, window_linf n hWx, fun a => ?_⟩
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW₀, hlam0, hlam1, hwL, hWt, hMee⟩ := sz0_numeric n hx
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := zero_mem_inst n hlam1
  exact qvFormQN_le_of_bounds (d := 3) (m := 3) (by norm_num) (by norm_num) 1 (1 / 2) 2 Cmol3
    (1 / 2) one_pos (by norm_num) two_pos (by positivity) (by norm_num) sz0 n hlam0 hlam1
    (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 4) (D := Dq) hW (by norm_num) (by norm_num) hWε hlog hLK hdW
    (by norm_num) hD_inst hW₀
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) hlam0) (v := 0) (w := 1 / 2) le_rfl
    (by norm_num) hwL hWt (E := 0) (by norm_num) mE_zero_im_ge (σ := sigma4) 0
    (Mee := 4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) hMee
    (fun b b' => hD4 sigma4 b b') (fun b b' hfar => hVb sigma4 b b' hfar) a

/-- **Instance of `qqTensorBoundsN`** (target 4) at `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `g = lam_n`), `d = 3`,
`m = 3`, `Λ_g = 1`, `K = 2`, the merged mollifier at `t = 0` (`ℓ_0 = 1`), `ε = 1/5`, `τ' = 1/10`, `C₀ = 4`, `D = C_Q + 6`,
the nonzero delta tensor `T = 1_{(0,0)}` (`M_ee = 1`, support of `L^∞`-spread `0`), at an `n` with `W_n ≥ W₀`
(`qProxyW0`): every hypothesis is discharged; the windows of (ii), (iii) are attained (a tuple of `ℓ¹`-spread
`3x ≥ W^ε ℓ_0`). -/
theorem qqTensorBoundsN_instance :
    ∃ n : ℕ, deltaTensor (d := 3) (L := sz0.L n) 3 ≠ 0 ∧
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) *
        ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧
      (∀ b b' : Fin (3 + 1) → Zd 3 (sz0.L n),
        ‖qqTensorN (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (deltaTensor 3) b b'‖ ≤
          ((sz0.W n : ℕ) : ℝ) ^ (2 * Cn3 * (1 / 5 : ℝ)) * 1 + ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) ∧
      (∀ b : Fin (3 + 1) → Zd 3 (sz0.L n),
        EKFastDecay (d := 3) (L := sz0.L n) (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) (Dq - CQ3)
          (fun b' => qqTensorN (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (deltaTensor 3) b b')) ∧
      (∀ b' b : Fin (3 + 1) → Zd 3 (sz0.L n),
        (∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤
          (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) →
          ‖qqTensorN (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (deltaTensor 3) b b'‖ ≤
            ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) := by
  obtain ⟨n, hx⟩ := exists_big_n
  obtain ⟨-, hWx⟩ := W_rpow_le_x n hx
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW₀, hlam0, hlam1, hwL, hWt, hMee⟩ := sz0_numeric n hx
  have hW1 : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hW.le
  have hDn : Cn3 + 2 < Dq := by
    have : (0 : ℝ) < qProxyCn 3 3 1 2 Cmol3 (1 / 2) :=
      qProxyCn_pos (by norm_num) 3 one_pos two_pos (by positivity) (by norm_num)
    simp only [Dq, CQ3, Cn3, qProxyCQ]
    linarith
  have hT : ∀ b b' : Fin (3 + 1) → Zd 3 (sz0.L n), ‖deltaTensor (d := 3) (L := sz0.L n) 3 b b'‖ ≤ 1 := by
    intro b b'
    unfold deltaTensor
    split_ifs <;> simp
  have hTfar : ∀ b b' : Fin (3 + 1) → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) 0 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
        (STdiamInf (Fin.append b b') : ℝ) →
        ‖deltaTensor (d := 3) (L := sz0.L n) 3 b b'‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (-Dq) := by
    intro b b' hfar
    by_cases hb : b = 0 ∧ b' = 0
    · exfalso
      obtain ⟨rfl, rfl⟩ := hb
      rw [diam_append_zero, Nat.cast_zero] at hfar
      have h1 : 0 < ellT (sz0.L n) (sz0.lam n) 0 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) :=
        mul_pos (ellT_pos (by have := sz0.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz0.L n)))
          (Real.rpow_pos_of_pos (by linarith) _)
      linarith
    · have : deltaTensor (d := 3) (L := sz0.L n) 3 b b' = 0 := by simp [deltaTensor, hb]
      rw [this]
      simpa using Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ)) _
  have h := qqTensorBoundsN (d := 3) (m := 3) (by norm_num) 1 2 Cmol3 (1 / 2) one_pos two_pos
    (by positivity) (by norm_num) (L := sz0.L n) (sz0.three_le_L n) (g := sz0.lam n) hlam0 hlam1
    (W := ((sz0.W n : ℕ) : ℝ)) (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 4) (D := Dq) hW (by norm_num)
    (by norm_num) hWε hLK hdW (by norm_num) hDn hW₀
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) hlam0) (t := 0) le_rfl
    (by norm_num) (deltaTensor 3) (Mee := 1)
    (Real.one_le_rpow hW1 (by norm_num)) hT hTfar
  refine ⟨n, ?_, window_l1 n hWx, h⟩
  intro h0
  have := congrFun (congrFun h0 0) 0
  simp [deltaTensor] at this

end QProxyInst

end RBM.Ind

end

#print axioms RBM.Ind.qqTensorN
#print axioms RBM.Ind.qvFormQN
#print axioms RBM.Ind.zVecQN
#print axioms RBM.Ind.yVecQN
#print axioms RBM.Ind.martIncQN_ae_eq
#print axioms RBM.Ind.qv_at_propagatorQ
#print axioms RBM.Ind.qqTensorN_sumZero
#print axioms RBM.Ind.azumaSubGQ_ugenN
#print axioms RBM.Ind.azumaSubGQ_gridExitN
#print axioms RBM.Ind.qProxyCn
#print axioms RBM.Ind.qProxyCQ
#print axioms RBM.Ind.qProxy4C
#print axioms RBM.Ind.qProxyW0
#print axioms RBM.Ind.qProxyCn_pos
#print axioms RBM.Ind.qProxy4C_pos
#print axioms RBM.Ind.qProxyCQ_pos
#print axioms RBM.Ind.qProxyW0_ge_two
#print axioms RBM.Ind.qqTensorBoundsN
#print axioms RBM.Ind.ugenPairQN_le_of_bounds
#print axioms RBM.Ind.qvFormQN_le_of_bounds
#print axioms RBM.Ind.qvFormQN_le_of_goodSetN
#print axioms RBM.Ind.yMomentsQUnifN
#print axioms RBM.Ind.QProxyInst.martIncQN_ae_eq_instance
#print axioms RBM.Ind.QProxyInst.Mx
#print axioms RBM.Ind.QProxyInst.qv_at_propagatorQ_instance
#print axioms RBM.Ind.QProxyInst.deltaTensor
#print axioms RBM.Ind.QProxyInst.Adelta
#print axioms RBM.Ind.QProxyInst.Adelta_ne
#print axioms RBM.Ind.QProxyInst.Adelta_not_sumZero
#print axioms RBM.Ind.QProxyInst.qqTensorN_sumZero_instance
#print axioms RBM.Ind.QProxyInst.azumaSubGQ_ugenN_instance
#print axioms RBM.Ind.QProxyInst.azumaSubGQ_gridExitN_instance
#print axioms RBM.Ind.QProxyInst.azumaSubGQ_gridExitN_instance_zero
#print axioms RBM.Ind.QProxyInst.yMomentsQUnifN_instance_pos
#print axioms RBM.Ind.QProxyInst.yMomentsQUnifN_instance
#print axioms RBM.Ind.QProxyInst.w5
#print axioms RBM.Ind.QProxyInst.w5_sumZero
#print axioms RBM.Ind.QProxyInst.w5_ne
#print axioms RBM.Ind.QProxyInst.T5
#print axioms RBM.Ind.QProxyInst.T5_ne
#print axioms RBM.Ind.QProxyInst.ugenPairQN_le_of_bounds_instance
#print axioms RBM.Ind.QProxyInst.qvFormQN_le_of_goodSetN_instance
#print axioms RBM.Ind.QProxyInst.qvFormQN_le_of_bounds_instance
#print axioms RBM.Ind.QProxyInst.qqTensorBoundsN_instance
