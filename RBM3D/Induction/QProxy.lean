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
import RBM3D.Chain.QGridGen
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.GridRepTailGen2
import RBM3D.Chain.GridGoodGen
import RBM3D.Chain.NQGood1Gen

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

## T2498 (row U3s3a, in place): the vocabulary and the targets over a flow carrier

Generic twins over `Cm : Step2Mat sz` (kernel `Step2Gen_UN`, law `Cm.Pp`, walk `Cm.Hpath`), namespace `RBM.Ind`, `open RBM.BA`:
* **Target 1 (D1).** `QProxyG_KerEK4` (EK-4 `(sum_res_2)` for `Step2Gen_UN C` at the kernel coupling `gK`, explicit constant `C4`, `L^d ≤ W^{KL}`),
  its family form `QProxyG_KerEK4Fam`, and the band discharge `qProxyG_kerEK4_band_at`, `qProxyG_kerEK4_band` (`C4 = qProxy4C d k 𝔡⁻¹ (min κ (4/5)) KL`).
* **Target 2.** `qvFormQNg`, `zVecQNg`, `yVecQNg`, `martIncQNg_ae_eq`, `qv_at_propagatorQg`, `azumaSubGQ_ugenNg`, `azumaSubGQ_gridExitNg`
  (band bridges `qProxy_qvFormQN_eq_g`, `qProxy_zVecQN_eq_g`, `qProxy_yVecQN_eq_g`).
* **Target 3.** `ugenPairQNg_le_of_bounds`, `qvFormQNg_le_of_bounds` (D1 at `gK`, the comparison R1 to the size level `sz.lam`, two constants
  `C4 ≤ Cv`, two radii `ε₁`, `ε` with `√A W^{ε₁} ≤ W^ε`), `yMomentsQUnifNg`.
* The band statements read outside this file (`martIncQN_ae_eq`, `azumaSubGQ_gridExitN`, `qvFormQN_le_of_bounds`, `yMomentsQUnifN`) keep name and type; the
  last three are corollaries of the generic theorems at `bandStep2Mat`; the band proofs of `qv_at_propagatorQ`, `azumaSubGQ_ugenN`, `ugenPairQN_le_of_bounds` and
  of the private chain behind them are replaced by the generic ones (no reader).  The compiled instances (§11 of the previous layout) are in `Induction/QProxy2`.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private NQGood1Gen_norm_UN_row from RBM3D.Chain.NQGood1Gen

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Green RBM.BA

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

/-! ### 1g. The vocabulary over a carrier `Cm : Step2Mat sz` (generic twins, D4; band bridges) -/

section VocabG

variable {d : ℕ} {sz : Sizes d}

def qvFormQNg (Cm : Step2Mat sz) (n : ℕ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (v w : ℝ)
    (σ : Fin (m + 1) → Bool) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)) : ℝ :=
  (∑ b : Fin (m + 1) → Zd d (sz.L n), ∑ b' : Fin (m + 1) → Zd d (sz.L n),
    (∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) v w (a i) (b i)) *
      (∏ i, Step2Gen_uKer Cm.toFlowFM n (!σ i) (!σ (finRotate (m + 1) i)) v w (a i) (b' i)) *
      qqTensorN ϑ v (fun c c' => STeeMg Cm n v M σ c c') b b').re

def zVecQNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n (j + 1)) (ZvecNg Cm s t K n j σ ω)

def yVecQNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n (j + 1)) (YvecNg Cm s t K n j σ ω)

variable (sz) (E : ℕ → ℝ)

theorem qProxy_qvFormQN_eq_g (n : ℕ) (hE : |E n| ≤ 2) {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin (m + 1) → Zd d (sz.L n)) :
    qvFormQN sz n ϑ (E n) v w σ M a = qvFormQNg (bandStep2Mat sz E) n ϑ v w σ M a := by
  have hK4 := (gridRepTailGen_ker_band sz E n hE).2.2.2
  unfold qvFormQN qvFormQNg
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : ∏ i : Fin (m + 1), Step2Gen_uKer (bandStep2Mat sz E).toFlowFM n (!σ i) (!σ (finRotate (m + 1) i)) v w (a i) (b' i) =
      (starRingEnd ℂ) (∏ i : Fin (m + 1), Step2Gen_uKer (bandStep2Mat sz E).toFlowFM n (σ i) (σ (finRotate (m + 1) i)) v w
        (a i) (b' i)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => hK4 _ _ v w hw0 hw1 _ _
  rw [hconj]
  have hfm : (bandStep2Mat sz E).toFlowFM = bandFM sz E := rfl
  simp only [hfm, Step2Kern_uKer_band]
  rfl

theorem qProxy_zVecQN_eq_g (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    zVecQN sz E s t K n j ϑ σ ω = zVecQNg (bandStep2Mat sz E) s t K n j ϑ σ ω := by
  unfold zVecQN zVecQNg; rw [bandStep2_ZvecN]

theorem qProxy_yVecQN_eq_g (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (σ : Fin (m + 1) → Bool) (ω : PathΩ sz) :
    yVecQN sz E s t K n j ϑ σ ω = yVecQNg (bandStep2Mat sz E) s t K n j ϑ σ ω := by
  unfold yVecQN yVecQNg; rw [bandStep2_YvecN]

end VocabG

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

section Gen3

variable {d : ℕ} {sz : Sizes d}

theorem martIncQNg_ae_eq {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hKL : HierDriftGen_KLink Cm n) (hs : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n)
    {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∀ᵐ ω ∂Cm.Pp, martIncQNg Cm s t K n ϑ σ j ω a = zVecQNg Cm s t K n j ϑ σ ω a + yVecQNg Cm s t K n j ϑ σ ω a := by
  filter_upwards [QGridGen_condExp_aTrueQNg hL hW s t K n j hKL hs hst ht1 hK hj ϑ σ a] with ω h
  have h1 : (fun c => ZvecNg Cm s t K n j σ ω c + YvecNg Cm s t K n j σ ω c) =
      fun c => AvecNg Cm s t K n (j + 1) σ ω c -
        Cm.Pp[fun ω' => AvecNg Cm s t K n (j + 1) σ ω' c | filt sz j] ω := by
    funext c
    simp only [YvecNg, martIncNg]
    ring
  have h2 := qProxy_Qop_add ϑ (gridTime s t K n (j + 1)) (ZvecNg Cm s t K n j σ ω) (YvecNg Cm s t K n j σ ω) a
  have h3 := qProxy_Qop_sub ϑ (gridTime s t K n (j + 1)) (AvecNg Cm s t K n (j + 1) σ ω)
    (fun c => Cm.Pp[fun ω' => AvecNg Cm s t K n (j + 1) σ ω' c | filt sz j] ω) a
  unfold zVecQNg yVecQNg
  rw [← h2, h1, h3]
  unfold martIncQNg
  rw [h]
  rfl

end Gen3

/-! ## 4. Target 3: `𝒫 ∘ 𝒬_t = 0` in each copy, and the variance identity of the propagated `𝒬`-family over a carrier -/

section Gen4

variable {d : ℕ} {sz : Sizes d}

/-- `qvFormQNg` as the conjugate pairing (K4). -/
private theorem qProxy_qvFormQNg_eq {Cm : Step2Mat sz} {n : ℕ} (hK : GridRepTailGen_Ker Cm.toFlowFM n) {v w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin (m + 1) → Zd d (sz.L n)) :
    qvFormQNg Cm n ϑ v w σ M a = (∑ b : Fin (m + 1) → Zd d (sz.L n), ∑ b' : Fin (m + 1) → Zd d (sz.L n),
      (∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) v w (a i) (b i)) *
        (starRingEnd ℂ) (∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) v w (a i) (b' i)) *
        qqTensorN ϑ v (fun c c' => STeeMg Cm n v M σ c c') b b').re := by
  have hK4 := hK.2.2.2
  unfold qvFormQNg
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : ∏ i, Step2Gen_uKer Cm.toFlowFM n (!σ i) (!σ (finRotate (m + 1) i)) v w (a i) (b' i) =
      (starRingEnd ℂ) (∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) v w (a i) (b' i)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => hK4 _ _ v w hw0 hw1 _ _
  rw [hconj]

/-- **`qv_at_propagatorQg`**: `qvPropagatedNg` at the transposed weights of `𝒬_u`. -/
theorem qv_at_propagatorQg {Cm : Step2Mat sz} {g : ℕ → ℝ} (hQV : QVPropagatedNg Cm g) {n : ℕ}
    (hK : GridRepTailGen_Ker Cm.toFlowFM n) (u w : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (g n) c : ℝ) *
        ‖∑ b : Fin (m + 1) → Zd d (sz.L n),
          (∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) u w (a i) (b i)) *
          STQop (d := d) ϑ u (fun b'' => RBM.Ind.dirDerivN (fun H => Cm.LM n u H σ b'') M
            (coordinateMatrix d (sz.L n) (sz.W n) c)) b‖ ^ 2 ≤
      ((m + 1 : ℕ) : ℝ) * qvFormQNg Cm n ϑ u w σ M a := by
  set κ : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b =>
    ∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) u w (a i) (b i) with hκ
  have h := hQV n u hu0 hu1 M hM (m + 1) (by omega) σ (qProxy_wts ϑ u κ)
  have hLHS : ∀ c : CoordF d (sz.L n) (sz.W n), ∑ b : Fin (m + 1) → Zd d (sz.L n), κ b *
      STQop (d := d) ϑ u (fun b'' => RBM.Ind.dirDerivN (fun H => Cm.LM n u H σ b'') M
        (coordinateMatrix d (sz.L n) (sz.W n) c)) b =
      ∑ b : Fin (m + 1) → Zd d (sz.L n), qProxy_wts ϑ u κ b *
        RBM.Ind.dirDerivN (fun H => Cm.LM n u H σ b) M (coordinateMatrix d (sz.L n) (sz.W n) c) :=
    fun c => qProxy_sum_Qop ϑ u κ _
  rw [qProxy_qvFormQNg_eq hK hw0 hw1]
  have e := qProxy_sum_qq ϑ u κ (fun c c' => STeeMg Cm n u M σ c c')
  rw [e]
  simp only [hκ] at hLHS ⊢
  simp only [hLHS]
  exact h

end Gen4

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

variable {d : ℕ} {sz : Sizes d}

/-- **`azumaSubGQ_ugenNg`**. -/
theorem azumaSubGQ_ugenNg {Cm : Step2Mat sz} [IsProbabilityMeasure Cm.Pp] {E g s t : ℕ → ℝ} {K : ℕ → ℕ}
    (h : AzumaSubGNg Cm g s t K) (hL : StepDecompGen_LoopForm Cm E) (hQV : QVPropagatedNg Cm g)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (n m : ℕ) (hKer : GridRepTailGen_Ker Cm.toFlowFM n) (hm : 1 ≤ m)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (τ : PathΩ sz → ℕ)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
    (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) (hG : ∀ ω j, j < τ ω → Cm.Hpath s t K n j ω ∈ G j)
    (p : ℕ) (hp : p ≤ K n) (a : Fin (m + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s t K n * (((m + 1 : ℕ) : ℝ) * qvFormQNg Cm n ϑ (gridTime s t K n (j + 1)) (gridTime s t K n p) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopNg Cm σ (gridTime s t K n) τ (fun j ω => zVecQNg Cm s t K n j ϑ σ ω) p a j Q := by
  have hKn : K n ≠ 0 := by omega
  have hu0 : 0 ≤ gridTime s t K n (j + 1) := qProxy_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
  have hu1 : gridTime s t K n (j + 1) < 1 :=
    (qProxy_gridTime_le s t K n (hst n) (show j + 1 ≤ K n by omega) hKn).trans_lt (ht1 n)
  have hw0 : 0 ≤ gridTime s t K n p := qProxy_gridTime_nonneg s t K n (hs0 n) (hst n) p
  have hw1 : gridTime s t K n p < 1 := (qProxy_gridTime_le s t K n (hst n) hp hKn).trans_lt (ht1 n)
  have hΔ : 0 ≤ gridStep s t K n := qProxy_gridStep_nonneg (hst n)
  set κ : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b =>
    ∏ i, Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) (gridTime s t K n (j + 1)) (gridTime s t K n p)
      (a i) (b i) with hκ
  have hΦ : ∀ b, HermTestFun sz n (loopFamNg Cm s t K n j σ b) := fun b => by
    change HermTestFun sz n (fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b)
    rw [StepDecompGen_LM_eq hL]
    exact (hermTestFunLoopNOf sz (m + 1) n (Cm.m n) (E n) _ (hL n).1 hu1 σ b).1
  have hcomb : ∀ ω' : PathΩ sz,
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n p) (zVecQNg Cm s t K n j ϑ σ ω') a =
      ∑ c, qProxy_wts ϑ (gridTime s t K n (j + 1)) κ c *
        ZfamNg Cm s t K n j (loopFamNg Cm s t K n j σ) ω' c := by
    intro ω'
    exact qProxy_sum_Qop ϑ (gridTime s t K n (j + 1)) κ (ZvecNg Cm s t K n j σ ω')
  have hz := h n (loopFamNg Cm s t K n j σ) hΦ (qProxy_wts ϑ (gridTime s t K n (j + 1)) κ) τ G hτ hG j Q
    (fun M hMG hMH => by
      have h3 := qv_at_propagatorQg hQV hKer (gridTime s t K n (j + 1)) (gridTime s t K n p) hu0 hu1 hw0 hw1 M hMH m hm ϑ σ a
      have h4 : ∀ c : CoordF d (sz.L n) (sz.W n),
          ∑ b, qProxy_wts ϑ (gridTime s t K n (j + 1)) κ b *
              RBM.Ind.dirDerivN (loopFamNg Cm s t K n j σ b) M (coordinateMatrix d (sz.L n) (sz.W n) c) =
            ∑ b : Fin (m + 1) → Zd d (sz.L n), κ b * STQop (d := d) ϑ (gridTime s t K n (j + 1))
              (fun b'' => RBM.Ind.dirDerivN (fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b'') M
                (coordinateMatrix d (sz.L n) (sz.W n) c)) b := fun c =>
        (qProxy_sum_Qop ϑ (gridTime s t K n (j + 1)) κ _).symm
      simp only [h4]
      exact (mul_le_mul_of_nonneg_left h3 hΔ).trans (hQ M hMG hMH))
  have hfun : (fun ω' : PathΩ sz => Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n p)
      (zVecQNg Cm s t K n j ϑ σ ω') a) =
      fun ω => ∑ b, qProxy_wts ϑ (gridTime s t K n (j + 1)) κ b *
        ZfamNg Cm s t K n j (loopFamNg Cm s t K n j σ) ω b := funext hcomb
  unfold SubGaussStopNg
  rw [hfun]
  exact hz

theorem azumaSubGQ_gridExitNg {Cm : Step2Mat sz} [IsProbabilityMeasure Cm.Pp] {E g lam' s v : ℕ → ℝ} {K : ℕ → ℕ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (h : AzumaSubGNg Cm g s v K) (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hQV : QVPropagatedNg Cm g)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (n m : ℕ) (hKer : GridRepTailGen_Ker Cm.toFlowFM n) (hm : 1 ≤ m)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) (hG : ∀ j, MeasurableSet (G j))
    (p : ℕ) (hp : p ≤ K n) (a : Fin (m + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p) (Q : ℝ≥0)
    (hQ : ∀ M ∈ G j, M.IsHermitian →
      gridStep s v K n * (((m + 1 : ℕ) : ℝ) * qvFormQNg Cm n ϑ (gridTime s v K n (j + 1)) (gridTime s v K n p) σ M a) ≤ (Q : ℝ)) :
    SubGaussStopNg Cm σ (gridTime s v K n) (gridExitTauNg Cm s v K n G)
      (fun j ω => zVecQNg Cm s v K n j ϑ σ ω) p a j Q :=
  azumaSubGQ_ugenNg h hL hQV hs0 hsv hv1 n m hKer hm ϑ σ (gridExitTauNg Cm s v K n G) G
    (fun j => gridExitTauNg_measurableSet hW hG j) (fun ω j hj => mem_of_lt_gridExitTauNg hj) p hp a j hj Q hQ

end AzumaQ

/-- **`azumaSubGQ_gridExitN`** (name and type unchanged): the corollary of `azumaSubGQ_gridExitNg` at `bandStep2Mat sz E`
(`LoopForm`, `WalkForm`, `qvPropagatedNg`, `azumaSubGNg`, K1-K4 by the band discharges; `qvFormQN = qvFormQNg`, `zVecQN = zVecQNg`). -/
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
      (fun j ω => zVecQN sz E s v K n j ϑ σ ω) p a j Q := by
  have hKn : K n ≠ 0 := by omega
  have hL := stepDecompGen_loopForm_band sz E hE
  have hW := stepDecompGen_walkForm_band sz E
  have hw0 : 0 ≤ gridTime s v K n p := qProxy_gridTime_nonneg s v K n (hs0 n) (hsv n) p
  have hw1 : gridTime s v K n p < 1 := (qProxy_gridTime_le s v K n (hsv n) hp hKn).trans_lt (hv1 n)
  have hkey := azumaSubGQ_gridExitNg (azumaSubGNg (bandStep2Mat sz E) hW s v K) hL hW
    (qvPropagatedNg (bandStep2Mat sz E) E sz.lam hL (fun _ => rfl)) hs0 hsv hv1 n m
    (gridRepTailGen_ker_band sz E n (hE n).le) hm ϑ σ G hG p hp a j hj Q
    (fun M hM hMH => by
      rw [← qProxy_qvFormQN_eq_g sz E n (hE n).le hw0 hw1]
      exact hQ M hM hMH)
  have hZ : (fun j ω => zVecQN sz E s v K n j ϑ σ ω) =
      fun j ω => zVecQNg (bandStep2Mat sz E) s v K n j ϑ σ ω :=
    funext fun j => funext fun ω => qProxy_zVecQN_eq_g sz E s v K n j ϑ σ ω
  rw [hZ]
  exact (bandStep2_SubGaussStopN sz E σ _ _ _ p a j Q).2 hkey

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

section D1

def QProxyG_KerEK4 {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (KL C4 : ℝ) (n : ℕ) : Prop :=
  1 < ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL →
  ∀ ε D : ℝ, 0 < ε → ε < 1 → 1 < D → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 →
      (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ σ : Fin k → Bool, ∀ A : (Fin k → Zd d (sz.L n)) → ℂ,
        EKFastDecay (gK n) s ((sz.W n : ℕ) : ℝ) ε D A → EKSumZero A →
        ‖Step2Gen_UN C n σ s t A‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (C4 * ε) * ((gK n ^ 2 + |1 - s|) / (gK n ^ 2 + |1 - t|)) ^ k * ‖A‖ +
            ((sz.W n : ℕ) : ℝ) ^ (-D + C4)

def QProxyG_KerEK4Fam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ ε 𝔡 KL : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < KL → ∃ C4 : ℝ, 0 < C4 ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, QProxyG_KerEK4 (mk sz z) (gK sz z) k KL C4 n

theorem qProxyG_kerEK4_band_at {d k : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) {Λ κ' KL : ℝ} (hΛ : 0 < Λ)
    (hκ' : 0 < κ') (hKL : 0 < KL) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ) (hE : |E n| ≤ 2) (hκm : κ' ≤ (mE (E n)).im) :
    QProxyG_KerEK4 (bandFM sz E) sz.lam k KL (qProxy4C d k Λ κ' KL) n := by
  intro hW hLK ε D hε0 hε1 hD hWε hlog s t hs hst ht hWt σ A hA hsum
  have hC : qProxy4C d k Λ κ' KL = Classical.choose (ekSumDecay2_holds d k Λ κ' (prop5Decay_holds d Λ) (prop5Short_holds d Λ κ')
      (prop6Diff1_holds d Λ κ' (1 / 2)) hd hk hΛ hκ' KL hKL) := by
    unfold qProxy4C; rw [dite_eq_left_of_eq_true (eq_true ⟨hd, hk, hΛ, hκ', hKL⟩)]
  obtain ⟨-, hEK⟩ := Classical.choose_spec (ekSumDecay2_holds d k Λ κ' (prop5Decay_holds d Λ) (prop5Short_holds d Λ κ')
    (prop6Diff1_holds d Λ κ' (1 / 2)) hd hk hΛ hκ' KL hKL)
  rw [hC, ← bandStep2_Ugen]
  exact hEK (sz.L n) (sz.three_le_L n) (sz.lam n) hg hgΛ _ ε D hW hε0 hε1 hD hWε hlog hLK s t hs hst ht hWt (mE (E n)) (norm_mE hE) hκm σ A hA hsum

private theorem QProxyG_flow_im {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (h : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (h.2 n).2.1

private theorem QProxyG_flow_E {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (h : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    |STflowE z n| ≤ 2 - κ :=
  (abs_lemE_le (QProxyG_flow_im h n)).trans (h.2 n).1

theorem qProxyG_kerEK4_band (d : ℕ) : QProxyG_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam) := by
  intro hd k hk κ ε 𝔡 KL hκ hε h𝔡 hKL
  have hκ' : 0 < min κ (4 / 5) := lt_min hκ (by norm_num)
  refine ⟨qProxy4C d k 𝔡⁻¹ (min κ (4 / 5)) KL, qProxy4C_pos hd hk (inv_pos.2 h𝔡) hκ' hKL, ?_⟩
  intro sz 𝔠 z hflow
  filter_upwards [hflow.1.2.2.2.2] with n hn
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1
  have hE := QProxyG_flow_E hflow n
  exact qProxyG_kerEK4_band_at sz (STflowE z) hd hk (inv_pos.2 h𝔡) hκ' hKL n hlam hn.2 (by linarith) (nqGood1_mE_im_ge hκ hE)

end D1


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


/-! ## 8. Target 5: the pair kernel from EK-4 over a carrier (D1 and R1) -/

section PairKernelG

variable {d k : ℕ} {sz : Sizes d}

/-- **`hker` for sum-zero tensors over a carrier** (band `qProxy_hker`): D1 at the kernel coupling `gK`, R1 to the size level. -/
private theorem qProxy_hkerg (C : FlowFM sz) {gK : ℕ → ℝ} {A C4 Cv KL : ℝ}
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : QProxyG_KerEK4 C gK k KL C4 n) (hCv : C4 ≤ Cv) {ε ε₁ D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hεε : Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ k ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) (hD : 1 < D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s)) {σ : Fin k → Bool} (X : (Fin k → Zd d (sz.L n)) → ℂ)
    (hz : EKSumZero X) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδD : δ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hXM : ∀ b, ‖X b‖ ≤ M)
    (hXcls : ∀ b : Fin k → Zd d (sz.L n),
      (∃ i j, ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) s ≤ (zdistD d (sz.L n) (b i - b j) : ℝ)) → ‖X b‖ ≤ δ)
    (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ s t X a‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k * M +
        ((sz.W n : ℕ) : ℝ) ^ Cv * δ := by
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have ht1 : t < 1 := NQGood1Gen_t_lt_one hW ht hWt
  have hL2 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 :=
    pow_pos (by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)) 2
  have hwin : t ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    linarith [div_le_div_of_nonneg_right (hcmp n).2.1 hL2.le]
  have hX : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr hXM
  have hrat := step34Gen_ratio_pow_le hcmp hA n (v := s) ht1 k
  have hell := step34Gen_ellT_ge hcmp hA n s
  have hfast : ∀ D'', δ ≤ W ^ (-D'') → EKFastDecay (gK n) s W ε D'' X := by
    intro D'' hD'' a' ⟨i, j, hij⟩
    refine (hXcls a' ⟨i, j, ?_⟩).trans hD''
    have hE0 : 0 ≤ ellT (sz.L n) (gK n) s := le_min (le_trans zero_le_one (le_max_right _ _)) (Nat.cast_nonneg _)
    have hε₁0 : 0 ≤ W ^ ε₁ := Real.rpow_nonneg hW0.le _
    calc W ^ ε₁ * ellT (sz.L n) (sz.lam n) s ≤ W ^ ε₁ * (Real.sqrt A * ellT (sz.L n) (gK n) s) :=
          mul_le_mul_of_nonneg_left hell hε₁0
      _ = (Real.sqrt A * W ^ ε₁) * ellT (sz.L n) (gK n) s := by ring
      _ ≤ W ^ ε * ellT (sz.L n) (gK n) s := mul_le_mul_of_nonneg_right hεε hE0
      _ ≤ _ := hij
  have hat : ∀ D'' : ℝ, 1 < D'' → δ ≤ W ^ (-D'') → ‖Step2Gen_UN C n σ s t X a‖ ≤
      W ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k * M + W ^ (-D'' + Cv) := by
    intro D'' hD'' hδ''
    have h := hKer hW hLK ε D'' hε0 hε1 hD'' hWε hlog s t hs hst hwin hWt σ X (hfast D'' hδ'') hz
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

/-- **`ugenPairQNg_le_of_bounds`** (band `ugenPairQN_le_of_bounds`): the pair kernel `(𝒰_σ ⊗ 𝒰_σ̄) ∘ T` at `(a, a)` from D1. -/
theorem ugenPairQNg_le_of_bounds (C : FlowFM sz) {gK : ℕ → ℝ} {A C4 Cv KL : ℝ}
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : QProxyG_KerEK4 C gK k KL C4 n) (hRow : GridRepTailGen_Ker C n) (hCv : C4 ≤ Cv) {ε ε₁ D₂ : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hεε : Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ k ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) (hD : (k : ℝ) + 1 < D₂)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s)) {σ : Fin k → Bool}
    (T : (Fin k → Zd d (sz.L n)) → (Fin k → Zd d (sz.L n)) → ℂ) {M' δ' : ℝ} (hδ : 0 ≤ δ')
    (hδD : δ' ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) (hT : ∀ b b', ‖T b b'‖ ≤ M')
    (hz1 : ∀ b' : Fin k → Zd d (sz.L n), EKSumZero (fun b => T b b'))
    (hz2 : ∀ b : Fin k → Zd d (sz.L n), EKSumZero (fun b' => T b b'))
    (hslice : ∀ b b' : Fin k → Zd d (sz.L n),
      (∃ i j, ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) s ≤ (zdistD d (sz.L n) (b' i - b' j) : ℝ)) → ‖T b b'‖ ≤ δ')
    (hblock : ∀ b b' : Fin k → Zd d (sz.L n),
      (∃ i j, ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) s ≤ (zdistD d (sz.L n) (b i - b j) : ℝ)) → ‖T b b'‖ ≤ δ')
    (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ s t (fun b => Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a) a‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k) *
          ((((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k) * M' +
            ((sz.W n : ℕ) : ℝ) ^ Cv * δ') +
        ((sz.W n : ℕ) : ℝ) ^ Cv * (((sz.W n : ℕ) : ℝ) ^ k * δ') := by
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have hD1 : 1 < D₂ := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith
  have ht1 : t < 1 := NQGood1Gen_t_lt_one hW ht hWt
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hT (fun _ => 0) (fun _ => 0))
  set κ1 : ℝ := W ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ k with hκ1
  have hκ10 : 0 ≤ κ1 := mul_nonneg (Real.rpow_nonneg hW0.le _) (by positivity)
  have hWC0 : 0 ≤ W ^ Cv := Real.rpow_nonneg hW0.le _
  have hstage1 : ∀ b : Fin k → Zd d (sz.L n),
      ‖Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ κ1 * M' + W ^ Cv * δ' := fun b =>
    qProxy_hkerg C hcmp hA hKer hCv hW hLK hε0 hε1 hWε hlog hεε hAk hD1 hs hst ht hWt (fun b' => T b b') (hz2 b) hM'0 hδ hδD
      (fun b' => hT b b') (fun b' hb' => hslice b b' hb') a
  have hP : (1 - s) / (1 - t) ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hP0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  have hstage1far : ∀ b : Fin k → Zd d (sz.L n),
      (∃ i j, W ^ ε₁ * ellT (sz.L n) (sz.lam n) s ≤ (zdistD d (sz.L n) (b i - b j) : ℝ)) →
      ‖Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ W ^ k * δ' := by
    intro b hb
    have h1 := NQGood1Gen_norm_UN_row hRow (fun i => !σ i) hs hst ht1 hδ (fun b' => hblock b b' hb) a
    calc _ ≤ ((1 - s) / (1 - t)) ^ k * δ' := h1
      _ ≤ W ^ k * δ' := by gcongr
  have hδ2 : W ^ k * δ' ≤ W ^ (-(D₂ - k)) := by
    calc W ^ k * δ' ≤ W ^ k * W ^ (-D₂) := by gcongr
      _ = W ^ (-(D₂ - k)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hW0]
          congr 1; ring
  have hY0 : EKSumZero (fun b : Fin k → Zd d (sz.L n) =>
      Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a) := by
    intro i₀ hi x
    unfold Step2Gen_UN
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [← Finset.mul_sum, hz1 b' i₀ hi x, mul_zero]
  have hstage2 := qProxy_hkerg C hcmp hA hKer hCv hW hLK hε0 hε1 hWε hlog hεε hAk (D := D₂ - k) (by linarith) hs hst ht hWt
    (σ := σ) (fun b => Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a) hY0
    (M := κ1 * M' + W ^ Cv * δ') (δ := W ^ k * δ')
    (add_nonneg (mul_nonneg hκ10 hM'0) (mul_nonneg hWC0 hδ))
    (mul_nonneg (pow_nonneg hW0.le _) hδ) hδ2 hstage1 hstage1far a
  calc _ ≤ _ := hstage2
    _ = _ := by ring

end PairKernelG

/-! ## 9. Target 6: the quadratic-variation majorant of `qvFormQNg` -/

section QVBoundG

variable {d : ℕ} {sz : Sizes d}

/-- `qvFormQNg` is the pair kernel applied to `(𝒬 ⊗ 𝒬̄)(𝓔 ⊗ 𝓔)`. -/
private theorem qProxy_qvFormQNg_eq_pair (Cm : Step2Mat sz) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (v w : ℝ) (σ : Fin (m + 1) → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin (m + 1) → Zd d (sz.L n)) :
    qvFormQNg Cm n ϑ v w σ M a =
      (Step2Gen_UN Cm.toFlowFM n σ v w (fun b => Step2Gen_UN Cm.toFlowFM n (fun i => !σ i) v w
        (fun b' => qqTensorN ϑ v (fun c c' => STeeMg Cm n v M σ c c') b b') a) a).re := by
  unfold qvFormQNg Step2Gen_UN
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

/-- **`qvFormQNg_le_of_bounds`** (band `qvFormQN_le_of_bounds`): the closed-form majorant of the variance form of the `𝒬`-process from
bounds on `𝓔 ⊗ 𝓔`, D1 at `gK` and R1; the two-copy `lem_+Q` is read at the radius `ε₁` with `√A W^{ε₁} ≤ W^ε`. -/
theorem qvFormQNg_le_of_bounds {m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (Λg K C c : ℝ) (hΛ : 0 < Λg) (hK : 0 < K)
    (hC : 0 < C) (hc : 0 < c) (Cm : Step2Mat sz) {gK : ℕ → ℝ} {A C4 Cv : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) (hKer : QProxyG_KerEK4 Cm.toFlowFM gK (m + 1) K C4 n)
    (hRow : GridRepTailGen_Ker Cm.toFlowFM n) (hCv : C4 ≤ Cv) {ε ε₁ τ' C₀ D : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hε₁0 : 0 < ε₁) (hε₁1 : ε₁ < 1)
    (hWε₁ : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁) (hεε : Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁)
    (hAk : A ^ (m + 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) (hC₀ : 0 ≤ C₀)
    (hD : (m : ℝ) + 2 + qProxyCQ d m Λg K C c < D)
    (hW₀ : qProxyW0 d m Λg K C c C₀ ε₁ D ≤ ((sz.W n : ℕ) : ℝ))
    {ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - v)) {σ : Fin (m + 1) → Bool}
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {Mee : ℝ}
    (hMee : Mee ≤ ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hT : ∀ b b' : Fin (m + 1) → Zd d (sz.L n), ‖STeeMg Cm n v M σ b b'‖ ≤ Mee)
    (hTfar : ∀ b b' : Fin (m + 1) → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) →
        ‖STeeMg Cm n v M σ b b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    qvFormQNg Cm n ϑ v w σ M a ≤
      (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) *
        ((((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) *
          (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d m Λg K C c * ε₁) * Mee +
            ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) +
          ((sz.W n : ℕ) : ℝ) ^ Cv * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) +
        ((sz.W n : ℕ) : ℝ) ^ Cv *
          (((sz.W n : ℕ) : ℝ) ^ (m + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) := by
  have hL3 := sz.three_le_L n
  have hw1 : w < 1 := NQGood1Gen_t_lt_one hW hwL hWt
  have hCQ0 : 0 < qProxyCQ d m Λg K C c := qProxyCQ_pos hd m hΛ hK hC hc
  have hCn0 : 0 < qProxyCn d m Λg K C c := qProxyCn_pos hd m hΛ hK hC hc
  have hCQ : qProxyCQ d m Λg K C c = 2 * qProxyCn d m Λg K C c + 2 := rfl
  have hDn : qProxyCn d m Λg K C c + 2 < D := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hv1 : v < 1 := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  obtain ⟨hi, hii, hiii⟩ := qqTensorBoundsN hd Λg K C c hΛ hK hC hc hL3 hg hgΛ hW hε₁0 hε₁1 hWε₁ hLK hdW
    hC₀ hDn hW₀ hϑ hv0 hv1 (fun b b' => STeeMg Cm n v M σ b b') hMee hT hTfar
  obtain ⟨hz1, hz2⟩ := qqTensorN_sumZero ϑ v (hϑ.1 v) (fun c c' => STeeMg Cm n v M σ c c')
  rw [qProxy_qvFormQNg_eq_pair]
  refine (Complex.re_le_norm _).trans ?_
  exact ugenPairQNg_le_of_bounds Cm.toFlowFM hcmp hA hKer hRow hCv hW hLK hε0 hε1 hWε hlog hεε hAk
    (D₂ := D - qProxyCQ d m Λg K C c) (by push_cast; linarith) hv0 hvw hwL hWt
    (fun b b' => qqTensorN ϑ v (fun c c' => STeeMg Cm n v M σ c c') b b')
    (δ' := ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c))
    (Real.rpow_nonneg hW0.le _) (le_of_eq (by congr 1; ring)) hi hz1 hz2
    (fun b b' hb' => by
      have h := hii b b' hb'
      rw [show -(D - qProxyCQ d m Λg K C c) = -D + qProxyCQ d m Λg K C c by ring] at h
      exact h)
    (fun b b' hb => hiii b' b hb) a

end QVBoundG

section QVBound

/-- **Target 6a (`qvFormQN_le_of_bounds`)**, name and type unchanged: the corollary of `qvFormQNg_le_of_bounds` at `bandStep2Mat sz (fun _ => E)`,
`gK = sz.lam`, `A = 1`, `ε₁ = ε`, `Cv = C4 = qProxy4C` (D1 by `qProxyG_kerEK4_band_at`). -/
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
  have hw1 : w < 1 := NQGood1Gen_t_lt_one hW hwL hWt
  have hw0 : 0 ≤ w := by linarith
  rw [qProxy_qvFormQN_eq_g sz (fun _ => E) n hE hw0 hw1]
  have hKer := qProxyG_kerEK4_band_at sz (fun _ => E) hd (by omega : 2 ≤ m + 1) hΛ hκ' hK n hg hgΛ hE hκm
  exact qvFormQNg_le_of_bounds hd hm Λg K C c hΛ hK hC hc (bandStep2Mat sz (fun _ => E)) (gK := sz.lam) (A := 1)
    (fun n' => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩) le_rfl hg hgΛ hKer
    (gridRepTailGen_ker_band sz (fun _ => E) n hE) le_rfl hW hε0 hε1 hWε hlog hε0 hε1 hWε (by simp) hLK hdW
    (by simp) hC₀ hD hW₀ hϑ hv0 hvw hwL hWt M hMee hT hTfar a

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

section YQG

variable {d : ℕ} {sz : Sizes d}

private theorem qProxy_stronglyMeasurable_yVecQNg {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => yVecQNg Cm s t K n j ϑ σ ω) := by
  have hcont : Continuous (fun A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ =>
      STQop (d := d) ϑ (gridTime s t K n (j + 1)) A) := by
    refine continuous_pi fun a => ?_
    unfold STQop STPsum
    exact (continuous_apply a).sub
      ((continuous_finsetSum _ fun c _ => continuous_apply c).mul continuous_const)
  exact hcont.comp_stronglyMeasurable (GridAssemblyGen_stronglyMeasurable_YvecNg hL hW s t K n j σ)

open scoped Matrix.Norms.L2Operator in
/-- **Item 8 over a carrier with an explicit strictly positive level** (body of `yMomentsQUnifNg`; band `qProxy_yMomentsQPos`). -/
theorem qProxy_yMomentsQPosg {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hKer : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n) (κm τ' : ℝ) (s t : ℕ → ℝ) :
    DecayGen_Spec Cm.toFlowFM κm → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.SizeTendsto → sz.RangeCond τ' t →
    ∀ (m : ℕ) (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), 0 < C → 0 ≤ c →
      (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → ∀ σ : Fin (m + 1) → Bool,
      ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
        ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 < P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
          ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
            YMomentBoundsNg Cm σ (gridTime s t K n) τ (K n)
              (fun j ω => yVecQNg Cm s t K n j (ϑ n) σ ω)
              (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2) := by
  intro hspec hs0 hst ht1 hsize hrange m C c ϑ hC hc hϑ σ
  have hc0 : 0 < κm := hspec.1
  set θ : ℝ := max 0 (1 - τ') with hθdef
  have hθ0 : 0 ≤ θ := le_max_left _ _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  refine ⟨11 + (4 * ((m + 1 : ℕ) : ℝ) + 4) * θ + 2 * m + 2, by positivity, ?_⟩
  intro K hK
  have hbig := hsize.eventually (eventually_ge_atTop
    (max (1 + C) (2000 * (2 ^ (m + 1) * (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) *
      (κm⁻¹) ^ (m + 1 + 2)) ^ 2)))
  filter_upwards [hrange, hbig] with n hR hN
  have hN1' : 1 + C ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hN
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hbig' : 2000 * (2 ^ (m + 1) * (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) *
      (κm⁻¹) ^ (m + 1 + 2)) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hN
  have hΘ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := Real.one_le_rpow hN1 hθ0
  have hΘ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ θ := by positivity
  set Smax : ℝ := (2 * ((sz.size n : ℕ) : ℝ) ^ θ) ^ (m + 1) with hSmax
  set C2 : ℝ := (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ)
    * (((sz.size n : ℕ) : ℝ) ^ θ / κm) ^ (m + 1 + 2) with hC2def
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
  · have hP0 := RBM.Ind.AzumaProxyN_P_le_pub (m + 1) hc0 hθ0 hN1 hbig'
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
    refine ⟨fun j => qProxy_stronglyMeasurable_yVecQNg hL hW s t K n j (ϑ n) σ, ?_⟩
    intro p hp b j hjp
    have hj : j + 1 ≤ K n := by omega
    have hv0 : 0 ≤ gridTime s t K n (j + 1) := qProxy_gridTime_nonneg s t K n (hs0 n) (hst n) (j + 1)
    have hvt : gridTime s t K n (j + 1) ≤ t n := qProxy_gridTime_le s t K n (hst n) hj (hK n)
    have hv1 : gridTime s t K n (j + 1) < 1 := hvt.trans_lt (ht1 n)
    have hw0 : 0 ≤ gridTime s t K n p := qProxy_gridTime_nonneg s t K n (hs0 n) (hst n) p
    have hwt : gridTime s t K n p ≤ t n := qProxy_gridTime_le s t K n (hst n) hp (hK n)
    have hw1 : gridTime s t K n p < 1 := hwt.trans_lt (ht1 n)
    set κb : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b' => ∏ i : Fin (m + 1),
      Step2Gen_uKer Cm.toFlowFM n (σ i) (σ (finRotate (m + 1) i)) (gridTime s t K n (j + 1))
        (gridTime s t K n p) (b i) (b' i) with hκb
    have hUrow : ∑ b', ‖κb b'‖ ≤ Smax := by
      refine (AzumaProxyN_rowsum_UN_pubg (hKer n) σ hv0 hv1 hw0 hw1 b).trans ?_
      have h1 : (1 - gridTime s t K n p)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τ') :=
        RBM.Ind.AzumaProxyN_inv_one_sub_le_pub hwt hN0 hR
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (1 - τ') ≤ ((sz.size n : ℕ) : ℝ) ^ θ :=
        Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) (m + 1)
    have hrow : ∑ c', ‖qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb c'‖ ≤ Smax' :=
      (qProxy_sum_norm_wts_le (by have := sz.three_le_L n; omega) hC.le hc (hϑ n) hv0 hv1 κb).trans
        (mul_le_mul_of_nonneg_left hUrow hLm0.le)
    have hC2' : ∀ (a : Fin (m + 1) → Zd d (sz.L n))
        (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
        y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamNgShift Cm Ψ s t K n j σ a)) M y y‖ ≤
          C2 * ‖y‖ ^ 2 := by
      intro a M y hM hy
      have hη := AzumaProxyN_eta_inv_le_pubg hspec n (u := gridTime s t K n (j + 1)) (t := t n) (τ' := τ')
        (N := ((sz.size n : ℕ) : ℝ)) hvt hN0 hR
      have hη' : (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ θ / κm :=
        hη.trans (by
          gcongr
          exact le_max_right _ _)
      have h := (StepDecompGen_loopFamShift_hermTestFun hL hW s t K n j (hst n) (ht1 n) hj σ a).2 M y hM hy
      refine h.trans ?_
      have hpos : 0 < Cm.eta n (gridTime s t K n (j + 1)) := by
        rw [hspec.2.2 n]
        exact mul_pos (by linarith) (lt_of_lt_of_le hc0 (hspec.2.1 n))
      have hle : (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ)
          * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1 + 2) ≤ C2 := by
        rw [hC2def]
        have hη0 : 0 ≤ (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ := inv_nonneg.mpr hpos.le
        have := pow_le_pow_left₀ hη0 hη' (m + 1 + 2)
        have hpos' : 0 ≤ (((m + 1) * (m + 1 + 1) : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left this hpos' |>.trans (le_of_eq (by ring))
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hcomb : ∀ ω' : PathΩ sz,
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (j + 1)) (gridTime s t K n p)
          (yVecQNg Cm s t K n j (ϑ n) σ ω') b =
        ∑ c', qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb c' *
          YvecNg Cm s t K n j σ ω' c' := fun ω' =>
      qProxy_sum_Qop (ϑ n) (gridTime s t K n (j + 1)) κb (YvecNg Cm s t K n j σ ω')
    have hpt : ∀ ω, stoppedEdgeNg Cm σ (gridTime s t K n) (gridTime s t K n p) τ
        (fun j ω => yVecQNg Cm s t K n j (ϑ n) σ ω) b j ω =
        AzumaProxyN_stopWg Cm s t K n j σ (qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb) τ ω := by
      intro ω
      unfold stoppedEdgeNg AzumaProxyN_stopWg
      by_cases h : ω ∈ {ω' | j < τ ω'}
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
        exact hcomb ω
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    have h8 := AzumaProxyN_YfieldsWg hL hW s t K n j (hst n) (ht1 n) hj σ
      (qProxy_wts (ϑ n) (gridTime s t K n (j + 1)) κb) hS0'.le hC20.le hrow hC2' le_rfl τ hτ
    simp only [hpt]
    exact h8

/-- **`yMomentsQUnifNg`** (band `yMomentsQUnifN`): the uniform `Y` moments of the `𝒬`-increment over a carrier, `C_P` before the grid. -/
theorem yMomentsQUnifNg {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hKer : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n) (κm τ' : ℝ) (s t : ℕ → ℝ) :
    DecayGen_Spec Cm.toFlowFM κm → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.SizeTendsto → sz.RangeCond τ' t →
    ∀ (m : ℕ) (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), 0 < C → 0 ≤ c →
      (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) → ∀ σ : Fin (m + 1) → Bool,
      ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
        ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
          ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
            YMomentBoundsNg Cm σ (gridTime s t K n) τ (K n)
              (fun j ω => yVecQNg Cm s t K n j (ϑ n) σ ω)
              (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2) := by
  intro hspec hs0 hst ht1 hsize hrange m C c ϑ hC hc hϑ σ
  obtain ⟨C_P, hC_P, h⟩ := qProxy_yMomentsQPosg hL hW hKer κm τ' s t hspec hs0 hst ht1 hsize hrange m C c ϑ hC hc hϑ σ
  refine ⟨C_P, hC_P, fun K hK => ?_⟩
  filter_upwards [h K hK] with n ⟨P, hP, hPN, hτ⟩
  exact ⟨P, hP.le, hPN, hτ⟩

end YQG

/-- **Target 8 (`yMomentsQUnifN`)**, name and type unchanged: the corollary of `yMomentsQUnifNg` at `bandStep2Mat sz E` with the spectral data
`κm = √κ/2` (`DecayGen_bandSpec`); the conclusion is converted by `bandStep2_YMomentBoundsN` and `qProxy_yVecQN_eq_g`. -/
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
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  obtain ⟨C_P, hC_P, h⟩ := yMomentsQUnifNg (stepDecompGen_loopForm_band sz E hE2) (stepDecompGen_walkForm_band sz E)
    (fun n => gridRepTailGen_ker_band sz E n (hE2 n).le) (Real.sqrt κ / 2) τ' s t (DecayGen_bandSpec sz hκ hE) hs0 hst ht1
    hsize hrange m C c ϑ hC hc hϑ σ
  refine ⟨C_P, hC_P, fun K hK => ?_⟩
  filter_upwards [h K hK] with n ⟨P, hP, hPN, hY⟩
  refine ⟨P, hP, hPN, fun τ hτ => ?_⟩
  have hYeq : (fun j ω => yVecQN sz E s t K n j (ϑ n) σ ω) =
      fun j ω => yVecQNg (bandStep2Mat sz E) s t K n j (ϑ n) σ ω :=
    funext fun j => funext fun ω => qProxy_yVecQN_eq_g sz E s t K n j (ϑ n) σ ω
  rw [hYeq]
  exact (bandStep2_YMomentBoundsN sz E σ _ τ _ _ _ _).2 (hY τ hτ)

end YQ

end RBM.Ind

end
