/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.AzumaProxyN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.DecayLoopB
import RBM3D.Induction.LoopC2N
import RBM3D.Induction.GridDriftN
import RBM3D.Evolution.SumDecay
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The non-alternating good-set inputs, first half (`d ≥ 3`)

The drift tensor, `hker`, the quadratic-variation majorant of `qvFormN`, and the good-set shift
`u_j → u_{j+1}`.  The `d ≥ 3` form of RBM2D's `NonAltGood` (§§1-2) and of the corresponding pieces of
`StoppedEndDefs` (`driftTensor`, `hker_of_case1`, `qvFormN_eq_re_UgenPair`): loops carry `W^{-d}` per
insertion, labels live in `Zd d L`, and `GoodSetN` (`Induction/GridGoodN.lean`) has the levels
`Γ, Λ, Φ` and no additive `W^{-D'}` in the bounds on the `ℰ` terms.
Paper: Lemma 4.6 (`lem:STOeq_NQ`) and its proof, (4.54) `sum_res_2_NAL` of Lemma 4.16 (`lem:sum_decay`).

## What is here (namespace `RBM.Ind`)

* §1 `driftTensorN` (the sum `Σ_{l=3}^k STksimLKM_l + STelklkM + STegtM` of `GridDriftN`, which
  states it inline) and `driftTensorN_far_of_goodSet` (the far-label clause of `GoodSetN`:
  `≤ W^{-D'}` beyond `ℓ_u W^{τ'}`).
* §2 `UgenPairN` (`𝒰_σ ⊗ 𝒰_σ̄`) and `qvFormN_eq_re_UgenPairN`.
* §3 `nqGood1C` (the constant of `ekSumDecayNAL_holds`) and `hker_of_case1N`: for non-alternating `σ`,
  the bound `‖𝒰_{s,t,σ} X‖ ≤ W^{Cε} ((g²+|1-s|)/(g²+|1-t|))^{k-1} M + W^C δ` from
  `ekSumDecayNAL_holds`; no `log L` power and no `ρ_{s,t}`, `K_w` factors (RBM2D's
  `(1+log L)^k K_w^{2(k-1)} ρ^k` and `((1-u)/(1-w))^k δ` do not occur: `ekSumDecayNAL_holds` has `W^{Cε}`
  and the ratio `r^{k-1}`).  The `L^∞` window of `GoodSetN` (`STdiamInf`) is turned into the `ℓ¹` window
  of `ekSumDecayNAL_holds` by `d W^{τ'} ≤ W^ε`.
* §4 `nqGood1_ugenPairN_le_of_bounds`, `nqGood1_qvFormN_le_of_bounds`: the majorant
  `κ₁ (κ₁ Γ(ΓΛ)B_u^{2k}/η_u + W^C W^{-D'}) + W^C W^k W^{-D'}` of `qvFormN`, by two uses of
  `hker_of_case1N` (first on the `b'`-block with `σ̄`, then on the `b`-block with `σ`); needs
  `D' > k + 1`.
* §5 the shift `u_j → u_{j+1}`: `loopShiftErrN`, `norm_loopL_zshiftN_le`, the crude envelopes
  `norm_loopFine_crudeN`, `STmaxLKM_crudeN`, `STXiLKM_crudeN`, and the shift of the pair form
  `norm_STeeM_shiftN_le` with `eeShiftErrN` (`STeeM` contains `𝓛` only).
  `ℓ_u ≤ ℓ_{u'}` is `nqGood1_ellT_mono`, for every real `g` (`0 ≤ lam n` is no field of `Sizes`; for
  `g < 0` both sides are `min 1 L`).

Every helper that is not part of the statements is `private` or prefixed `nqGood1_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. The drift tensor and its compositions with `GoodSetN` -/

section Drift

variable {d : ℕ} (sz : Sizes d)

/-- The drift tensor of the stopped hierarchy at a grid time. -/
def driftTensorN (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u H l (loopOf σ a) +
    sz.STelklkM n E u H (loopOf σ a) + sz.STegtM n E u H (loopOf σ a)

/-- **The drift far decay on the good set** (`hDcls`; the far-label clause of `GoodSetN`): `‖Dr(σ,a)‖ ≤
W^{-D'}` when `ℓ_u W^{τ'} ≤ diam_∞ a`; as RBM2D's `driftTensor_far_of_goodSet`. -/
theorem driftTensorN_far_of_goodSet {n : ℕ} {E u Γ Λ Φ τ' D' : ℝ} {k : ℕ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D') (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (hfar : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)) :
    ‖driftTensorN sz n E u M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  obtain ⟨-, -, -, -, -, -, -, hVa, -⟩ := hM
  have h := hVa σ a hfar
  unfold driftTensorN
  exact (norm_add₃_le).trans h

end Drift

/-! ## 2. The pair kernel `𝒰_σ ⊗ 𝒰_σ̄` and `qvFormN` -/

section PairKernel

variable {d L : ℕ} [NeZero L] {g : ℝ}

private theorem nqGood1_SB_conj (a b : Zd d L) :
    (starRingEnd ℂ) (SB d L g a b) = SB d L g a b := by
  rw [SB_apply, sbKernel_eq_ofReal, Complex.conj_ofReal]

/-- `Θ_{conj ξ} = conj Θ_ξ` entrywise. -/
private theorem nqGood1_Theta_star (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g (star ξ) a b = star (Theta d L g ξ a b) := by
  have hξ' : ‖star ξ‖ < 1 := by rwa [norm_star]
  have hmul : (Theta d L g ξ).map (starRingEnd ℂ) * (1 - star ξ • SB d L g) = 1 := by
    have h := congrArg (fun A : Matrix (Zd d L) (Zd d L) ℂ => A.map (starRingEnd ℂ))
      (Theta_mul_of_three_le (d := d) (g := g) hL hξ)
    simp only [Matrix.map_mul] at h
    have h1 : (1 - ξ • SB d L g).map (starRingEnd ℂ) = 1 - star ξ • SB d L g := by
      ext x y
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul, nqGood1_SB_conj]
      split_ifs <;> simp
    rw [h1] at h
    rw [h]
    ext x y
    simp only [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  have key := eq_Theta_of_mul d L g (norm_SB d L g hL) hξ' hmul
  have := congrFun (congrFun key a) b
  simpa using this.symm

/-- `conj (uKer μ v w) = uKer (conj μ) v w` for real `v, w` (`S^{(B)}` is real). -/
private theorem nqGood1_conj_uKer (hL : 3 ≤ L) {μ : ℂ} {v w : ℝ} (hξ : ‖(w : ℂ) * μ‖ < 1)
    (x y : Zd d L) :
    (starRingEnd ℂ) (uKer d L g μ v w x y) = uKer d L g ((starRingEnd ℂ) μ) v w x y := by
  have hT := nqGood1_Theta_star (d := d) (L := L) (g := g) hL hξ
  have hw : star ((w : ℂ) * μ) = (w : ℂ) * (starRingEnd ℂ) μ := by
    simp [Complex.conj_ofReal]
  rw [hw] at hT
  unfold uKer
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
      map_mul, nqGood1_SB_conj, Complex.conj_ofReal]
    split_ifs <;> simp
  · exact (hT z y).symm ▸ rfl

private theorem nqGood1_mSigma_not (E : ℝ) (s : Bool) :
    mSigma E (!s) = (starRingEnd ℂ) (mSigma E s) := by
  cases s <;> simp [mSigma]

variable (d L g)

/-- **The pair kernel** `(𝒰_{v,w,σ} ⊗ 𝒰_{v,w,σ̄}) ∘ T` at `(a, a)`:
`Σ_{b,b'} Π_i 𝒰_σ(a_i,b_i) Π_i 𝒰_σ̄(a_i,b'_i) T_{b,b'}`, `σ̄ = !σ`. -/
def UgenPairN (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) : ℂ :=
  ∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
    (∏ i : Fin k, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
      (∏ i : Fin k, uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) * T b b'

variable {d L g}

/-- `UgenPairN` is `𝒰_σ` applied to `b ↦ (𝒰_σ̄ ∘ T_{b,·})(a)`. -/
theorem nqGood1_UgenPairN_eq_Ugen (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) :
    UgenPairN d L g E σ v w T a =
      Ugen d L g E σ v w (fun b => Ugen d L g E (fun i => !σ i) v w (T b) a) a := by
  unfold UgenPairN Ugen UN
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

end PairKernel

section QV

variable {d : ℕ} (sz : Sizes d)

/-- **`qvFormN` is the real part of the pair kernel `𝒰_σ ⊗ 𝒰_σ̄` applied to `𝓔 ⊗ 𝓔`**
(`STeeM`): the conjugate of the slotwise kernel of `σ` is the slotwise kernel of `σ̄`
(`m(σ̄) = conj m(σ)`, `S^{(B)}` real); as RBM2D's `qvFormN_eq_re_UgenPair`. -/
theorem qvFormN_eq_re_UgenPairN (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) {v w : ℝ} (hw : |w| < 1)
    {k : ℕ} (σ : Fin k → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin k → Zd d (sz.L n)) :
    qvFormN sz n E v w σ M a =
      (UgenPairN d (sz.L n) (sz.lam n) E σ v w (fun b b' => sz.STeeM n E v M σ b b') a).re := by
  unfold qvFormN UgenPairN
  refine congrArg Complex.re (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_)
  have hconj : (starRingEnd ℂ) (∏ i : Fin k, uKer d (sz.L n) (sz.lam n)
      (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b' i)) =
      ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (!σ i)) i) v w
        (a i) (b' i) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hn : ‖(w : ℂ) * cycProd (fun i => mSigma E (σ i)) i‖ < 1 := by
      rw [cycProd, norm_mul, norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul, mul_one,
        Complex.norm_real]
      simpa using hw
    rw [nqGood1_conj_uKer (sz.three_le_L n) hn]
    congr 1
    simp only [cycProd, map_mul, ← nqGood1_mSigma_not]
  rw [hconj]

end QV

/-! ## 3. `hker`: the non-alternating kernel bound of `Ugen` from `ekSumDecayNAL_holds` -/

section Hker

/-- **The constant `C(d, k, Λ_g, κ')` of `ekSumDecayNAL_holds`** (Lemma 4.16 `lem:sum_decay`, (4.54)
`sum_res_2_NAL`), chosen once for all `L, g, W, ε, D`; `1` outside the range of the statement. -/
def nqGood1C (d k : ℕ) (Λg κ' : ℝ) : ℝ :=
  if h : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' then
    Classical.choose (ekSumDecayNAL_holds d k Λg κ' (prop5Decay_holds d Λg)
      (prop5Short_holds d Λg κ') h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 1

theorem nqGood1C_pos {d k : ℕ} {Λg κ' : ℝ} (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg)
    (hκ' : 0 < κ') : 0 < nqGood1C d k Λg κ' := by
  have h : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' := ⟨hd, hk, hΛ, hκ'⟩
  unfold nqGood1C
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec (ekSumDecayNAL_holds d k Λg κ' (prop5Decay_holds d Λg)
    (prop5Short_holds d Λg κ') h.1 h.2.1 h.2.2.1 h.2.2.2)).1

/-- The `L^∞` class `{‖X b‖ ≤ δ when ℓ_s W^{τ'} ≤ diam_∞ b}` of the good set implies the window
`(deccA0)` of `EKFastDecay` (`ℓ¹` distance, radius `W^ε ℓ_s`) once `d W^{τ'} ≤ W^ε`
(`zdistD ≤ d · zdistInf`). -/
private theorem nqGood1_fast_of_cls {d L k : ℕ} (hd : 0 < d) (hL : 1 ≤ (L : ℝ)) {g s W ε τ' D δ : ℝ}
    (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hδ : δ ≤ W ^ (-D)) {X : (Fin k → Zd d L) → ℂ}
    (hcls : ∀ b : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ) :
    EKFastDecay g s W ε D X := by
  intro a ⟨i, j, hij⟩
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

/-- **`hker` in the non-alternating case, `d ≥ 3`**, from `ekSumDecayNAL_holds`
(Lemma 4.16 `lem:sum_decay`, (4.54) `sum_res_2_NAL`), with the constant
`C = nqGood1C d k Λ_g κ'`.  For `σ` with `σ_i = σ_{i+1}` for some `i`, `0 ≤ s ≤ t ≤ 1 - g²/L²`,
`W⁻¹ ≤ (1-t)/(1-s)`, `κ' ≤ Im m(E)`, the kernel `𝒰_{s,t,σ}` maps a tensor of sup-norm `≤ M`, which
is `≤ δ ≤ W^{-D}` (`D > 1`) off the window `ℓ_s W^{τ'} ≤ diam_∞`, to
`W^{Cε} ((g²+|1-s|)/(g²+|1-t|))^{k-1} M + W^C δ`.  No `log L` power and no `ρ_{s,t}`, `K_w`
factors appear (RBM2D's `hker_of_case1` has `(1+log L)^k K_w^{2(k-1)} ρ^k` and
`((1-u)/(1-w))^k δ`); the hypothesis `d W^{τ'} ≤ W^ε` converts the `L^∞` window of `GoodSetN` into
the `ℓ¹` window of `ekSumDecayNAL_holds`. -/
theorem hker_of_case1N {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg)
    (hκ' : 0 < κ') {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg)
    {W ε τ' D : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε)
    (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hD : 1 < D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2)
    (hWt : W⁻¹ ≤ (1 - t) / (1 - s)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im)
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (X : (Fin k → Zd d L) → ℂ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδD : δ ≤ W ^ (-D))
    (hXM : ∀ b, ‖X b‖ ≤ M)
    (hXcls : ∀ b : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ)
    (a : Fin k → Zd d L) :
    ‖Ugen d L g E σ s t X a‖ ≤
      W ^ (nqGood1C d k Λg κ' * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1) * M +
        W ^ nqGood1C d k Λg κ' * δ := by
  have hex : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' := ⟨hd, hk, hΛ, hκ'⟩
  have hCdef : nqGood1C d k Λg κ' = Classical.choose (ekSumDecayNAL_holds d k Λg κ'
      (prop5Decay_holds d Λg) (prop5Short_holds d Λg κ') hd hk hΛ hκ') := by
    unfold nqGood1C; rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hC, hEK⟩ := Classical.choose_spec (ekSumDecayNAL_holds d k Λg κ'
    (prop5Decay_holds d Λg) (prop5Short_holds d Λg κ') hd hk hΛ hκ')
  rw [hCdef]
  set C := Classical.choose (ekSumDecayNAL_holds d k Λg κ' (prop5Decay_holds d Λg)
    (prop5Short_holds d Λg κ') hd hk hΛ hκ') with hCset
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hW0 : (0 : ℝ) < W := by linarith
  have hr : 0 ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1) :=
    mul_nonneg (Real.rpow_nonneg hW0.le _) (by positivity)
  have hX : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr hXM
  have hat : ∀ D'' : ℝ, 1 < D'' → δ ≤ W ^ (-D'') → ‖Ugen d L g E σ s t X a‖ ≤
      W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1) * M + W ^ (-D'' + C) := by
    intro D'' hD'' hδD''
    have hfast : EKFastDecay g s W ε D'' X :=
      nqGood1_fast_of_cls (by omega) hL1 hdW hδD'' hXcls
    have h := hEK L hL g hg hgΛ W ε D'' hW hε0 hε1 hD'' hWε s t hs hst ht hWt (mE E) (norm_mE hE)
      hκm σ hσ X hfast
    have h2 : ‖Ugen d L g E σ s t X a‖ ≤ ‖UN d L g (EKsgn (mE E) σ) s t X‖ :=
      norm_le_pi_norm (UN d L g (EKsgn (mE E) σ) s t X) a
    calc ‖Ugen d L g E σ s t X a‖ ≤ ‖UN d L g (EKsgn (mE E) σ) s t X‖ := h2
      _ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1) * ‖X‖ +
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

end Hker

/-! ## 4. The quadratic-variation majorant of `qvFormN` on the good set (at the time of the good set) -/

section QVBound

/-- `diam_∞` of the right half of an appended label vector. -/
private theorem nqGood1_diam_append_right {d L k : ℕ} (b b' : Fin k → Zd d L) :
    STdiamInf b' ≤ STdiamInf (Fin.append b b') := by
  refine Finset.sup_le fun p _ => ?_
  have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) =>
      zdistInf d L (Fin.append b b' q.1 - Fin.append b b' q.2))
      (Finset.mem_univ (Fin.natAdd k p.1, Fin.natAdd k p.2))
  rw [Fin.append_right, Fin.append_right] at h
  exact h

/-- `diam_∞` of the left half of an appended label vector. -/
private theorem nqGood1_diam_append_left {d L k : ℕ} (b b' : Fin k → Zd d L) :
    STdiamInf b ≤ STdiamInf (Fin.append b b') := by
  refine Finset.sup_le fun p _ => ?_
  have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) =>
      zdistInf d L (Fin.append b b' q.1 - Fin.append b b' q.2))
      (Finset.mem_univ (Fin.castAdd k p.1, Fin.castAdd k p.2))
  rw [Fin.append_left, Fin.append_left] at h
  exact h

/-- The bulk gap: `|E| ≤ 2 - κ`, `κ > 0` gives `min κ (4/5) ≤ Im m(E)`. -/
theorem nqGood1_mE_im_ge {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    min κ (4 / 5) ≤ (mE E).im := by
  rw [mE_im]
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h1 : |E| ^ 2 ≤ (2 - κ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hE 2
    rwa [sq_abs] at h1
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hm0 : 0 < min κ (4 / 5) := lt_min hκ (by norm_num)
  have hsq : (2 * min κ (4 / 5)) ^ 2 ≤ 4 - E ^ 2 := by
    rcases min_cases κ (4 / 5) with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h]; nlinarith
    · rw [h]; nlinarith [mul_nonneg (sub_nonneg.2 h'.le) (by linarith : (0 : ℝ) ≤ 16 / 5 - κ)]
  have : 2 * min κ (4 / 5) ≤ Real.sqrt (4 - E ^ 2) := by
    calc 2 * min κ (4 / 5) = Real.sqrt ((2 * min κ (4 / 5)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  linarith

/-- **The pair kernel on a tensor with a sup bound and far decay** (the engine of the
quadratic-variation majorant; as RBM2D's `ugenPairCase1Explicit`, derived here from `hker_of_case1N`
twice): for non-alternating `σ`, a tensor `T_{b,b'}` with `‖T_{b,b'}‖ ≤ M_ee` and
`‖T_{b,b'}‖ ≤ δ ≤ W^{-D}` when `ℓ_s W^{τ'} ≤ diam_∞(b,b')`, `D > k + 1`,
`‖(𝒰_{s,t,σ} ⊗ 𝒰_{s,t,σ̄}) ∘ T (a,a)‖ ≤ κ₁ (κ₁ M_ee + W^C δ) + W^C (W^k δ)`,
`κ₁ = W^{Cε} ((g²+|1-s|)/(g²+|1-t|))^{k-1}`, `C = nqGood1C d k Λ_g κ'`.  First the `b'`-block
with `σ̄` (non-alternating iff `σ` is), on the tensors `b' ↦ T_{b,b'}`; then the `b`-block with `σ`,
on `b ↦ (𝒰_σ̄ ∘ T_{b,·})(a)`, whose far level `W^k δ` comes from the row sums
(`norm_UN_apply_le`, `(1-s)/(1-t) ≤ W`). -/
theorem nqGood1_ugenPairN_le_of_bounds {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg)
    (hκ' : 0 < κ') {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg)
    {W ε τ' D : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε)
    (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hD : (k : ℝ) + 1 < D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2)
    (hWt : W⁻¹ ≤ (1 - t) / (1 - s)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im)
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) {Mee δ : ℝ} (hδ : 0 ≤ δ) (hδD : δ ≤ W ^ (-D))
    (hT : ∀ b b', ‖T b b'‖ ≤ Mee)
    (hTfar : ∀ b b' : Fin k → Zd d L,
      ellT L g s * W ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) → ‖T b b'‖ ≤ δ)
    (a : Fin k → Zd d L) :
    ‖UgenPairN d L g E σ s t T a‖ ≤
      (W ^ (nqGood1C d k Λg κ' * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1)) *
          ((W ^ (nqGood1C d k Λg κ' * ε) *
              ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1)) * Mee +
            W ^ nqGood1C d k Λg κ' * δ) +
        W ^ nqGood1C d k Λg κ' * (W ^ k * δ) := by
  set C : ℝ := nqGood1C d k Λg κ' with hCdef
  have hW0 : 0 < W := by linarith
  have hD1 : 1 < D := by
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
  have hMee0 : 0 ≤ Mee := (norm_nonneg _).trans (hT (fun _ => 0) (fun _ => 0))
  set κ1 : ℝ := W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1) with hκ1
  have hκ10 : 0 ≤ κ1 := mul_nonneg (Real.rpow_nonneg hW0.le _) (by positivity)
  have hWC0 : 0 ≤ W ^ C := Real.rpow_nonneg hW0.le _
  have hσb : ∃ i, (fun i => !σ i) i = (fun i => !σ i) (finRotate k i) := by
    obtain ⟨i, hi⟩ := hσ
    exact ⟨i, by simp only [hi]⟩
    -- first the `b'`-block, for every `b`
  have hstage1 : ∀ b : Fin k → Zd d L,
      ‖Ugen d L g E (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ κ1 * Mee + W ^ C * δ := by
    intro b
    exact hker_of_case1N Λg κ' hd hk hΛ hκ' hL hg hgΛ hW hε0 hε1 hWε hdW hD1 hs hst ht hWt hE
      hκm hσb (fun b' => T b b') hMee0 hδ hδD (fun b' => hT b b')
      (fun b' hfar => hTfar b b' (hfar.trans (by exact_mod_cast nqGood1_diam_append_right b b'))) a
    -- the far decay of the output of the first step
  have hP : (1 - s) / (1 - t) ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hP0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  have hstage1far : ∀ b : Fin k → Zd d L,
      ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) →
      ‖Ugen d L g E (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ W ^ k * δ := by
    intro b hfar
    have hT' : ‖(fun b' => T b b')‖ ≤ δ :=
      (pi_norm_le_iff_of_nonneg hδ).mpr fun b' =>
        hTfar b b' (hfar.trans (by exact_mod_cast nqGood1_diam_append_left b b'))
    have h1 := norm_UN_apply_le (d := d) (L := L) (g := g) hL
      (m := fun i => mSigma E (!σ i)) (fun i => norm_mSigma hE _) hs hst ht1
      (fun b' => T b b') a
    calc _ ≤ ((1 - s) / (1 - t)) ^ k * ‖(fun b' => T b b')‖ := h1
      _ ≤ W ^ k * δ := by gcongr
  have hδ2 : W ^ k * δ ≤ W ^ (-(D - k)) := by
    calc W ^ k * δ ≤ W ^ k * W ^ (-D) := by gcongr
      _ = W ^ (-(D - k)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hW0]
          congr 1; ring
  have hstage2 := hker_of_case1N Λg κ' hd hk hΛ hκ' hL hg hgΛ hW hε0 hε1 hWε hdW
    (D := D - k) (by linarith) hs hst ht hWt hE hκm hσ
    (fun b => Ugen d L g E (fun i => !σ i) s t (fun b' => T b b') a)
    (M := κ1 * Mee + W ^ C * δ) (δ := W ^ k * δ)
    (add_nonneg (mul_nonneg hκ10 hMee0) (mul_nonneg hWC0 hδ))
    (mul_nonneg (pow_nonneg hW0.le _) hδ) hδ2 hstage1 hstage1far a
  calc _ ≤ _ := hstage2
    _ = _ := by ring

/-- **The quadratic-variation majorant of `qvFormN` from bounds on `𝓔⊗𝓔`** (`Re ≤ ‖·‖` and
`qvFormN_eq_re_UgenPairN`): if the pair form `STeeM n E v M σ b b'` is `≤ M_ee` and `≤ δ ≤ W^{-D}`
when `ℓ_v W^{τ'} ≤ diam_∞(b,b')`, then `qvFormN_{v,w,σ}(M)(a) ≤ κ₁ (κ₁ M_ee + W^C δ) + W^C W^k δ`
(`v = s`, `t = w` in `nqGood1_ugenPairN_le_of_bounds`).  The time of the matrix `M` need not be `v`: the
shift `u_j → u_{j+1}` enters through `M_ee`, `δ` (`norm_STeeM_shiftN_le`). -/
theorem nqGood1_qvFormN_le_of_bounds {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg)
    (hκ' : 0 < κ') (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg)
    {ε τ' D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hD : (k : ℝ) + 1 < D)
    {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - v)) {E : ℝ} (hE : |E| ≤ 2)
    (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {Mee δ : ℝ}
    (hδ : 0 ≤ δ) (hδD : δ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hT : ∀ b b' : Fin k → Zd d (sz.L n), ‖sz.STeeM n E v M σ b b'‖ ≤ Mee)
    (hTfar : ∀ b b' : Fin k → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) →
        ‖sz.STeeM n E v M σ b b'‖ ≤ δ)
    (a : Fin k → Zd d (sz.L n)) :
    qvFormN sz n E v w σ M a ≤
      ((((sz.W n : ℕ) : ℝ)) ^ (nqGood1C d k Λg κ' * ε) *
          ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
        ((((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) *
            ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) * Mee +
          ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * δ) +
        ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * (((sz.W n : ℕ) : ℝ) ^ k * δ) := by
  have hL3 := sz.three_le_L n
  have hLpos : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hw1 : w < 1 := by
    have : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  rw [qvFormN_eq_re_UgenPairN sz n hE (abs_lt.2 ⟨by linarith, hw1⟩)]
  refine (Complex.re_le_norm _).trans ?_
  exact nqGood1_ugenPairN_le_of_bounds Λg κ' hd hk hΛ hκ' hL3 hg hgΛ hW hε0 hε1 hWε hdW hD hv0 hvw hwL
    hWt hE hκm hσ (fun b b' => sz.STeeM n E v M σ b b') hδ hδD hT hTfar a

end QVBound

/-! ## 5. The good-set shift `u_j → u_{j+1}` -/

section Shift

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `‖G(z') - G(z)‖ ≤ η⁻¹ ‖z' - z‖ η⁻¹` for one signed Green factor (resolvent identity). -/
private theorem nqGood1_norm_Gres_sub_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    (s : Bool) : ‖Gres H z' s - Gres H z s‖ ≤ η⁻¹ * ‖z' - z‖ * η⁻¹ := by
  have hz0 : z.im ≠ 0 := abs_pos.mp (hη.trans_le hz)
  have hz0' : z'.im ≠ 0 := abs_pos.mp (hη.trans_le hz')
  have h1 := isUnit_sub_zSig hH hz0 s
  have h2 := isUnit_sub_zSig hH hz0' s
  have hG : ‖Gres H z s‖ ≤ η⁻¹ := (norm_Gsig_le hH hz0 s).trans (inv_anti₀ hη hz)
  have hG' : ‖Gres H z' s‖ ≤ η⁻¹ := (norm_Gsig_le hH hz0' s).trans (inv_anti₀ hη hz')
  have e : Gres H z' s - Gres H z s = (zSig z' s - zSig z s) • (Gres H z' s * Gres H z s) := by
    rw [Gres_eq_green_zSig, Gres_eq_green_zSig]
    exact green_sub_green h2 h1
  rw [e, norm_smul, norm_zSig_sub_zSig]
  calc ‖z' - z‖ * ‖Gres H z' s * Gres H z s‖ ≤ ‖z' - z‖ * (η⁻¹ * η⁻¹) :=
        mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
          (mul_le_mul hG' hG (norm_nonneg _) (by positivity))) (norm_nonneg _)
    _ = η⁻¹ * ‖z' - z‖ * η⁻¹ := by ring

/-- `‖C_{σ,a}(z') - C_{σ,a}(z)‖ ≤ |σ| η^{-(|σ|+1)} (W^{-d})^{|a|} |z' - z|` for a `G`-chain: the
telescoping `G'E C' - G E C = (G' - G) E C' + G E (C' - C)`. -/
private theorem nqGood1_norm_gchain_sub_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    {σ : List Bool} {a : List (Zd d L)} (h : σ.length = a.length + 1) :
    ‖gchain d L W H z' σ a - gchain d L W H z σ a‖ ≤
      (σ.length : ℝ) * (η⁻¹ ^ (σ.length + 1) * (((W : ℝ) ^ d)⁻¹) ^ a.length * ‖z' - z‖) := by
  have hz0' : z'.im ≠ 0 := abs_pos.mp (hη.trans_le hz')
  have hη0 : 0 ≤ η⁻¹ := (inv_pos.2 hη).le
  have hGle : ∀ (w : ℂ) (s : Bool), η ≤ |w.im| → ‖Gres H w s‖ ≤ η⁻¹ := by
    intro w s hw
    exact (norm_Gsig_le hH (abs_pos.mp (hη.trans_le hw)) s).trans (inv_anti₀ hη hw)
  have hW0 : 0 ≤ (((W : ℝ) ^ d)⁻¹) := by positivity
  induction σ generalizing a with
  | nil => simp at h
  | cons s σ ih =>
    cases a with
    | nil =>
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hσ
      have := nqGood1_norm_Gres_sub_le hH hη hz hz' s
      simp only [gchain_single, List.length_cons, List.length_nil, Nat.cast_one, zero_add,
        pow_zero, mul_one, one_mul]
      calc ‖Gres H z' s - Gres H z s‖ ≤ η⁻¹ * ‖z' - z‖ * η⁻¹ := this
        _ = η⁻¹ ^ 2 * ‖z' - z‖ := by ring
    | cons b a =>
      have h' : σ.length = a.length + 1 := by simpa using h
      have hC' : ‖gchain d L W H z' σ a‖ ≤ η⁻¹ ^ σ.length * (((W : ℝ) ^ d)⁻¹) ^ a.length := by
        refine (norm_gchain_le hH hz0' h').trans ?_
        gcongr
      have hrec := ih h'
      have hE := norm_Eblk_le (W := W) b
      have hGd := nqGood1_norm_Gres_sub_le hH hη hz hz' s
      have hGz := hGle z s hz
      have hsplit : gchain d L W H z' (s :: σ) (b :: a) - gchain d L W H z (s :: σ) (b :: a) =
          (Gres H z' s - Gres H z s) * Eblk d L W b * gchain d L W H z' σ a +
            Gres H z s * Eblk d L W b * (gchain d L W H z' σ a - gchain d L W H z σ a) := by
        rw [gchain_cons, gchain_cons]; noncomm_ring
      rw [hsplit, List.length_cons, List.length_cons]
      refine (norm_add_le _ _).trans ?_
      have e1 : ‖(Gres H z' s - Gres H z s) * Eblk d L W b * gchain d L W H z' σ a‖ ≤
          (η⁻¹ * ‖z' - z‖ * η⁻¹) * (((W : ℝ) ^ d)⁻¹) *
            (η⁻¹ ^ σ.length * (((W : ℝ) ^ d)⁻¹) ^ a.length) := by
        refine (norm_mul_le _ _).trans ?_
        refine mul_le_mul ((norm_mul_le _ _).trans ?_) hC' (norm_nonneg _) (by positivity)
        exact mul_le_mul hGd hE (norm_nonneg _) (by positivity)
      have e2 : ‖Gres H z s * Eblk d L W b * (gchain d L W H z' σ a - gchain d L W H z σ a)‖ ≤
          η⁻¹ * (((W : ℝ) ^ d)⁻¹) * ((σ.length : ℝ) *
            (η⁻¹ ^ (σ.length + 1) * (((W : ℝ) ^ d)⁻¹) ^ a.length * ‖z' - z‖)) := by
        refine (norm_mul_le _ _).trans ?_
        refine mul_le_mul ((norm_mul_le _ _).trans ?_) hrec (norm_nonneg _) (by positivity)
        exact mul_le_mul hGz hE (norm_nonneg _) hη0
      refine (add_le_add e1 e2).trans (le_of_eq ?_)
      push_cast
      ring

/-- The shift error of one loop of length `ℓ`: `ℓ η^{-(ℓ+1)} (W^{-d})^{ℓ-1} Δ`
(`Δ = u' - u`, `η = η_{u'}`), the right-hand side of `norm_loopL_zshiftN_le` at `|z' - z| = Δ`. -/
def loopShiftErrN (d W : ℕ) (η : ℝ) (ℓ : ℕ) (Δ : ℝ) : ℝ :=
  (ℓ : ℝ) * (η⁻¹ ^ (ℓ + 1) * (((W : ℝ) ^ d)⁻¹) ^ (ℓ - 1) * Δ)

theorem nqGood1_loopShiftErrN_nonneg {η Δ : ℝ} (hη : 0 ≤ η) (hΔ : 0 ≤ Δ) (d W ℓ : ℕ) :
    0 ≤ loopShiftErrN d W η ℓ Δ := by
  unfold loopShiftErrN
  have : 0 ≤ η⁻¹ := inv_nonneg.2 hη
  positivity

/-- **Spectral-parameter shift of one loop** at a fixed Hermitian matrix (as RBM2D's
`norm_gloop_zshiftN_le`; `d ≥ 3`: the loop has
`ℓ` edges and `ℓ - 1` insertions `E_a` of operator norm `W^{-d}`):
`|𝓛(z') - 𝓛(z)| ≤ ℓ η^{-(ℓ+1)} (W^{-d})^{ℓ-1} |z' - z|` for `|Im z|, |Im z'| ≥ η`. -/
theorem norm_loopL_zshiftN_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.σ.length = I.a.length) (hlen : 1 ≤ I.a.length) :
    ‖loopL d L W H z' I - loopL d L W H z I‖ ≤
      (I.a.length : ℝ) * (η⁻¹ ^ (I.a.length + 1) * (((W : ℝ) ^ d)⁻¹) ^ (I.a.length - 1) *
        ‖z' - z‖) := by
  obtain ⟨σ, a⟩ := I
  simp only at hwf hlen ⊢
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', b, rfl⟩
  · simp at hlen
  have h : σ.length = a'.length + 1 := by simpa using hwf
  have hd := nqGood1_norm_gchain_sub_le hH hη hz hz' h
  have e : loopL d L W H z' ⟨σ, a' ++ [b]⟩ - loopL d L W H z ⟨σ, a' ++ [b]⟩ =
      Matrix.trace ((gchain d L W H z' σ a' - gchain d L W H z σ a') * Eblk d L W b) := by
    rw [← trace_gchain_mul_Eblk h b, ← trace_gchain_mul_Eblk h b, sub_mul, Matrix.trace_sub]
  rw [e]
  refine (split_norm_trace_mul_Eblk_le _ b).trans (hd.trans (le_of_eq ?_))
  simp [h]

/-- `|Im z_u| = η_u` for `u < 1`. -/
private theorem nqGood1_abs_zt_im {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) :
    |(zt E u).im| = etaT E u := by
  rw [zt_im, abs_of_pos (mul_pos (by linarith) (mE_im_pos hE))]
  rfl

/-- `|z_{u'} - z_u| = |u' - u|` (`|m| = 1`). -/
private theorem nqGood1_norm_zt_sub {E : ℝ} (hE : |E| < 2) (u u' : ℝ) :
    ‖zt E u' - zt E u‖ = |u' - u| := by
  have h : zt E u' - zt E u = ((u - u' : ℝ) : ℂ) * mE E := by
    simp only [zt]; push_cast; ring
  rw [h, norm_mul, norm_mE hE.le, Complex.norm_real, Real.norm_eq_abs, mul_one, abs_sub_comm]

/-- `η_u ≤ 1` for `0 ≤ u` (`Im m ≤ |m| = 1`). -/
private theorem nqGood1_etaT_le_one {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) :
    etaT E u ≤ 1 := by
  unfold etaT
  have hm : (mE E).im ≤ 1 := by
    have := Complex.abs_im_le_norm (mE E)
    rw [norm_mE hE.le] at this
    exact (le_abs_self _).trans this
  have hm0 := (mE_im_pos hE).le
  nlinarith

/-- `η_{u'} ≤ η_u` for `u ≤ u'`. -/
private theorem nqGood1_etaT_anti {E : ℝ} (hE : |E| < 2) {u u' : ℝ} (hu : u ≤ u') :
    etaT E u' ≤ etaT E u := by
  unfold etaT
  have := (mE_im_pos hE).le
  nlinarith

end Shift

section ShiftSz

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d)

/-- `ℓ_u ≤ ℓ_{u'}` for every real `g` (`ellT_mono` needs `0 ≤ g`, and `0 ≤ sz.lam n` is not a field
of `Sizes`: for `g < 0` both sides are `min 1 L`). -/
theorem nqGood1_ellT_mono (L : ℕ) (g : ℝ) {u t : ℝ} (hut : u ≤ t) (ht : t < 1) :
    ellT L g u ≤ ellT L g t := by
  by_cases hg : 0 ≤ g
  · exact ellT_mono hg hut ht
  · have hg' : g < 0 := not_le.1 hg
    unfold ellT
    have h1 : ∀ x : ℝ, g / Real.sqrt |1 - x| ≤ 0 := fun x =>
      div_nonpos_of_nonpos_of_nonneg hg'.le (Real.sqrt_nonneg _)
    rw [max_eq_right ((h1 u).trans zero_le_one), max_eq_right ((h1 t).trans zero_le_one)]

/-- **Crude loop bound** (as RBM2D's `norm_gloop_crudeN`): `|𝓛_{u,σ,a}(M)| ≤ η_u^{-ℓ}` for Hermitian
`M`, `ℓ ≥ 1` (`d ≥ 3` has the sharper `η^{-ℓ} (W^{-d})^{ℓ-1}`, `norm_gloop_le_of_le_abs_im`). -/
theorem norm_loopFine_crudeN (n : ℕ) {E : ℝ} (hE : |E| < 2)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    {u : ℝ} (hu1 : u < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d (sz.L n)) :
    ‖loopFine d (sz.L n) (sz.W n) M (zt E u) σ a‖ ≤ (etaT E u)⁻¹ ^ ℓ := by
  have hη := etaT_pos hE hu1
  have hMb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hM.submatrix _
  have hwf : (loopOf σ a).σ.length = (loopOf σ a).a.length := by simp [loopOf]
  have hlen : (loopOf σ a).a.length = ℓ := by simp [loopOf]
  have h := norm_gloop_le_of_le_abs_im hMb hη (le_of_eq (nqGood1_abs_zt_im hE hu1).symm)
    (loopOf σ a) hwf (by rw [hlen]; exact hℓ)
  rw [hlen] at h
  unfold loopFine
  rw [loopM_eq_loopL]
  refine h.trans ?_
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWi : (((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹) ^ (ℓ - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW))
  have h0 : 0 ≤ (etaT E u)⁻¹ ^ ℓ := by positivity
  calc (etaT E u)⁻¹ ^ ℓ * (((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹) ^ (ℓ - 1)
      ≤ (etaT E u)⁻¹ ^ ℓ * 1 := mul_le_mul_of_nonneg_left hWi h0
    _ = _ := mul_one _

/-- **The crude `(𝓛-𝒦)` envelope** (as RBM2D's `norm_lk_envN`): for Hermitian `M`,
`0 ≤ u < 1` and a bound `‖𝒦^{(m)}_{u,σ,a}‖ ≤ M_K` for the loops of length `m ≤ n'`, the matrix-level
maximum satisfies `max|𝓛 - 𝒦| ≤ η_u^{-n'} + M_K` (`1 ≤ m ≤ n'`). -/
theorem STmaxLKM_crudeN (n : ℕ) {E : ℝ} (hE : |E| < 2)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {n' m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n') {MK : ℝ}
    (hK : ∀ (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), ‖STKloop sz n E u σ a‖ ≤ MK) :
    sz.STmaxLKM n E u m M ≤ (etaT E u)⁻¹ ^ n' + MK := by
  have hη := etaT_pos hE hu1
  have hη1 : 1 ≤ (etaT E u)⁻¹ := (one_le_inv₀ hη).mpr (nqGood1_etaT_le_one hE hu0)
  unfold STmaxLKM
  refine Finset.sup'_le _ _ fun p _ => ?_
  have h1 := norm_loopFine_crudeN sz n hE hM hu1 hm p.1 p.2
  have h2 : (etaT E u)⁻¹ ^ m ≤ (etaT E u)⁻¹ ^ n' := pow_le_pow_right₀ hη1 hmn
  have h3 := hK p.1 p.2
  calc _ ≤ ‖loopFine d (sz.L n) (sz.W n) M (zt E u) p.1 p.2‖ + ‖STKloop sz n E u p.1 p.2‖ :=
        norm_sub_le _ _
    _ ≤ _ := by linarith

/-- **Crude bound on `Ξ̂^{(𝓛-𝒦)}_m(M)`**: for `1 ≤ m ≤ n'` and `B_u ≤ 1`,
`Ξ̂^{(𝓛-𝒦)}_m ≤ 1 + (η_u^{-n'} + M_K) / B_u^{n'}`. -/
theorem STXiLKM_crudeN (n : ℕ) {E : ℝ} (hE : |E| < 2)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hB1 : sz.Bctl n u ≤ 1) {n' m : ℕ} (hm : 1 ≤ m)
    (hmn : m ≤ n') {MK : ℝ}
    (hK : ∀ (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), ‖STKloop sz n E u σ a‖ ≤ MK) :
    sz.STXiLKM n E u m M ≤ 1 + ((etaT E u)⁻¹ ^ n' + MK) / (sz.Bctl n u) ^ n' := by
  have hB : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu1
  have h1 := STmaxLKM_crudeN sz n hE hM hu0 hu1 hm hmn hK
  have h0 : 0 ≤ sz.STmaxLKM n E u m M :=
    Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))))
      (norm_nonneg _)
  have hpow : (sz.Bctl n u) ^ n' ≤ (sz.Bctl n u) ^ m := pow_le_pow_of_le_one hB.le hB1 hmn
  unfold STXiLKM
  have h2 : sz.STmaxLKM n E u m M / (sz.Bctl n u) ^ m ≤
      sz.STmaxLKM n E u m M / (sz.Bctl n u) ^ n' :=
    div_le_div_of_nonneg_left h0 (pow_pos hB _) hpow
  have h3 : sz.STmaxLKM n E u m M / (sz.Bctl n u) ^ n' ≤
      ((etaT E u)⁻¹ ^ n' + MK) / (sz.Bctl n u) ^ n' :=
    div_le_div_of_nonneg_right h1 (pow_pos hB _).le
  linarith

/-- The shift error of the pair form at loop length `2k+2`:
`W^d · k · L^d · (2k+2) η_{u'}^{-(2k+3)} (W^{-d})^{2k+1} (u'-u)` (`Σ_{b,b'} |S^{(B)}_{bb'}| = L^d`). -/
def eeShiftErrN (d L W : ℕ) (E : ℝ) (k : ℕ) (u u' : ℝ) : ℝ :=
  ((W : ℝ) ^ d) * ((k : ℝ) * (((L : ℝ) ^ d) * loopShiftErrN d W (etaT E u') (2 * k + 2) (u' - u)))

private theorem nqGood1_sum_sum_norm_SB {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) :
    ∑ b : Zd d L, ∑ b' : Zd d L, ‖SB d L g b b'‖ = (L : ℝ) ^ d := by
  simp only [sum_norm_SB_row d L g hL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : Fintype.card (Zd d L) = L ^ d := by simp [Zd, ZMod.card]
  rw [this]
  push_cast
  rfl

/-- **The shift of the pair form** (as RBM2D's `norm_eeN_shiftN_le`): `|(𝓔⊗𝓔)_{u'} - (𝓔⊗𝓔)_u| ≤
eeShiftErrN` for Hermitian `M` (`STeeM` contains `𝓛` only, no `𝒦`, so only the loop shift of
`norm_loopL_zshiftN_le` enters). -/
theorem norm_STeeM_shiftN_le (n : ℕ) {E : ℝ} (hE : |E| < 2)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    {u u' : ℝ} (huu' : u ≤ u') (hu'1 : u' < 1) {k : ℕ} (σ : Fin k → Bool)
    (a a' : Fin k → Zd d (sz.L n)) :
    ‖sz.STeeM n E u' M σ a a' - sz.STeeM n E u M σ a a'‖ ≤
      eeShiftErrN d (sz.L n) (sz.W n) E k u u' := by
  have hW2 : ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
  have hδ0 := nqGood1_loopShiftErrN_nonneg (etaT_pos hE hu'1).le (by linarith : 0 ≤ u' - u) d (sz.W n)
    (2 * k + 2)
  have hMb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hM.submatrix _
  have hη := etaT_pos hE hu'1
  have hz : etaT E u' ≤ |(zt E u).im| := by
    rw [nqGood1_abs_zt_im hE (huu'.trans_lt hu'1)]; exact nqGood1_etaT_anti hE huu'
  have hz' : etaT E u' ≤ |(zt E u').im| := by rw [nqGood1_abs_zt_im hE hu'1]
  unfold STeeM
  rw [← mul_sub, norm_mul, hW2]
  have key : ‖∑ k' ∈ Finset.Icc 1 k, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        SB d (sz.L n) (sz.lam n) b b' *
          sz.STLIM n E u' M (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') -
      ∑ k' ∈ Finset.Icc 1 k, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        SB d (sz.L n) (sz.lam n) b b' *
          sz.STLIM n E u M (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b')‖ ≤
      (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
        loopShiftErrN d (sz.W n) (etaT E u') (2 * k + 2) (u' - u)) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k' ∈ Finset.Icc 1 k, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
          ‖SB d (sz.L n) (sz.lam n) b b'‖ *
            loopShiftErrN d (sz.W n) (etaT E u') (2 * k + 2) (u' - u) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
          simp only [Finset.mem_Icc] at hk'
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
          rw [← mul_sub, norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hwf := eeLoop_WF (List.ofFn σ) (List.ofFn a) (List.ofFn a') hk'.1
            (by simpa using hk'.2) (by simp) (by simp) b b'
          have hlenE : (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').a.length =
              2 * k + 2 := by
            have := length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := k')
              (by simp; omega) (by simp) b b'
            simpa [LoopIdx.length] using this
          have h1 := norm_loopL_zshiftN_le hMb hη hz hz'
            (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') hwf
            (by rw [hlenE]; omega)
          rw [hlenE, nqGood1_norm_zt_sub hE, abs_of_nonneg (by linarith)] at h1
          unfold STLIM loopShiftErrN
          exact h1
      _ = (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
          loopShiftErrN d (sz.W n) (etaT E u') (2 * k + 2) (u' - u)) := by
          simp only [← Finset.sum_mul, nqGood1_sum_sum_norm_SB (sz.lam n) (sz.three_le_L n),
            Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          ring
  unfold eeShiftErrN
  exact mul_le_mul_of_nonneg_left key (by positivity)

end ShiftSz

end RBM.Ind
