/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistStep
import RBM3D.BA.EMn2BA
import RBM3D.BA.KInduct

/-!
# The untwisted BA grid martingale statement from the twisted one

Paper: Lemma 3.4 (`Sol_CalL`) and Lemma 3.6 (`lem:DIfREP`), at block Anderson Section 8 (the twisted loops,
Lemma 8.6 `lem:TL1_BA`, (8.4) `eq:TL2_BA`).

* `BAGridBridge`, `baGridBridge_holds`: the three identities at `c₁ = c₂ = a 1`
  along the grid, eventually along a BA flow: (H1) the observable `Z̃ = L̃ - K̃` is
  `(𝓛-𝒦)^{(2)}` (`STgAg`), (H2) the twisted drift is `STgDriftg`, (H3′) `‖Ẽ⊗Ẽ‖ ≤ 2 ‖STEEMg‖`
  (an inequality: the twisted gradient `∂L̃ = -(Q₁ + Q₂)` has two slots, `STEEMg`
  is the sum of the two diagonal 6-loops).
* `baGridMart_holds`: `STGridMartgL` at `baStep2Mat` along `BAFlow`, from
  `baTwistGridMart_holds` and `baGridBridge_holds` (the glue `GridMartBA_bridge` is private: it takes the
  statement `BATwistGridMartAt` as a hypothesis).  Clause (iii) of the statement lies inside
  clause (iii) of the twisted one at `ε'/2`, eventually in `n` (`N^{ε'/2} ≥ 2`).

Every statement is for every `d` (no `3 ≤ d`).  The names of the private helpers begin with GridMartBA_.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open private TwistGrid_Pb TwistGrid_twL2M_trace TwistGrid_twL3M_trace TwistGrid_LM_two
  from RBM3D.BA.TwistGrid
open private TwistKer_loopFine_eq TwistKer_fE TwistKer_fE_apply TwistKer_trace_sandwich TwistKer_Gres_conjTranspose
  from RBM3D.BA.TwistKer

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The three identities -/

/-- **`BAGridBridge`** (the three identities at `c₁ = c₂ = a 1`): along the grid
`k ≤ K n`, eventually in `n` along a BA flow, (H1) `twAk = STgAg`, (H2) `twDriftk = STgDriftg`, (H3′) `‖twEEk‖ ≤ 2 ‖STEEMg‖`. -/
def BAGridBridge (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ∀ k ≤ K n, ∀ ω : PathΩ sz,
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 1) (a 1) k ω (a 0) =
            STgAg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω =
            STgDriftg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω‖ ≤
            2 * ‖STEEMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n k)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n k ω) σ a‖

/-! ## 2. Matrix facts at one size index and a Hermitian matrix -/

section Pointwise

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- The grid walk is Hermitian (`g₀` real, `Ψ` Hermitian, `pathH` Hermitian). -/
private theorem GridMartBA_Hpath_herm (s t : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ) (ω : PathΩ sz) :
    ((baStep2Mat sz lam0 E).Hpath s t K n k ω).IsHermitian := by
  rw [baStep2Mat_Hpath]
  refine Matrix.IsHermitian.add ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d (sz.L n) (sz.W n)).eq,
      show star ((lam0 n : ℝ) : ℂ) = ((lam0 n : ℝ) : ℂ) from Complex.conj_ofReal _]
  · exact pathH_isHermitian (sz.withLam 0) s t K n k ω

/-- `P_{cc} = E_c` on the block-product index. -/
private theorem GridMartBA_Pb_diag (c : Zd d (sz.L n)) :
    TwistGrid_Pb (d := d) (L := sz.L n) (W := sz.W n) c c = Eblk d (sz.L n) (sz.W n) c := by
  ext p q
  simp only [TwistGrid_Pb, Matrix.of_apply, Eblk, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    by_cases hp : p.1 = c <;> simp [hp]
  · have h' : ¬ (p.1 = c ∧ q.1 = c ∧ p.2 = q.2) := fun ⟨h1, h2, h3⟩ => h (Prod.ext (h1.trans h2.symm) h3)
    simp [h, h']

/-- **H1, loop part**: `L̃_{σ,(a;c,c)} = 𝓛^{(2)}_{σ,(a,c)}` for Hermitian `H`. -/
private theorem GridMartBA_twL2M_diag (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (a c : Zd d (sz.L n)) :
    twL2M sz lam0 E n u H σ a c c = (baStep2Mat sz lam0 E).LM n u H σ ![a, c] := by
  rw [TwistGrid_twL2M_trace sz lam0 E n u hH σ a c c, TwistGrid_LM_two sz lam0 E n u H σ a c, GridMartBA_Pb_diag]

/-- The 3-loop as a trace on the block-product index. -/
private theorem GridMartBA_LM_three (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 3 → Bool) (a b c : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H σ ![a, b, c] =
      Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * Eblk d (sz.L n) (sz.W n) a *
        Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) * Eblk d (sz.L n) (sz.W n) b *
        Gres (blockMat d (sz.L n) (sz.W n) H) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 2) * Eblk d (sz.L n) (sz.W n) c) := by
  simp [baStep2Mat, loopFine, loopM, List.ofFn_succ, Matrix.mul_assoc]

/-- **Ẽ^{G̊}, loop part**: `L̃^{(3)}_{σ,(a₁,a₂;c,c)} = 𝓛^{(3)}_{σ,(a₁,a₂,c)}` for Hermitian `H`. -/
private theorem GridMartBA_twL3M_diag (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 3 → Bool) (a₁ a₂ c : Zd d (sz.L n)) :
    twL3M sz lam0 E n u H σ a₁ a₂ c c = (baStep2Mat sz lam0 E).LM n u H σ ![a₁, a₂, c] := by
  rw [TwistGrid_twL3M_trace sz lam0 E n u hH σ a₁ a₂ c c, GridMartBA_LM_three sz lam0 E n u H σ a₁ a₂ c,
    GridMartBA_Pb_diag]

/-- `twMB` is `M^{(B)}` at the BA carrier (`BAMfine_eq`). -/
private theorem GridMartBA_twMB (hm : 0 < (BAmF sz lam0 E n).im) :
    twMB (baFM sz lam0 E) n = BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) := by
  ext a b
  have ha : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (a, 0)) = (a, 0) :=
    (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
  have hb : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (b, 0)) = (b, 0) :=
    (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
  simp only [twMB, Matrix.of_apply, baFM]
  rw [BAMfine_eq sz _ _ n hm]
  change (if (split d (sz.L n) (sz.W n) _).2 = (split d (sz.L n) (sz.W n) _).2 then _ else _) = _
  rw [ha, hb]
  exact ite_eq_left_iff.mpr fun h => absurd rfl h

/-- `K̃_{σ,(a;c,c)} = W^{-d} (Θ_u M^{(σ₀σ₁)})(a, c)` (the twist at `c₁ = c₂` is the plain matrix product). -/
private theorem GridMartBA_twK_diag (hm : 0 < (BAmF sz lam0 E n).im) (u : ℝ) (σ : Fin 2 → Bool) (a c : Zd d (sz.L n)) :
    twK (baFM sz lam0 E) n u σ a c c = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      (BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) a c := by
  unfold twK
  rw [GridMartBA_twMB sz lam0 E n hm]
  congr 1
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [BATheta, BAMss, Matrix.of_apply]
  ring

/-- `𝒦^{(2)}_{σ,a} = W^{-d} (Θ_u M^{(σ₀σ₁)})(a₀, a₁)` at the BA carrier (`baKsol_two`). -/
private theorem GridMartBA_K_two {κ : ℝ} (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    (baFM sz lam0 E).K n u σ a = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      (BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) (a 0) (a 1) :=
  baKsol_two d hκ hg (sz.three_le_L n) (sz.W n) hr hu σ a

/-- **H1, the `K`-part**: `K̃_{σ,(a₀;a₁,a₁)} = 𝒦^{(2)}_{σ,a}`. -/
private theorem GridMartBA_K_eq {κ : ℝ} (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    twK (baFM sz lam0 E) n u σ (a 0) (a 1) (a 1) = (baFM sz lam0 E).K n u σ a := by
  rw [GridMartBA_K_two sz lam0 E n hκ hg hr hu σ a, GridMartBA_twK_diag sz lam0 E n (lt_of_lt_of_le hκ hr.2) u σ (a 0) (a 1)]

/-- **H1** (pointwise, at a Hermitian `H`): `Z̃ = L̃ - K̃` at `c₁ = c₂ = a 1` is `(𝓛-𝒦)^{(2)}_{σ,a}`. -/
private theorem GridMartBA_H1 {κ : ℝ} (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    twL2M sz lam0 E n u H σ (a 0) (a 1) (a 1) - twK (baFM sz lam0 E) n u σ (a 0) (a 1) (a 1) =
      STLKMg (baStep2Mat sz lam0 E) n u H σ a := by
  have ha : a = ![a 0, a 1] := by
    ext i; fin_cases i <;> rfl
  rw [GridMartBA_twL2M_diag sz lam0 E n u hH σ (a 0) (a 1), GridMartBA_K_eq sz lam0 E n hκ hg hr hu σ a]
  unfold STLKMg STLMg
  rw [← ha]
  rfl

/-! ## 3. H2: the drift -/

/-- `M^{(σ'σ)} = (M^{(σσ')})ᵀ` for every `M` (commutativity of `ℂ`; as the private `BAKTreeDeriv_Mss_swap`). -/
private theorem GridMartBA_Mss_swap {L : ℕ} (B : Matrix (Zd d L) (Zd d L) ℂ) (s s' : Bool) :
    BAMss d L B s' s = (BAMss d L B s s')ᵀ := by
  ext a b
  simp only [BAMss, Matrix.of_apply, Matrix.transpose_apply, mul_comm]

/-- `Θ^{(σ'σ)} = (Θ^{(σσ')})ᵀ` (as the private `BAKTreeDeriv_Theta_swap`: `Ring.inverse` commutes with `ᵀ`). -/
private theorem GridMartBA_Theta_swap {L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) :
    BATheta d L g E m t s' s = (BATheta d L g E m t s s')ᵀ := by
  unfold BATheta PropThetaQ
  rw [GridMartBA_Mss_swap, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]

/-- **The transposition of the drift kernel at `S = 1`**: `thetaKer(σ',σ)(a, b) = thetaKer(σ,σ')(b, a)`
(`(M^{(σσ')})ᵀ = M^{(σ'σ)}`, `Θ` a function of `M`). -/
private theorem GridMartBA_thetaKer_swap (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (u : ℝ) (σ σ' : Bool)
    (a b : Zd d (sz.L n)) :
    Step2Gen_thetaKer (baFM sz lam0 E) n σ' σ u a b = Step2Gen_thetaKer (baFM sz lam0 E) n σ σ' u b a := by
  rw [Step2Kern_thetaKer_BA sz lam0 E n hIm σ' σ u, Step2Kern_thetaKer_BA sz lam0 E n hIm σ σ' u,
    GridMartBA_Theta_swap, GridMartBA_Mss_swap]
  have hc : BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ' *
        BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u σ σ' =
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u σ σ' *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ' :=
    Step2Kern_Theta_comm (BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ') (u : ℂ)
  rw [← Matrix.transpose_mul, hc, Matrix.transpose_apply]

/-- `STthetaOpg` is the sum of its two slots, with `update a 0 b = ![b, a 1]`, `update a 1 b = ![a 0, b]`. -/
private theorem GridMartBA_STthetaOpg_two (u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) :
    STthetaOpg (baStep2Mat sz lam0 E) n u σ A a =
      ∑ b, Step2Gen_thetaKer (baFM sz lam0 E) n (σ 0) (σ 1) u (a 0) b * A ![b, a 1] +
        ∑ b, Step2Gen_thetaKer (baFM sz lam0 E) n (σ 1) (σ 0) u (a 1) b * A ![a 0, b] := by
  unfold STthetaOpg
  rw [Fin.sum_univ_two]
  have h0 : ∀ b, Function.update a 0 b = ![b, a 1] := fun b => by
    ext i; fin_cases i <;> simp
  have h1 : ∀ b, Function.update a 1 b = ![a 0, b] := fun b => by
    ext i; fin_cases i <;> simp
  have f0 : finRotate 2 0 = 1 := by decide
  have f1 : finRotate 2 1 = 0 := by decide
  simp only [h0, h1, f0, f1]
  rfl

/-- **H2** (pointwise, at a Hermitian `H`): the twisted drift `Θ̃∘Z + B̃₁ + B̃₂ + Ẽ^{G̊}` at `c₁ = c₂ = a 1` is
`Θ^{(2)}∘(𝓛-𝒦)^{(2)} + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{G̃}` (`STthetaOpg + STELKLKMg + STEGtMg`, `S = 1`). -/
private theorem GridMartBA_H2 {κ : ℝ} (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    twDriftM sz lam0 E n u H σ (a 0) (a 1) (a 1) =
      STthetaOpg (baStep2Mat sz lam0 E) n u σ (STLKMg (baStep2Mat sz lam0 E) n u H σ) a +
        STELKLKMg (baStep2Mat sz lam0 E) n u H σ a + STEGtMg (baStep2Mat sz lam0 E) n u H σ a := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by simpa using hm.ne'
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  have hZ : ∀ b, twL2M sz lam0 E n u H σ b (a 1) (a 1) - twK (baFM sz lam0 E) n u σ b (a 1) (a 1) =
      STLKMg (baStep2Mat sz lam0 E) n u H σ ![b, a 1] := fun b => by
    simpa using GridMartBA_H1 sz lam0 E n hκ hg hr hu hH σ ![b, a 1]
  rw [GridMartBA_STthetaOpg_two]
  have e1 : ((BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) *ᵥ
        fun b => twL2M sz lam0 E n u H σ b (a 1) (a 1) - twK (baFM sz lam0 E) n u σ b (a 1) (a 1)) (a 0) =
      ∑ b, Step2Gen_thetaKer (baFM sz lam0 E) n (σ 0) (σ 1) u (a 0) b * STLKMg (baStep2Mat sz lam0 E) n u H σ ![b, a 1] := by
    rw [twTheta_eq_thetaKer sz lam0 E n hIm σ u]
    simp only [Matrix.mulVec, dotProduct, hZ]
  have e2 : twB1M sz lam0 E n u H σ (a 0) (a 1) (a 1) =
      ∑ b, Step2Gen_thetaKer (baFM sz lam0 E) n (σ 1) (σ 0) u (a 1) b * STLKMg (baStep2Mat sz lam0 E) n u H σ ![a 0, b] := by
    unfold twB1M
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GridMartBA_twK_diag sz lam0 E n hm u σ b (a 1), GridMartBA_thetaKer_swap sz lam0 E n hIm u (σ 0) (σ 1) (a 1) b,
      ← twTheta_eq_thetaKer sz lam0 E n hIm σ u]
    unfold STLKMg STLMg
    rw [← mul_assoc, mul_inv_cancel_left₀ hW]
  have e3 : twB2M sz lam0 E n u H σ (a 0) (a 1) (a 1) = STELKLKMg (baStep2Mat sz lam0 E) n u H σ a := by
    unfold twB2M STELKLKMg
    congr 1
    simp only [hZ]
    have hS : ∀ x y : Zd d (sz.L n), (baStep2Mat sz lam0 E).S n x y = if x = y then 1 else 0 := fun x y => by
      change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y = _
      rw [Matrix.one_apply]
    simp only [hS, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  have e4 : twEGM sz lam0 E n u H σ (a 0) (a 1) (a 1) = STEGtMg (baStep2Mat sz lam0 E) n u H σ a := by
    unfold twEGM STEGtMg STavgMg STmsigg
    have hS : ∀ x y : Zd d (sz.L n), (baStep2Mat sz lam0 E).S n x y = if x = y then 1 else 0 := fun x y => by
      change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y = _
      rw [Matrix.one_apply]
    have key : ∀ (A B : ℂ) (f g : Zd d (sz.L n) → ℂ) (x : Zd d (sz.L n)),
        ∑ y, (A * (baStep2Mat sz lam0 E).S n x y * f y + B * (baStep2Mat sz lam0 E).S n x y * g y) = A * f x + B * g x := by
      intro A B f g x
      rw [Finset.sum_add_distrib]
      simp [hS]
    have hvec : ∀ (τ : Bool) (x : Zd d (sz.L n)), STLMg (baStep2Mat sz lam0 E) n u H (fun _ : Fin 1 => τ) (fun _ => x) =
        (baStep2Mat sz lam0 E).LM n u H ![τ] ![x] := fun τ x => by
      unfold STLMg
      have h1 : (fun _ : Fin 1 => τ) = ![τ] := by funext i; fin_cases i; rfl
      have h2 : (fun _ : Fin 1 => x) = ![x] := by funext i; fin_cases i; rfl
      rw [h1, h2]
    simp only [key, hvec]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [GridMartBA_twL3M_diag sz lam0 E n u hH, GridMartBA_twL3M_diag sz lam0 E n u hH]
    rfl
  unfold twDriftM
  rw [e1, e2, e3, e4]

end Pointwise

/-! ## 4. H3′: the quadratic variation -/

section QV

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- `E_a = W^{-d} 1_{[a]}` is Hermitian. -/
private theorem GridMartBA_fE_herm (c : Zd d (sz.L n)) : (TwistKer_fE n c)ᴴ = TwistKer_fE n c := by
  ext i j
  rw [Matrix.conjTranspose_apply, TwistKer_fE_apply, TwistKer_fE_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : (split d (sz.L n) (sz.W n) i).1 = c <;> simp [hi]
  · have hji : ¬ j = i := fun h => hij h.symm
    simp [hij, hji]

/-- `(A E_b B E_c C)_{yx} = W^{-2d} Σ_{z∈[b]} Σ_{w∈[c]} A_{yz} B_{zw} C_{wx}`. -/
private theorem GridMartBA_chain (A B C : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (b c : Zd d (sz.L n))
    (y x : Idx d (sz.L n) (sz.W n)) :
    (A * TwistKer_fE n b * B * TwistKer_fE n c * C) y x =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, A y z * B z w * C w x := by
  set w₀ : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with hw₀
  have e1 : ∀ (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n)) (i j : Idx d (sz.L n) (sz.W n)),
      (M * TwistKer_fE n c) i j = M i j * (if (split d (sz.L n) (sz.W n) j).1 = c then w₀ else 0) := by
    intro M c i j
    simp [TwistKer_fE, Matrix.mul_diagonal, hw₀]
  rw [Matrix.mul_apply]
  simp only [e1, Matrix.mul_apply]
  simp only [twBlk, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : (split d (sz.L n) (sz.W n) z).1 = b
  · simp only [hz, ite_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : (split d (sz.L n) (sz.W n) w).1 = c
    · simp [hw]; ring
    · simp [hw]
  · simp [hz]

/-- `G(σ)` of the charged resolvent array: `twChg (twGM H) σ = Gres H z σ` for Hermitian `H`. -/
private theorem GridMartBA_chg (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (τ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    twChg (twGM sz lam0 E n u H) τ x y = Gres H (ztOf (BAmF sz lam0 E n) (E n) u) τ x y := by
  cases τ
  · have h := TwistKer_Gres_conjTranspose hH (ztOf (BAmF sz lam0 E n) (E n) u) true
    simp only [Bool.not_true] at h
    simp only [twChg, twGM, Bool.false_eq_true, ite_false]
    rw [← h, Matrix.conjTranspose_apply, Complex.star_def]
  · rfl

/-- The two slots of the gradient: `Q₁ = G(σ₀) E_b G(σ₁) E_c G(σ₀)`. -/
private def GridMartBA_Q1 (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (b c : Zd d (sz.L n)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * TwistKer_fE n b * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) *
    TwistKer_fE n c * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0)

/-- `Q₂ = G(σ₁) E_c G(σ₀) E_b G(σ₁)`. -/
private def GridMartBA_Q2 (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (b c : Zd d (sz.L n)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) * TwistKer_fE n c * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) *
    TwistKer_fE n b * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)

/-- **The gradient at `c₁ = c₂ = c`**: `∂_{xy} L̃_{σ,(b;c,c)} = -(Q₁ + Q₂)_{yx}` (Hermitian `H`). -/
private theorem GridMartBA_twDerM_eq (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (b c : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) :
    twDerM sz lam0 E n u H σ b c c x y =
      -(GridMartBA_Q1 sz lam0 E n u H σ b c + GridMartBA_Q2 sz lam0 E n u H σ b c) y x := by
  have hsh : ∀ w ∈ twBlk n c, twShift (sz := sz) n c w = w := fun w hw => by
    have h1 : (split d (sz.L n) (sz.W n) w).1 = c := by simpa [twBlk] using hw
    unfold twShift
    rw [← h1]
    exact (splitEquiv d (sz.L n) (sz.W n)).symm_apply_apply w
  unfold twDerM
  simp only [GridMartBA_chg sz lam0 E n u hH]
  rw [Matrix.add_apply, GridMartBA_Q1, GridMartBA_Q2, GridMartBA_chain, GridMartBA_chain]
  set G0 := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) with hG0
  set G1 := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) with hG1
  have s1 : ∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, G0 y z * G1 z w * G0 (twShift (sz := sz) n c w) x =
      ∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, G0 y z * G1 z w * G0 w x :=
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w hw => by rw [hsh w hw]
  have s2 : ∑ w ∈ twBlk n c, ∑ z ∈ twBlk n b, G1 y w * G0 (twShift (sz := sz) n c w) z * G1 z x =
      ∑ w ∈ twBlk n c, ∑ z ∈ twBlk n b, G1 y w * G0 w z * G1 z x :=
    Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun z _ => by rw [hsh w hw]
  rw [s1, s2]
  ring

/-- The squared Hilbert-Schmidt weight of a fine matrix `Q`: `Φ(Q) = W^{-d} Σ_{[i]=[j]} |Q_{ij}|²` (real, `≥ 0`). -/
private def GridMartBA_Phi (Q : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ i, ∑ j, if (split d (sz.L n) (sz.W n) i).1 = (split d (sz.L n) (sz.W n) j).1 then ‖Q i j‖ ^ 2 else 0

private theorem GridMartBA_Phi_nonneg (Q : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    0 ≤ GridMartBA_Phi sz n Q := by
  unfold GridMartBA_Phi
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity)

private theorem GridMartBA_Phi_add_le (Q Q' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    GridMartBA_Phi sz n (Q + Q') ≤ 2 * (GridMartBA_Phi sz n Q + GridMartBA_Phi sz n Q') := by
  unfold GridMartBA_Phi
  rw [← mul_add, ← Finset.sum_add_distrib]
  have hw : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  rw [← mul_assoc, mul_comm (2 : ℝ), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hw
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · have h1 := norm_add_le (Q i j) (Q' i j)
    have h2 : ‖(Q + Q') i j‖ ≤ ‖Q i j‖ + ‖Q' i j‖ := by simpa using h1
    have h3 : 0 ≤ ‖(Q + Q') i j‖ := norm_nonneg _
    nlinarith [norm_nonneg (Q i j), norm_nonneg (Q' i j), sq_nonneg (‖Q i j‖ - ‖Q' i j‖)]
  · simp

/-- **The quadratic variation at `c₁ = c₂ = c`**: `(Ẽ⊗Ẽ)(b,b; c,c) = Φ(Q₁ + Q₂)` (`S = 1`, Hermitian `H`). -/
private theorem GridMartBA_twEEM_eq (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (b c : Zd d (sz.L n)) :
    twEEM sz lam0 E n u H σ b b c c =
      ((GridMartBA_Phi sz n (GridMartBA_Q1 sz lam0 E n u H σ b c + GridMartBA_Q2 sz lam0 E n u H σ b c) : ℝ) : ℂ) := by
  unfold twEEM GridMartBA_Phi
  rw [Finset.sum_comm]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hS : (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) j).1 (split d (sz.L n) (sz.W n) i).1 =
      if (split d (sz.L n) (sz.W n) i).1 = (split d (sz.L n) (sz.W n) j).1 then 1 else 0 := by
    change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) _ _ = _
    rw [Matrix.one_apply]
    simp only [eq_comm]
  rw [hS, GridMartBA_twDerM_eq sz lam0 E n u hH, map_neg]
  by_cases hij : (split d (sz.L n) (sz.W n) i).1 = (split d (sz.L n) (sz.W n) j).1
  · simp only [hij, ite_true]
    rw [neg_mul_neg, Complex.mul_conj']
    push_cast
    ring
  · simp [hij]

/-- `W^d Σ_c Tr(R E_c R^* E_c) = Φ(R)`. -/
private theorem GridMartBA_sum_trace (R : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    (((sz.W n : ℕ) : ℂ) ^ d) * ∑ c, Matrix.trace (R * TwistKer_fE n c * Rᴴ * TwistKer_fE n c) =
      ((GridMartBA_Phi sz n R : ℝ) : ℂ) := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  simp only [TwistKer_trace_sandwich]
  have h1 : ∀ i j : Idx d (sz.L n) (sz.W n), R i j * Rᴴ j i = ((‖R i j‖ ^ 2 : ℝ) : ℂ) := fun i j => by
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']
    push_cast; ring
  have h2 : ∑ c : Zd d (sz.L n), ∑ i ∈ twBlk n c, ∑ j ∈ twBlk n c, R i j * Rᴴ j i =
      ∑ i, ∑ j, if (split d (sz.L n) (sz.W n) i).1 = (split d (sz.L n) (sz.W n) j).1 then ((‖R i j‖ ^ 2 : ℝ) : ℂ) else 0 := by
    simp only [twBlk, Finset.sum_filter, h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : (split d (sz.L n) (sz.W n) i).1 = (split d (sz.L n) (sz.W n) j).1
    · simp [hij]
    · have : ¬ (split d (sz.L n) (sz.W n) j).1 = (split d (sz.L n) (sz.W n) i).1 := fun h => hij h.symm
      simp [hij, this]
  rw [← Finset.mul_sum, h2]
  unfold GridMartBA_Phi
  push_cast
  simp only [apply_ite Complex.ofReal, Complex.ofReal_pow, Complex.ofReal_zero]
  generalize (∑ x : Idx d (sz.L n) (sz.W n), ∑ x_1 : Idx d (sz.L n) (sz.W n),
    if (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) x_1).1 then (↑‖R x x_1‖ : ℂ) ^ 2 else 0) = S
  field_simp

/-- `Q₁^* = G(-σ₀) E_c G(-σ₁) E_b G(-σ₀)`. -/
private theorem GridMartBA_Q1_conjTranspose (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (b c : Zd d (sz.L n)) :
    (GridMartBA_Q1 sz lam0 E n u H σ b c)ᴴ =
      Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (!σ 0) * TwistKer_fE n c * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (!σ 1) *
        TwistKer_fE n b * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (!σ 0) := by
  unfold GridMartBA_Q1
  simp only [Matrix.conjTranspose_mul, GridMartBA_fE_herm, TwistKer_Gres_conjTranspose hH, Matrix.mul_assoc]

/-- `Q₂^* = G(-σ₁) E_b G(-σ₀) E_c G(-σ₁)`. -/
private theorem GridMartBA_Q2_conjTranspose (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (b c : Zd d (sz.L n)) :
    (GridMartBA_Q2 sz lam0 E n u H σ b c)ᴴ =
      Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (!σ 1) * TwistKer_fE n b * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (!σ 0) *
        TwistKer_fE n c * Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (!σ 1) := by
  unfold GridMartBA_Q2
  simp only [Matrix.conjTranspose_mul, GridMartBA_fE_herm, TwistKer_Gres_conjTranspose hH, Matrix.mul_assoc]

/-- **The 6-loop of `STEEkMg`, `k = 0`**: `𝓛_{(σ₀σ₁σ₀σ̄₀σ̄₁σ̄₀),(a₀,a₁,c,a₁,a₀,c)} = Tr(Q₁ E_c Q₁^* E_c)`. -/
private theorem GridMartBA_loop6_zero (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c, a 1, a 0, c] =
      Matrix.trace (GridMartBA_Q1 sz lam0 E n u H σ (a 0) (a 1) * TwistKer_fE n c *
        (GridMartBA_Q1 sz lam0 E n u H σ (a 0) (a 1))ᴴ * TwistKer_fE n c) := by
  rw [GridMartBA_Q1_conjTranspose sz lam0 E n u hH]
  change loopFine d (sz.L n) (sz.W n) H (ztOf (BAmF sz lam0 E n) (E n) u) _ _ = _
  rw [TwistKer_loopFine_eq]
  simp only [GridMartBA_Q1, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_assoc]

/-- **The 6-loop of `STEEkMg`, `k = 1`**: `𝓛_{(σ₁σ₀σ₁σ̄₁σ̄₀σ̄₁),(a₁,a₀,c,a₀,a₁,c)} = Tr(Q₂ E_c Q₂^* E_c)`. -/
private theorem GridMartBA_loop6_one (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c, a 0, a 1, c] =
      Matrix.trace (GridMartBA_Q2 sz lam0 E n u H σ (a 0) (a 1) * TwistKer_fE n c *
        (GridMartBA_Q2 sz lam0 E n u H σ (a 0) (a 1))ᴴ * TwistKer_fE n c) := by
  rw [GridMartBA_Q2_conjTranspose sz lam0 E n u hH]
  change loopFine d (sz.L n) (sz.W n) H (ztOf (BAmF sz lam0 E n) (E n) u) _ _ = _
  rw [TwistKer_loopFine_eq]
  simp only [GridMartBA_Q2, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_assoc]

/-- `STEEkMg` at `k = 0, 1` is `Φ(Q_{k+1})` (`S = 1`, Hermitian `H`). -/
private theorem GridMartBA_STEEk (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEkMg (baStep2Mat sz lam0 E) n u H 0 σ a = ((GridMartBA_Phi sz n (GridMartBA_Q1 sz lam0 E n u H σ (a 0) (a 1)) : ℝ) : ℂ) ∧
      STEEkMg (baStep2Mat sz lam0 E) n u H 1 σ a = ((GridMartBA_Phi sz n (GridMartBA_Q2 sz lam0 E n u H σ (a 0) (a 1)) : ℝ) : ℂ) := by
  have hS : ∀ x y : Zd d (sz.L n), (baStep2Mat sz lam0 E).S n x y = if x = y then 1 else 0 := fun x y => by
    change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y = _
    rw [Matrix.one_apply]
  constructor
  · rw [← GridMartBA_sum_trace]
    unfold STEEkMg
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hS, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold STLMg
    exact GridMartBA_loop6_zero sz lam0 E n u hH σ a c
  · rw [← GridMartBA_sum_trace]
    unfold STEEkMg
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hS, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold STLMg
    exact GridMartBA_loop6_one sz lam0 E n u hH σ a c

/-- **H3′** (pointwise, at a Hermitian `H`): `‖Ẽ⊗Ẽ(a,a;a₁,a₁)‖ ≤ 2 ‖STEEMg‖`.  (`|Q₁+Q₂|² ≤ 2|Q₁|² + 2|Q₂|²`; the sum of the two
diagonal 6-loops `STEEkMg` is `Φ(Q₁) + Φ(Q₂)`, the twisted `Ẽ⊗Ẽ` is `Φ(Q₁ + Q₂)`.) -/
private theorem GridMartBA_H3 (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖twEEM sz lam0 E n u H σ (a 0) (a 0) (a 1) (a 1)‖ ≤ 2 * ‖STEEMg (baStep2Mat sz lam0 E) n u H σ a‖ := by
  obtain ⟨h0, h1⟩ := GridMartBA_STEEk sz lam0 E n u hH σ a
  rw [GridMartBA_twEEM_eq sz lam0 E n u hH σ (a 0) (a 1)]
  unfold STEEMg
  rw [h0, h1, ← Complex.ofReal_add, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (GridMartBA_Phi_nonneg sz n _),
    Real.norm_of_nonneg (add_nonneg (GridMartBA_Phi_nonneg sz n _) (GridMartBA_Phi_nonneg sz n _))]
  exact GridMartBA_Phi_add_le sz n _ _

end QV

/-! ## 5. `baGridBridge_holds` -/

/-- **The three identities**: at `c₁ = c₂ = a 1` along the grid, eventually along a BA flow, for
every `d`.  The finitely many `n` with `BAflowLam0 sz z n ≤ 0` are absorbed by "eventually" (`BAflow_lam0_window`); `BAReal` holds for
every `n` (`BAflow_real`); the grid walk `H_{u_k}` is Hermitian at every `k`, `ω`. -/
theorem baGridBridge_holds (d : ℕ) : BAGridBridge d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htT K hK0
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro σ a k hk ω
  have hg : 0 < BAflowLam0 sz z n := hn.1
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hT1 : BAflowT0 sz z n < 1 := (baStep2Data sz z).flowOK_T hκ hflow n
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 (hst n)) (Nat.cast_nonneg _)
  have hu : gridTime s t K n k ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨add_nonneg (hs n) (mul_nonneg (Nat.cast_nonneg _) hΔ), ?_⟩
    have hle : gridTime s t K n k ≤ gridTime s t K n (K n) := by
      unfold gridTime
      have : (k : ℝ) ≤ (K n : ℝ) := Nat.cast_le.2 hk
      nlinarith
    rw [gridTime_last s t K n (hK0 n)] at hle
    linarith [htT n]
  have hH := GridMartBA_Hpath_herm sz (BAflowLam0 sz z) (BAflowEs sz z) n s t K k ω
  refine ⟨?_, ?_, ?_⟩
  · exact GridMartBA_H1 sz (BAflowLam0 sz z) (BAflowEs sz z) n hκ hg hr hu hH σ a
  · exact GridMartBA_H2 sz (BAflowLam0 sz z) (BAflowEs sz z) n hκ hg hr hu hH σ a
  · exact GridMartBA_H3 sz (BAflowLam0 sz z) (BAflowEs sz z) n _ hH σ a

/-! ## 6. The untwisted BA grid statement -/

/-- The tail comparison of clause (iii): if `St ≤ 2 Sp` and `2 ≤ N^{ε'/2}` then the event of the untwisted statement at `ε'` (the sum `Sp` of the
untwisted QV) lies inside the event of the twisted one at `ε'/2` (the sum `St` of the twisted QV):
`N^{ε'/2} (St + B)^{1/2} ≤ N^{ε'/2} √2 (Sp + B)^{1/2} ≤ N^{ε'} (Sp + B)^{1/2}`. -/
private theorem GridMartBA_tail_mono {N Sp St B M ε' : ℝ} (hN0 : 0 < N) (hN : 2 ≤ N ^ (ε' / 2)) (hSp : 0 ≤ Sp) (hSt : 0 ≤ St)
    (hSS : St ≤ 2 * Sp) (hB : 0 ≤ B) (h : N ^ ε' * (Sp + B) ^ (1 / 2 : ℝ) < M) :
    N ^ (ε' / 2) * (St + B) ^ (1 / 2 : ℝ) < M := by
  have h1 : (St + B) ^ (1 / 2 : ℝ) ≤ (2 * (Sp + B)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h2 : (2 * (Sp + B)) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * (Sp + B) ^ (1 / 2 : ℝ) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ N ^ (ε' / 2) := by
    refine le_trans ?_ hN
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hP : 0 ≤ (Sp + B) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hNe : 0 ≤ N ^ (ε' / 2) := Real.rpow_nonneg hN0.le _
  calc N ^ (ε' / 2) * (St + B) ^ (1 / 2 : ℝ) ≤ N ^ (ε' / 2) * (N ^ (ε' / 2) * (Sp + B) ^ (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hNe
        exact h1.trans (by rw [h2]; exact mul_le_mul_of_nonneg_right h3 hP)
    _ = N ^ ε' * (Sp + B) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, ← Real.rpow_add hN0]
        congr 2
        ring
    _ < M := h

/-- **The glue** (private: it takes the statement `BATwistGridMartAt` as a hypothesis): the three identities and the twisted grid statement at
`C₀` give the untwisted one at `C₀`.  `Mart`, `Rem` are those of the twisted statement where the identities hold (`Pn n`, eventually) and the canonical untwisted ones
elsewhere (the decomposition holds for every `n`: the conditional expectation cancels).  Clause (iii): the event of the untwisted statement at `ε'` lies in
the twisted event at `ε'/2` (`GridMartBA_tail_mono`, H3′, `N^{ε'/2} ≥ 2` eventually). -/
private theorem GridMartBA_bridge {d : ℕ} (C₀ : ℝ) (hB : BAGridBridge d) (hT : BATwistGridMartAt d C₀) :
    STGridMartAtgL d C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htT D hD
  obtain ⟨CK, hCK, hK⟩ := hT κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htT D hD
  refine ⟨CK, hCK, fun K hK0 hKN => ?_⟩
  obtain ⟨Mart, Rem, hid, hrem, htail, -⟩ := hK K hK0 hKN
  have hP := hB κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htT K hK0
  have hΔ : ∀ n, 0 ≤ gridStep s t K n := fun n => div_nonneg (sub_nonneg.2 (hst n)) (Nat.cast_nonneg _)
  classical
  set Cm : Step2Mat sz := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z) with hCm
  -- the canonical untwisted `Mart`, `Rem` (every `n`): the conditional expectation cancels
  let Ac : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ :=
    fun n i k ω => STgAg Cm s t K n i.1 i.2 k ω
  let Mc : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ := fun n i k ω =>
    ∑ j ∈ Finset.range k, (Ac n i (j + 1) ω - Cm.Pp[fun ω' => Ac n i (j + 1) ω' | filt (sz.withLam 0) j] ω)
  let Rc : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ := fun n i k ω =>
    ∑ j ∈ Finset.range k, (Cm.Pp[fun ω' => Ac n i (j + 1) ω' | filt (sz.withLam 0) j] ω - Ac n i j ω -
      ((gridStep s t K n : ℝ) : ℂ) * STgDriftg Cm s t K n i.1 i.2 j ω)
  have hcanon : ∀ n i k ω, Ac n i k ω = Ac n i 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
      ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω + Rc n i k ω + Mc n i k ω := by
    intro n i k ω
    induction k with
    | zero => simp [Rc, Mc]
    | succ k ih =>
        simp only [Rc, Mc, Finset.sum_range_succ, mul_add] at ih ⊢
        linear_combination ih
  let tw : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) →
      (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) := fun n i => (i.1, i.2 0, i.2 1, i.2 1)
  let Pn : ℕ → Prop := fun n => ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ∀ k ≤ K n, ∀ ω : PathΩ sz,
      twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 1) (a 1) k ω (a 0) = STgAg Cm s t K n σ a k ω ∧
        twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω = STgDriftg Cm s t K n σ a k ω ∧
        ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω‖ ≤
          2 * ‖STEEMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ a‖
  refine ⟨fun n i k ω => if Pn n then Mart n (tw n i) k ω else Mc n i k ω,
    fun n i k ω => if Pn n then Rem n (tw n i) k ω else Rc n i k ω, ?_, ?_, ?_⟩
  · intro n i
    by_cases hn : Pn n
    · filter_upwards [hid n (tw n i)] with ω hω k hk
      have h := hω k hk
      dsimp only [tw] at h
      have e2 : ∀ j ∈ Finset.range k, twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 (i.2 0) (i.2 1) (i.2 1) j ω =
          STgDriftg Cm s t K n i.1 i.2 j ω := fun j hj =>
        (hn i.1 i.2 j (by have := Finset.mem_range.1 hj; omega) ω).2.1
      rw [Finset.sum_congr rfl e2, (hn i.1 i.2 k hk ω).1, (hn i.1 i.2 0 (Nat.zero_le _) ω).1] at h
      simp only [hn, ↓reduceIte]
      exact h
    · exact Filter.Eventually.of_forall fun ω k hk => by
        simp only [hn, ↓reduceIte]; exact hcanon n i k ω
  · filter_upwards [hrem, hP] with n hn hPn0 i
    have hPn : Pn n := hPn0
    filter_upwards [hn (tw n i)] with ω hω k hk
    simp only [hPn, ↓reduceIte]
    exact hω k hk
  · intro ε' hε'
    have hN : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (ε' / 2) :=
      ((tendsto_rpow_atTop (half_pos hε')).comp hflow.1.2.2.1).eventually_ge_atTop 2
    filter_upwards [htail (ε' / 2) (half_pos hε'), hP, hN] with n hn hPn0 hNn i
    have hPn : Pn n := hPn0
    have h := hn (tw n i)
    dsimp only [tw] at h
    simp only [hPn, ↓reduceIte]
    refine le_trans (measure_mono ?_) h
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    refine ⟨k, hk, ?_⟩
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    refine GridMartBA_tail_mono hN0 hNn (Finset.sum_nonneg fun j _ => mul_nonneg (hΔ n) (norm_nonneg _))
      (Finset.sum_nonneg fun j _ => mul_nonneg (hΔ n) (norm_nonneg _)) ?_ (Real.rpow_nonneg hN0.le _) hlt
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : j ≤ K n := by have := Finset.mem_range.1 hj; omega
    have h3 := (hPn i.1 i.2 j hj' ω).2.2
    calc gridStep s t K n * ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 (i.2 0) (i.2 1) (i.2 1) j ω‖
        ≤ gridStep s t K n * (2 * ‖STEEMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖) :=
          mul_le_mul_of_nonneg_left h3 (hΔ n)
      _ = 2 * (gridStep s t K n * ‖STEEMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖) := by ring

/-! ## 7. `baGridMart_holds` -/

/-- **The untwisted BA grid statement** `STGridMartgL` at `baStep2Mat` along `BAFlow`, for every `d`: from `baTwistGridMart_holds` and the three
identities `baGridBridge_holds`.  The statement is the case `m = 2` of the carrier-generic statements of
`Chain/Step2Gen`; the reading of `STGridMartAtgL` (`∃ C₀`) is `GridMartBA_bridge`. -/
theorem baGridMart_holds (d : ℕ) :
    STGridMartgL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
  obtain ⟨C₀, hC₀, hAt⟩ := baTwistGridMart_holds d
  exact ⟨C₀, hC₀, GridMartBA_bridge C₀ (baGridBridge_holds d) hAt⟩


end RBM.BA

end
