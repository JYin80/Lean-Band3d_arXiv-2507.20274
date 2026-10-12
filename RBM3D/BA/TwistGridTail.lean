/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGrid2
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenSchur
import RBM3D.Path.DifREP2
import RBM3D.Path.StepDecompLoop
import RBM3D.Path.QVIdentity
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.AzumaProxyN2

/-!
# BA stage TL, row TL2a3 (T2438): the martingale tail of `twMart` with the quadratic variation `twEEk`

Ticket `docs/tickets/T2438.md`; clause (iii) of 4 (b) of `docs/tickets/T2428-amend-1.md`; pin `BATwistGridTail`
(`RBM3D/BA/TwistGrid2.lean:239`); route of `RBM3D/Path/DifREP2.lean` §7-§12 (`gridRepTailN_holds`, Azuma with a random
predictable proxy, DECISIONS §7, paper-delta D90), re-proved for the twisted family `L̃_{σ,(b;c₁,c₂)}` of
`RBM3D/BA/TwistGrid.lean` with its gradient (D.2) `twDerM`.

* `baTwistGridTail_holds d : BATwistGridTail d` for every `d` (no `3 ≤ d`).
* `TwistGridTail_condMGF_Z`: the conditional mgf of `Re`, `Im` of `Σ_b κ_b Z_b` (general weights `κ`) with the
  random proxy `Δ · Re Σ_{b,b'} κ_b conj κ_{b'} twEEM(b,b')` (twin of `difRepTail_condMGF_Z`).
* the variance identity `Σ_c gvar_c |Σ_b κ_b ∂_c L̃_b|² = Re Σ_{b,b'} κ_b conj κ_{b'} twEEM(b,b')` (constant `1`).

Every helper is `private` or prefixed `TwistGridTail_`; private helpers of the merged band files (`Path/DifREP2`,
`Path/StepDecompLoop`, `Path/QVIdentity`, `Induction/StepDecompN`, `Induction/GridAssemblyN`) are reached through
`open private` (the pattern of `BA/Step2BA.lean:35`), not copied.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private difRepTail_doob_tail difRepTail_condExp_exp difRepTail_memLp_two_of_pow4 difRepTail_trace_eq
  difRepTail_linTrVar_le difRepTail_gridTime_nonneg difRepTail_gridTime_le difRepTail_gridTime_succ
  difRepTail_K_mul_step difRepTail_measurable_linTr_uncurry difRepTail_standardBorelMatrix difRepTail_eventually_Z
  from RBM3D.Path.DifREP2
open private StepDecompLoop_word_jets StepDecompLoop_word_jet1 StepDecompLoop_hasDerivAt_Gres
  StepDecompLoop_fderiv_of_line StepDecompLoop_fderiv2_of_line StepDecompLoop_isHermitian_add_realSmul
  StepDecompLoop_trace_hasDerivAt StepDecompLoop_trCLM StepDecompLoop_hasDerivAt_line StepDecompLoop_nmul
  StepDecompLoop_gres_false StepDecompLoop_nadd from RBM3D.Path.StepDecompLoop
open private QVIdentity_coord_sum QVIdentity_pair QVIdentity_svarF_cast QVIdentity_sum_swap4 from RBM3D.Path.QVIdentity
open private StepDecompN_integrable_phi StepDecompN_measurable_AbCN from RBM3D.Induction.StepDecompN
open private gridAsm_measurable_coord from RBM3D.Induction.GridAssemblyN
open private StepDecompN_integrable_phi StepDecompN_measurable_AbCN from RBM3D.Induction.StepDecompN

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Ind RBM.Loop

/-! ## 1. The twisted word `L̃ = tr (G₁ E_b G₂ Q)` on the fine lattice

`E_b = W^{-d} 1_{[b]}` (diagonal) and `Q = Q_{c₁c₂}`, `Q_{w p} = W^{-d} 1[w ∈ [c₁], p = Π_{c₂} w]`, so that
`tr (X₁ E_b X₂ Q) = W^{-2d} Σ_{x ∈ [b]} Σ_{w ∈ [c₁]} (X₂)_{xw} (X₁)_{Π_{c₂}w, x} = twLoopX n X₁ X₂ b c₁ c₂`. -/

section Words

variable {d : ℕ} {sz : Sizes d} (n : ℕ)

/-- `E_b` on the fine lattice: `W^{-d}` on the block `[b]`. -/
private def TwistGridTail_Ea (b : Zd d (sz.L n)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Matrix.diagonal fun x => if x ∈ twBlk n b then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0

/-- `Q_{c₁c₂}`: `Q_{w p} = W^{-d} 1[w ∈ [c₁], p = Π_{c₂} w]`. -/
private def TwistGridTail_Q (c₁ c₂ : Zd d (sz.L n)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Matrix.of fun w p => if w ∈ twBlk n c₁ ∧ p = twShift n c₂ w then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0

private theorem TwistGridTail_Q_mul (c₁ c₂ : Zd d (sz.L n)) (Y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (w r : Idx d (sz.L n) (sz.W n)) :
    (TwistGridTail_Q n c₁ c₂ * Y) w r = if w ∈ twBlk n c₁ then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Y (twShift n c₂ w) r else 0 := by
  simp only [Matrix.mul_apply, TwistGridTail_Q, Matrix.of_apply]
  by_cases hw : w ∈ twBlk n c₁
  · simp [hw]
  · simp [hw]

private theorem TwistGridTail_Ea_mul (b : Zd d (sz.L n)) (Y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (x r : Idx d (sz.L n) (sz.W n)) :
    (TwistGridTail_Ea n b * Y) x r = if x ∈ twBlk n b then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Y x r else 0 := by
  simp only [TwistGridTail_Ea, Matrix.diagonal_mul]
  by_cases hx : x ∈ twBlk n b
  · simp [hx]
  · simp [hx]

/-- `tr (X₁ E_b X₂ Q) = twLoopX X₁ X₂ b c₁ c₂`. -/
private theorem TwistGridTail_twLoopX_eq (X₁ X₂ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (b c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n (fun x y => X₁ x y) (fun x y => X₂ x y) b c₁ c₂ =
      Matrix.trace (X₁ * TwistGridTail_Ea n b * X₂ * TwistGridTail_Q n c₁ c₂) := by
  rw [Matrix.trace_mul_comm]
  set e : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with he
  have hY : ∀ p w, (X₁ * TwistGridTail_Ea n b * X₂) p w =
      ∑ x, X₁ p x * (if x ∈ twBlk n b then e else 0) * X₂ x w := by
    intro p w
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [TwistGridTail_Ea, Matrix.mul_diagonal]
  have h1 : ∀ (f : Idx d (sz.L n) (sz.W n) → ℂ) (c : Zd d (sz.L n)),
      ∑ x ∈ twBlk n c, f x = ∑ x, if x ∈ twBlk n c then f x else 0 := fun f c => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  unfold twLoopX
  simp only [Matrix.trace, Matrix.diag_apply, TwistGridTail_Q_mul, hY]
  rw [← he]
  simp only [h1, Finset.mul_sum]
  have h2 : ∀ (x : Idx d (sz.L n) (sz.W n)) (F : Idx d (sz.L n) (sz.W n) → ℂ),
      (if x ∈ twBlk n c₁ then ∑ i, F i else 0) = ∑ i, if x ∈ twBlk n c₁ then F i else 0 := fun x F => by
    split_ifs <;> simp
  have h3 : ∀ (i : Idx d (sz.L n) (sz.W n)) (F : Idx d (sz.L n) (sz.W n) → ℂ),
      (if i ∈ twBlk n b then ∑ x, F x else 0) = ∑ x, if i ∈ twBlk n b then F x else 0 := fun i F => by
    split_ifs <;> simp
  simp only [h2, h3, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> first | rfl | ring

private theorem TwistGridTail_e_nonneg : (0 : ℝ) ≤ ((sz.W n : ℝ) ^ d)⁻¹ := by positivity

private theorem TwistGridTail_e_le_one : ((sz.W n : ℝ) ^ d)⁻¹ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (sz.W n : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)

private theorem TwistGridTail_norm_Ea (b : Zd d (sz.L n)) : ‖TwistGridTail_Ea n b‖ ≤ ((sz.W n : ℝ) ^ d)⁻¹ := by
  rw [TwistGridTail_Ea, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (TwistGridTail_e_nonneg n)).mpr fun p => ?_
  split_ifs with h
  · simp
  · simp [TwistGridTail_e_nonneg]

private theorem TwistGridTail_shift_inj {c : Zd d (sz.L n)} {c₁ : Zd d (sz.L n)} {w r : Idx d (sz.L n) (sz.W n)}
    (hw : w ∈ twBlk n c₁) (hr : r ∈ twBlk n c₁) (h : twShift n c w = twShift n c r) : w = r := by
  have hs : ∀ x : Idx d (sz.L n) (sz.W n), split d (sz.L n) (sz.W n) (twShift n c x) = (c, (split d (sz.L n) (sz.W n) x).2) :=
    fun x => (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
  have h2 : (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) r).2 := by
    have := congrArg (fun y => (split d (sz.L n) (sz.W n) y).2) h
    simpa only [hs] using this
  have h1 : (split d (sz.L n) (sz.W n) w).1 = (split d (sz.L n) (sz.W n) r).1 := by
    have e1 : (split d (sz.L n) (sz.W n) w).1 = c₁ := by simpa [twBlk] using hw
    have e2 : (split d (sz.L n) (sz.W n) r).1 = c₁ := by simpa [twBlk] using hr
    rw [e1, e2]
  exact split_injective d (sz.L n) (sz.W n) (Prod.ext h1 h2)

private theorem TwistGridTail_norm_Q (c₁ c₂ : Zd d (sz.L n)) : ‖TwistGridTail_Q n c₁ c₂‖ ≤ ((sz.W n : ℝ) ^ d)⁻¹ := by
  set e : ℝ := ((sz.W n : ℝ) ^ d)⁻¹ with he
  have hce : (starRingEnd ℂ) (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ := by
    simp
  have hQQ : TwistGridTail_Q n c₁ c₂ * (TwistGridTail_Q n c₁ c₂)ᴴ =
      Matrix.diagonal fun w => if w ∈ twBlk n c₁ then (e : ℂ) * e else 0 := by
    ext w r
    rw [TwistGridTail_Q_mul, Matrix.diagonal_apply]
    simp only [Matrix.conjTranspose_apply, TwistGridTail_Q, Matrix.of_apply, he]
    by_cases hw : w ∈ twBlk n c₁
    · by_cases hwr : w = r
      · subst hwr
        simp [hw, hce]
      · have : ¬ (r ∈ twBlk n c₁ ∧ twShift n c₂ w = twShift n c₂ r) :=
          fun h => hwr (TwistGridTail_shift_inj n hw h.1 h.2)
        simp [hw, this, hwr]
    · simp [hw]
  have h1 : ‖TwistGridTail_Q n c₁ c₂ * (TwistGridTail_Q n c₁ c₂)ᴴ‖ ≤ e * e := by
    rw [hQQ, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
    split_ifs with h
    · simp
    · simpa using mul_nonneg (TwistGridTail_e_nonneg (sz := sz) (d := d) n) (TwistGridTail_e_nonneg (sz := sz) (d := d) n)
  have h2 : ‖TwistGridTail_Q n c₁ c₂ * (TwistGridTail_Q n c₁ c₂)ᴴ‖ = ‖TwistGridTail_Q n c₁ c₂‖ * ‖TwistGridTail_Q n c₁ c₂‖ := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self (TwistGridTail_Q n c₁ c₂)ᴴ
    rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
  rw [h2] at h1
  by_contra hlt
  push_neg at hlt
  nlinarith [norm_nonneg (TwistGridTail_Q n c₁ c₂), TwistGridTail_e_nonneg (sz := sz) (d := d) n]

end Words

/-! ## 2. The twisted family as an observable of the walk matrix: smoothness, bound and second derivative -/

section Obs

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- **The twisted observable at the spectral time `u`**, as a function of the walk matrix `M`
(`H = g₀ Ψ + M`; `Hpath = g₀ Ψ + pathH`): `M ↦ L̃_{σ,(b;c₁,c₂)}(g₀ Ψ + M)`. -/
def TwistGridTail_phi (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℂ :=
  twL2M sz lam0 E n u (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) σ b c₁ c₂

/-- The signed resolvent as a matrix, valid for every `H`: `G(+) = (H - z)⁻¹`, `G(-) = G(+)^*`
(which is `(H - z̄)⁻¹` for Hermitian `H`). -/
private def TwistGridTail_Gc {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ℂ) (H : Matrix ι ι ℂ) (σ : Bool) :
    Matrix ι ι ℂ :=
  if σ then Gres H z true else (Gres H z true)ᴴ

private theorem TwistGridTail_Gc_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) : TwistGridTail_Gc z H σ = Gres H z σ := by
  cases σ
  · simp only [TwistGridTail_Gc, Bool.false_eq_true, ite_false]
    exact (StepDecompLoop_gres_false H hH z).symm
  · simp [TwistGridTail_Gc]

private theorem TwistGridTail_twL2M_eq (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) :
    twL2M sz lam0 E n u H σ b c₁ c₂ =
      Matrix.trace (TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) H (σ 0) * TwistGridTail_Ea n b *
        TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) H (σ 1) * TwistGridTail_Q n c₁ c₂) := by
  have h : ∀ τ : Bool, twChg (twGM sz lam0 E n u H) τ =
      fun x y => TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) H τ x y := by
    intro τ
    funext x y
    cases τ
    · simp [twChg, twGM, TwistGridTail_Gc, Matrix.conjTranspose_apply]
    · simp [twChg, twGM, TwistGridTail_Gc]
  unfold twL2M
  rw [h, h]
  exact TwistGridTail_twLoopX_eq n _ _ b c₁ c₂

private theorem TwistGridTail_phi_eq (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b M =
      Matrix.trace (TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) (σ 0) *
        TwistGridTail_Ea n b *
        TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) (σ 1) *
        TwistGridTail_Q n c₁ c₂) :=
  TwistGridTail_twL2M_eq sz lam0 E n u _ σ b c₁ c₂

private theorem TwistGridTail_Hh_herm {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) : (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M).IsHermitian := by
  refine Matrix.IsHermitian.add ?_ hM
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star ((lam0 n : ℝ) : ℂ) = ((lam0 n : ℝ) : ℂ) from Complex.conj_ofReal _]

/-- Conjugate transpose as a continuous real-linear map. -/
private def TwistGridTail_ctCLM (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun r A => by
        simp [Matrix.conjTranspose_smul] }

private theorem TwistGridTail_contDiffAt_Gc {z : ℂ} (hz : z.im ≠ 0)
    (σ : Bool) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    ContDiffAt ℝ 2 (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      TwistGridTail_Gc z (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M') σ) M := by
  set Hh : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    fun M' => ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M' with hHh
  have hu : IsUnit (Hh M - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    isUnit_sub_smul_of_isHermitian (TwistGridTail_Hh_herm sz lam0 n hM) hz
  have hA : ContDiff ℝ 2 (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Hh M' - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :=
    (contDiff_const.add contDiff_id).sub contDiff_const
  have hinv : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
      (Hh M - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h := hinv.comp M hA.contDiffAt
  have hfun : (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Gres (Hh M') z true) =
      Ring.inverse ∘ (fun M' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        Hh M' - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) := by
    funext M'
    simp [Gres]
  cases σ
  · have h2 := (TwistGridTail_ctCLM (Idx d (sz.L n) (sz.W n))).contDiff.contDiffAt.comp M (hfun ▸ h)
    exact h2
  · simpa [TwistGridTail_Gc, hHh] using (hfun ▸ h)

private theorem TwistGridTail_phi_trace_herm (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) :
    TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b M =
      Matrix.trace (Gres (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) *
        TwistGridTail_Ea n b *
        Gres (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) *
        TwistGridTail_Q n c₁ c₂) := by
  rw [TwistGridTail_phi_eq, TwistGridTail_Gc_herm (TwistGridTail_Hh_herm sz lam0 n hM),
    TwistGridTail_Gc_herm (TwistGridTail_Hh_herm sz lam0 n hM)]

/-- `(H) ` the twisted observable is in the Hermitian test class (`C²` at every Hermitian point, bounded on the
Hermitian matrices), for `η_u = (1 - u) Im m_F > 0`. -/
private theorem TwistGridTail_hermTestFun {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool)
    (c₁ c₂ b : Zd d (sz.L n)) : HermTestFun sz n (TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b) := by
  have hz0 : (ztOf (BAmF sz lam0 E n) (E n) u).im ≠ 0 := by rw [ztOf_im]; exact hη.ne'
  have hzη : etaOf (BAmF sz lam0 E n) u ≤ |(ztOf (BAmF sz lam0 E n) (E n) u).im| := by
    rw [ztOf_im, abs_of_pos hη]
  refine ⟨fun M hM => ?_, ?_⟩
  · have hfun : TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b = fun M' =>
        Matrix.trace (TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M') (σ 0) *
          TwistGridTail_Ea n b *
          TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M') (σ 1) *
          TwistGridTail_Q n c₁ c₂) :=
      funext fun M' => TwistGridTail_phi_eq sz lam0 E n u σ c₁ c₂ b M'
    rw [hfun]
    have h0 := TwistGridTail_contDiffAt_Gc sz lam0 n hz0 (σ 0) hM
    have h1 := TwistGridTail_contDiffAt_Gc sz lam0 n hz0 (σ 1) hM
    have hprod := ((h0.mul (contDiffAt_const (c := TwistGridTail_Ea n b))).mul h1).mul
      (contDiffAt_const (c := TwistGridTail_Q n c₁ c₂))
    exact (StepDecompLoop_trCLM (Idx d (sz.L n) (sz.W n))).contDiff.contDiffAt.comp M hprod
  · refine ⟨(Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) *
      ((etaOf (BAmF sz lam0 E n) u)⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹ * (etaOf (BAmF sz lam0 E n) u)⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹),
      fun M hM => ?_⟩
    rw [TwistGridTail_phi_trace_herm sz lam0 E n u σ c₁ c₂ b hM]
    have hH := TwistGridTail_Hh_herm sz lam0 n hM
    refine (norm_matrix_trace_le_card_mul _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul (norm_Gsig_le_inv_eta hH hη hzη (σ 0))
      (TwistGridTail_norm_Ea n b)) (norm_Gsig_le_inv_eta hH hη hzη (σ 1))) (TwistGridTail_norm_Q n c₁ c₂)

/-- **The second derivative of the twisted observable along a Hermitian line**: `‖∂²L̃[y,y]‖ ≤ 6 N η_u⁻⁴ ‖y‖²`
(the loop bound of `hermTestFunLoopN` at `k = 2`: six Leibniz words, trace `≤ N ‖·‖`, `‖E_b‖, ‖Q‖ ≤ W^{-d} ≤ 1`). -/
private theorem TwistGridTail_second_deriv_bound {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool)
    (c₁ c₂ b : Zd d (sz.L n)) {M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ (TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b)) M y y‖ ≤
      6 * (sz.size n : ℝ) * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 4 * ‖y‖ ^ 2 := by
  set η := etaOf (BAmF sz lam0 E n) u with hηdef
  set z := ztOf (BAmF sz lam0 E n) (E n) u with hzdef
  have hz0 : z.im ≠ 0 := by rw [hzdef, ztOf_im]; exact hη.ne'
  have hzη : η ≤ |z.im| := by rw [hzdef, ztOf_im, abs_of_pos hη]
  have hH0 := TwistGridTail_Hh_herm sz lam0 n hM
  have hline : ∀ s : ℝ, ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + (M + (s : ℂ) • y) =
      (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) + (s : ℂ) • y := fun s => by abel
  have hMs : ∀ s : ℝ, (M + (s : ℂ) • y).IsHermitian := fun s => StepDecompLoop_isHermitian_add_realSmul hM hy s
  obtain ⟨φ₁, φ₂, hd1, hd2, -, hb⟩ := StepDecompLoop_word_jets
    (R₁ := fun s : ℝ => Gres ((((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) + (s : ℂ) • y) z (σ 0))
    (R₂ := fun s : ℝ => Gres ((((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) + (s : ℂ) • y) z (σ 1))
    (D := y) (Ep := TwistGridTail_Ea n b) (Eq := TwistGridTail_Q n c₁ c₂) (K := η⁻¹)
    (e := ((sz.W n : ℝ) ^ d)⁻¹)
    (StepDecompLoop_hasDerivAt_Gres hH0 hy hz0 (σ 0)) (StepDecompLoop_hasDerivAt_Gres hH0 hy hz0 (σ 1))
    (fun t => norm_Gsig_le_inv_eta (StepDecompLoop_isHermitian_add_realSmul hH0 hy t) hη hzη (σ 0))
    (fun t => norm_Gsig_le_inv_eta (StepDecompLoop_isHermitian_add_realSmul hH0 hy t) hη hzη (σ 1))
    (TwistGridTail_norm_Ea n b) (TwistGridTail_norm_Q n c₁ c₂)
  have hφ : ∀ s : ℝ, TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b (M + (s : ℂ) • y) =
      Matrix.trace (Gres ((((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) + (s : ℂ) • y) z (σ 0) * TwistGridTail_Ea n b *
        (Gres ((((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) + (s : ℂ) • y) z (σ 1) * TwistGridTail_Q n c₁ c₂)) := by
    intro s
    rw [TwistGridTail_phi_trace_herm sz lam0 E n u σ c₁ c₂ b (hMs s), hline s]
    simp only [Matrix.mul_assoc]
    try rfl
  have h₀ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b (M + (s : ℂ) • y)) (φ₁ t) t := by
    intro t
    have : (fun s : ℝ => TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b (M + (s : ℂ) • y)) = fun s : ℝ =>
        Matrix.trace (Gres ((((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) + (s : ℂ) • y) z (σ 0) * TwistGridTail_Ea n b *
          (Gres ((((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) + (s : ℂ) • y) z (σ 1) * TwistGridTail_Q n c₁ c₂)) :=
      funext hφ
    rw [this]
    exact hd1 t
  have hΦ : ∀ M', M'.IsHermitian → ContDiffAt ℝ 2 (TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b) M' := fun M' hM' =>
    (TwistGridTail_hermTestFun sz lam0 E n hη σ c₁ c₂ b).contDiffAt M' hM'
  rw [StepDecompLoop_fderiv2_of_line hΦ hM hy h₀ hd2]
  refine (hb 0).trans ?_
  rw [Sizes.card_Idx]
  have he := TwistGridTail_e_nonneg (sz := sz) (d := d) n
  have he1 := TwistGridTail_e_le_one (sz := sz) (d := d) n
  have hN : (0 : ℝ) ≤ (sz.size n : ℝ) := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ η⁻¹ ^ 4 := by positivity
  have hy2 : (0 : ℝ) ≤ ‖y‖ ^ 2 := by positivity
  calc (sz.size n : ℝ) * (6 * η⁻¹ ^ 4 * (((sz.W n : ℝ) ^ d)⁻¹) ^ 2 * ‖y‖ ^ 2)
      = (6 * (sz.size n : ℝ) * η⁻¹ ^ 4 * ‖y‖ ^ 2) * (((sz.W n : ℝ) ^ d)⁻¹) ^ 2 := by ring
    _ ≤ (6 * (sz.size n : ℝ) * η⁻¹ ^ 4 * ‖y‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ he he1) (by positivity)
    _ = 6 * (sz.size n : ℝ) * η⁻¹ ^ 4 * ‖y‖ ^ 2 := mul_one _

end Obs

/-! ## 3. The gradient (D.2) as a matrix, the first derivative and the variance identity -/

section Grad

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- The gradient matrix of `L̃_{σ,(b;c₁,c₂)}` at `(u, H)`: `Der_{y x} = ∂_{xy} L̃ = twDerM x y` (D.2). -/
private def TwistGridTail_Der (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Matrix.of fun y x => twDerM sz lam0 E n u H σ b c₁ c₂ x y

/-- The two block sums of (D.2) as the entries of two matrix words: `G₁ E_b G₂ Q G₁` and `G₂ Q G₁ E_b G₂`. -/
private theorem TwistGridTail_words_apply (G₁ G₂ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (b c₁ c₂ : Zd d (sz.L n)) (y x : Idx d (sz.L n) (sz.W n)) :
    (G₁ * TwistGridTail_Ea n b * G₂ * TwistGridTail_Q n c₁ c₂ * G₁) y x =
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, G₁ y z * G₂ z w * G₁ (twShift n c₂ w) x ∧
    (G₂ * TwistGridTail_Q n c₁ c₂ * G₁ * TwistGridTail_Ea n b * G₂) y x =
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, G₂ y w * G₁ (twShift n c₂ w) z * G₂ z x := by
  set e : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with he
  have h1 : ∀ (f : Idx d (sz.L n) (sz.W n) → ℂ) (c : Zd d (sz.L n)),
      ∑ x ∈ twBlk n c, f x = ∑ x, if x ∈ twBlk n c then f x else 0 := fun f c => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hEa : ∀ (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) p z,
      (A * TwistGridTail_Ea n b) p z = A p z * (if z ∈ twBlk n b then e else 0) := fun A p z => by
    rw [TwistGridTail_Ea, Matrix.mul_diagonal]
  have hA : ∀ (A B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) p w,
      (A * TwistGridTail_Ea n b * B) p w = ∑ z, A p z * (if z ∈ twBlk n b then e else 0) * B z w := fun A B p w => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun z _ => by rw [hEa]
  have hQ : ∀ (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) w r,
      (TwistGridTail_Q n c₁ c₂ * A) w r = if w ∈ twBlk n c₁ then e * A (twShift n c₂ w) r else 0 :=
    fun A w r => TwistGridTail_Q_mul n c₁ c₂ A w r
  have hpull : ∀ (c : Prop) [Decidable c] (F : Idx d (sz.L n) (sz.W n) → ℂ),
      (if c then ∑ x, F x else 0) = ∑ x, if c then F x else 0 := fun c _ F => by split_ifs <;> simp
  constructor
  · rw [Matrix.mul_assoc (G₁ * TwistGridTail_Ea n b * G₂) (TwistGridTail_Q n c₁ c₂) G₁, Matrix.mul_apply]
    simp only [hQ, hA]
    simp only [h1, hpull, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> first | rfl | ring
  · have hB : ∀ p, (G₁ * (TwistGridTail_Ea n b * G₂)) p x =
        ∑ z, G₁ p z * (if z ∈ twBlk n b then e * G₂ z x else 0) := fun p => by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun z _ => by rw [TwistGridTail_Ea_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_apply]
    simp only [hQ, hB]
    simp only [h1, hpull, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> first | rfl | ring

private theorem TwistGridTail_twChg_Gc (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (τ : Bool) :
    twChg (twGM sz lam0 E n u H) τ = fun x y => TwistGridTail_Gc (ztOf (BAmF sz lam0 E n) (E n) u) H τ x y := by
  funext x y
  cases τ
  · simp [twChg, twGM, TwistGridTail_Gc, Matrix.conjTranspose_apply]
  · simp [twChg, twGM, TwistGridTail_Gc]

/-- **(D.2) as a matrix identity**: for Hermitian `H`, `Der = -(G₁ E_b G₂ Q G₁ + G₂ Q G₁ E_b G₂)`. -/
private theorem TwistGridTail_Der_eq (u : ℝ) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) :
    TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂ =
      -(Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * TwistGridTail_Ea n b *
          Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) * TwistGridTail_Q n c₁ c₂ *
          Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) +
        Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1) * TwistGridTail_Q n c₁ c₂ *
          Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0) * TwistGridTail_Ea n b *
          Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)) := by
  ext y x
  have h := TwistGridTail_words_apply (sz := sz) n (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0))
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)) b c₁ c₂ y x
  simp only [TwistGridTail_Der, Matrix.of_apply, twDerM, TwistGridTail_twChg_Gc, TwistGridTail_Gc_herm hH,
    Matrix.neg_apply, Matrix.add_apply]
  rw [h.1, h.2]
  ring

private theorem TwistGridTail_trace_cyc {ι : Type*} [Fintype ι] [DecidableEq ι] (U X V : Matrix ι ι ℂ) :
    Matrix.trace (U * X * V) = Matrix.trace (X * (V * U)) := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

private theorem TwistGridTail_trace_deriv_alg {ι : Type*} [Fintype ι] [DecidableEq ι] (A B X E Q : Matrix ι ι ℂ) :
    Matrix.trace (-(A * X * A) * E * (B * Q) - A * E * (B * X * B * Q)) =
      Matrix.trace (-(A * E * B * Q * A + B * Q * A * E * B) * X) := by
  have t1 : Matrix.trace (A * X * A * E * (B * Q)) = Matrix.trace (X * (A * E * B * Q * A)) := by
    have := TwistGridTail_trace_cyc A X (A * E * (B * Q))
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  have t2 : Matrix.trace (A * E * (B * X * B * Q)) = Matrix.trace (X * (B * Q * A * E * B)) := by
    have := TwistGridTail_trace_cyc (A * E * B) X (B * Q)
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  have t3 : ∀ Y : Matrix ι ι ℂ, Matrix.trace (Y * X) = Matrix.trace (X * Y) := fun Y => Matrix.trace_mul_comm Y X
  simp only [Matrix.neg_mul, Matrix.trace_sub, Matrix.trace_neg, Matrix.add_mul, Matrix.trace_add]
  rw [t1, t2, t3 (A * E * B * Q * A), t3 (B * Q * A * E * B)]
  ring

/-- **The first derivative** (D.2): for Hermitian `M`, `X`, `∂_X L̃_b (g₀ Ψ + M) = tr (Der_b X)`. -/
private theorem TwistGridTail_dirDeriv {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool)
    (c₁ c₂ b : Zd d (sz.L n)) {M X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) (hX : X.IsHermitian) :
    dirDerivN (TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b) M X =
      Matrix.trace (TwistGridTail_Der sz lam0 E n u (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) σ b c₁ c₂ * X) := by
  set z := ztOf (BAmF sz lam0 E n) (E n) u with hzdef
  have hz0 : z.im ≠ 0 := by rw [hzdef, ztOf_im]; exact hη.ne'
  have hH0 := TwistGridTail_Hh_herm sz lam0 n hM
  set H0 := ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M with hH0def
  have hline : ∀ s : ℝ, ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + (M + (s : ℂ) • X) = H0 + (s : ℂ) • X :=
    fun s => by rw [hH0def]; abel
  have hMs : ∀ s : ℝ, (M + (s : ℂ) • X).IsHermitian := fun s => StepDecompLoop_isHermitian_add_realSmul hM hX s
  have hφ : ∀ s : ℝ, TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b (M + (s : ℂ) • X) =
      Matrix.trace (Gres (H0 + (s : ℂ) • X) z (σ 0) * TwistGridTail_Ea n b *
        (Gres (H0 + (s : ℂ) • X) z (σ 1) * TwistGridTail_Q n c₁ c₂)) := by
    intro s
    rw [TwistGridTail_phi_trace_herm sz lam0 E n u σ c₁ c₂ b (hMs s), hline s]
    simp only [Matrix.mul_assoc]
    try rfl
  have hd := StepDecompLoop_trace_hasDerivAt (StepDecompLoop_word_jet1
    (R₁ := fun s : ℝ => Gres (H0 + (s : ℂ) • X) z (σ 0)) (R₂ := fun s : ℝ => Gres (H0 + (s : ℂ) • X) z (σ 1))
    (D := X) (Ep := TwistGridTail_Ea n b) (Eq := TwistGridTail_Q n c₁ c₂)
    (StepDecompLoop_hasDerivAt_Gres hH0 hX hz0 (σ 0)) (StepDecompLoop_hasDerivAt_Gres hH0 hX hz0 (σ 1)) 0)
  have hfun : (fun y : ℝ => TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b (M + (y : ℂ) • X)) = fun s : ℝ =>
      Matrix.trace (Gres (H0 + (s : ℂ) • X) z (σ 0) * TwistGridTail_Ea n b *
        (Gres (H0 + (s : ℂ) • X) z (σ 1) * TwistGridTail_Q n c₁ c₂)) := funext hφ
  unfold dirDerivN
  rw [hfun, hd.deriv, TwistGridTail_Der_eq sz lam0 E n u hH0 σ b c₁ c₂]
  simp only [Complex.ofReal_zero, zero_smul, add_zero]
  exact TwistGridTail_trace_deriv_alg _ _ _ _ _

private theorem TwistGridTail_trace_eq_pair (A X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    Matrix.trace (A * X) = QVIdentity_pair X (fun l k => A l k) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, QVIdentity_pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `svar_{kl} = W^{-d} S^{(B)}(0)_{[k][l]}` with `S^{(B)}(0) = 1`, as the weight of `twEEM`. -/
private theorem TwistGridTail_svarF_zero (k l : Idx d (sz.L n) (sz.W n)) :
    ((svarF d (sz.L n) (sz.W n) 0 k l : ℝ) : ℂ) =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) k).1 (split d (sz.L n) (sz.W n) l).1 := by
  have h := QVIdentity_svarF_cast (d := d) (L := sz.L n) (W := sz.W n) (0 : ℝ) (split d (sz.L n) (sz.W n) k)
    (split d (sz.L n) (sz.W n) l)
  have hk : (splitEquiv d (sz.L n) (sz.W n)).symm (split d (sz.L n) (sz.W n) k) = k :=
    (splitEquiv d (sz.L n) (sz.W n)).symm_apply_apply k
  have hl : (splitEquiv d (sz.L n) (sz.W n)).symm (split d (sz.L n) (sz.W n) l) = l :=
    (splitEquiv d (sz.L n) (sz.W n)).symm_apply_apply l
  rw [hk, hl] at h
  rw [h, EMn2BA_SB_zero (d := d) (sz.L n)]
  change _ = _ * (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) _ _
  ring

/-- **The variance identity** (constant `1`): `Σ_c gvar_c |Σ_b κ_b tr (Der_b X_c)|² = Re Σ_{b,b'} κ_b conj κ_{b'} twEEM(b,b')`
(`gvar` at the coupling `0` of the walk `sz.withLam 0`; `Der_{yx} = ∂_{xy} L̃`, `S^{(B)}(0) = 1`). -/
private theorem TwistGridTail_quadVar (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (κ : Zd d (sz.L n) → ℂ) :
    ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) *
        ‖∑ b, κ b * Matrix.trace (TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂ * coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 =
      (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u H σ b b' c₁ c₂).re := by
  set A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := ∑ b, κ b • TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂ with hA
  have hD : ∀ c, ∑ b, κ b * Matrix.trace (TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂ * coordinateMatrix d (sz.L n) (sz.W n) c) =
      QVIdentity_pair (coordinateMatrix d (sz.L n) (sz.W n) c) (fun l k => A l k) := by
    intro c
    rw [← TwistGridTail_trace_eq_pair, hA, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hmc : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcast : (((∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) *
        ‖∑ b, κ b * Matrix.trace (TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂ * coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ c : CoordF d (sz.L n) (sz.W n), ((gvarF d (sz.L n) (sz.W n) 0 c : ℝ) : ℂ) *
        (QVIdentity_pair (coordinateMatrix d (sz.L n) (sz.W n) c) (fun l k => A l k) *
          (starRingEnd ℂ) (QVIdentity_pair (coordinateMatrix d (sz.L n) (sz.W n) c) (fun l k => A l k))) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.ofReal_mul, hmc, hD c]
  have hfin := QVIdentity_coord_sum (d := d) (L := sz.L n) (W := sz.W n) (0 : ℝ) (fun l k => A l k) (fun l k => A l k)
  have hAe : ∀ k l, A l k = ∑ b, κ b * twDerM sz lam0 E n u H σ b c₁ c₂ k l := fun k l => by
    rw [hA, Matrix.sum_apply]
    simp [TwistGridTail_Der]
  have hexp : ∑ k, ∑ l, ((svarF d (sz.L n) (sz.W n) 0 k l : ℝ) : ℂ) * (A l k * (starRingEnd ℂ) (A l k)) =
      ∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u H σ b b' c₁ c₂ := by
    have h1 : ∀ k l, ((svarF d (sz.L n) (sz.W n) 0 k l : ℝ) : ℂ) * (A l k * (starRingEnd ℂ) (A l k)) =
        ∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * (((svarF d (sz.L n) (sz.W n) 0 k l : ℝ) : ℂ) *
          (twDerM sz lam0 E n u H σ b c₁ c₂ k l * (starRingEnd ℂ) (twDerM sz lam0 E n u H σ b' c₁ c₂ k l))) := by
      intro k l
      rw [hAe, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [map_mul]
      ring
    simp only [h1]
    rw [← QVIdentity_sum_swap4]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [twEEM, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TwistGridTail_svarF_zero sz lam0 E n k l]
  have hre : (((∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) *
        ‖∑ b, κ b * Matrix.trace (TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂ * coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u H σ b b' c₁ c₂ := by
    rw [hcast, hfin, hexp]
  have := congrArg Complex.re hre
  rwa [Complex.ofReal_re] at this

end Grad

/-! ## 4. Crude bounds on `Der` and `twEEM`, and the shift `u → u'` -/

section Crude

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

private theorem TwistGridTail_word_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (A₁ C₁ A₂ C₂ A₃ : Matrix ι ι ℂ)
    {k₁ k₂ k₃ e : ℝ} (h₁ : ‖A₁‖ ≤ k₁) (h₂ : ‖A₂‖ ≤ k₂) (h₃ : ‖A₃‖ ≤ k₃) (hc₁ : ‖C₁‖ ≤ e) (hc₂ : ‖C₂‖ ≤ e) :
    ‖A₁ * C₁ * A₂ * C₂ * A₃‖ ≤ k₁ * e * k₂ * e * k₃ :=
  StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul (StepDecompLoop_nmul h₁ hc₁) h₂) hc₂) h₃

private theorem TwistGridTail_word_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (A₁ A₂ A₃ B₁ B₂ B₃ C₁ C₂ : Matrix ι ι ℂ)
    {K e δ : ℝ} (ha₂ : ‖A₂‖ ≤ K) (ha₃ : ‖A₃‖ ≤ K) (hb₁ : ‖B₁‖ ≤ K) (hb₂ : ‖B₂‖ ≤ K)
    (hd₁ : ‖A₁ - B₁‖ ≤ δ) (hd₂ : ‖A₂ - B₂‖ ≤ δ) (hd₃ : ‖A₃ - B₃‖ ≤ δ) (hc₁ : ‖C₁‖ ≤ e) (hc₂ : ‖C₂‖ ≤ e) :
    ‖A₁ * C₁ * A₂ * C₂ * A₃ - B₁ * C₁ * B₂ * C₂ * B₃‖ ≤ 3 * (δ * K ^ 2 * e ^ 2) := by
  have hid : A₁ * C₁ * A₂ * C₂ * A₃ - B₁ * C₁ * B₂ * C₂ * B₃ =
      (A₁ - B₁) * C₁ * A₂ * C₂ * A₃ + B₁ * C₁ * (A₂ - B₂) * C₂ * A₃ + B₁ * C₁ * B₂ * C₂ * (A₃ - B₃) := by
    noncomm_ring
  rw [hid]
  have w1 := TwistGridTail_word_norm (A₁ - B₁) C₁ A₂ C₂ A₃ hd₁ ha₂ ha₃ hc₁ hc₂
  have w2 := TwistGridTail_word_norm B₁ C₁ (A₂ - B₂) C₂ A₃ hb₁ hd₂ ha₃ hc₁ hc₂
  have w3 := TwistGridTail_word_norm B₁ C₁ B₂ C₂ (A₃ - B₃) hb₁ hb₂ hd₃ hc₁ hc₂
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
  nlinarith [w1, w2, w3]

/-- The resolvent identity `G(w') - G(w) = (w' - w) G(w') G(w)` for Hermitian `H` and `Im w, Im w' ≠ 0`. -/
private theorem TwistGridTail_resolvent_diff {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {w w' : ℂ} (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    Ring.inverse (H - w' • (1 : Matrix ι ι ℂ)) - Ring.inverse (H - w • (1 : Matrix ι ι ℂ)) =
      (w' - w) • (Ring.inverse (H - w' • (1 : Matrix ι ι ℂ)) * Ring.inverse (H - w • (1 : Matrix ι ι ℂ))) := by
  have hA := isUnit_sub_smul_of_isHermitian hH hw
  have hA' := isUnit_sub_smul_of_isHermitian hH hw'
  have hdA : IsUnit (H - w • (1 : Matrix ι ι ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hdA' : IsUnit (H - w' • (1 : Matrix ι ι ℂ)).det := (Matrix.isUnit_iff_isUnit_det _).mp hA'
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
  set A := H - w • (1 : Matrix ι ι ℂ)
  set A' := H - w' • (1 : Matrix ι ι ℂ)
  have hAA' : A - A' = (w' - w) • (1 : Matrix ι ι ℂ) := by
    simp only [A, A']
    rw [sub_smul]
    abel
  have key : A'⁻¹ - A⁻¹ = A'⁻¹ * (A - A') * A⁻¹ := by
    rw [mul_sub, sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdA, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hdA', Matrix.one_mul]
  rw [key, hAA']
  simp [Matrix.mul_smul, Matrix.smul_mul]

private theorem TwistGridTail_Gres_diff_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) (σ : Bool) {K : ℝ} (h : ‖Gres H z σ‖ ≤ K) (h' : ‖Gres H z' σ‖ ≤ K) :
    ‖Gres H z' σ - Gres H z σ‖ ≤ ‖z' - z‖ * K * K := by
  have key : ∀ {w w' : ℂ}, w.im ≠ 0 → w'.im ≠ 0 → ‖w' - w‖ = ‖z' - z‖ →
      ‖Ring.inverse (H - w' • (1 : Matrix ι ι ℂ))‖ ≤ K → ‖Ring.inverse (H - w • (1 : Matrix ι ι ℂ))‖ ≤ K →
      ‖Ring.inverse (H - w' • (1 : Matrix ι ι ℂ)) - Ring.inverse (H - w • (1 : Matrix ι ι ℂ))‖ ≤ ‖z' - z‖ * K * K := by
    intro w w' hw hw' hww' hn hn'
    rw [TwistGridTail_resolvent_diff hH hw hw', norm_smul, hww', mul_assoc]
    exact mul_le_mul_of_nonneg_left (StepDecompLoop_nmul hn hn') (norm_nonneg _)
  cases σ
  · simp only [Gres, Bool.false_eq_true, ite_false] at h h' ⊢
    refine key (by simpa using hz) (by simpa using hz') ?_ h' h
    rw [← map_sub, Complex.norm_conj]
  · simp only [Gres, ite_true] at h h' ⊢
    exact key hz hz' rfl h' h

/-- `‖Der‖ ≤ 2 η⁻³` (two words of three resolvents, `‖E_b‖, ‖Q‖ ≤ W^{-d} ≤ 1`), for Hermitian `H`. -/
private theorem TwistGridTail_Der_norm {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) :
    ‖TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂‖ ≤ 2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3 := by
  set η := etaOf (BAmF sz lam0 E n) u with hηdef
  have hzη : η ≤ |(ztOf (BAmF sz lam0 E n) (E n) u).im| := by rw [ztOf_im, abs_of_pos hη]
  have hG : ∀ τ : Bool, ‖Gres H (ztOf (BAmF sz lam0 E n) (E n) u) τ‖ ≤ η⁻¹ := fun τ => norm_Gsig_le_inv_eta hH hη hzη τ
  have he := TwistGridTail_e_nonneg (sz := sz) (d := d) n
  have he1 := TwistGridTail_e_le_one (sz := sz) (d := d) n
  have w1 := TwistGridTail_word_norm (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0)) (TwistGridTail_Ea n b)
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)) (TwistGridTail_Q n c₁ c₂)
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0)) (hG _) (hG _) (hG _) (TwistGridTail_norm_Ea n b) (TwistGridTail_norm_Q n c₁ c₂)
  have w2 := TwistGridTail_word_norm (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)) (TwistGridTail_Q n c₁ c₂)
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0)) (TwistGridTail_Ea n b)
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)) (hG _) (hG _) (hG _) (TwistGridTail_norm_Q n c₁ c₂) (TwistGridTail_norm_Ea n b)
  rw [TwistGridTail_Der_eq sz lam0 E n u hH σ b c₁ c₂, norm_neg]
  refine (norm_add_le _ _).trans ?_
  have hK : (0 : ℝ) ≤ η⁻¹ := by positivity
  have hee : ((sz.W n : ℝ) ^ d)⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹ ≤ 1 := by nlinarith
  have hb : η⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹ * η⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹ * η⁻¹ ≤ η⁻¹ ^ 3 := by
    calc η⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹ * η⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹ * η⁻¹ =
        η⁻¹ ^ 3 * (((sz.W n : ℝ) ^ d)⁻¹ * ((sz.W n : ℝ) ^ d)⁻¹) := by ring
      _ ≤ η⁻¹ ^ 3 * 1 := mul_le_mul_of_nonneg_left hee (by positivity)
      _ = η⁻¹ ^ 3 := mul_one _
  linarith

/-- `etaOf` is antitone in `u` (for `Im m > 0`). -/
private theorem TwistGridTail_eta_anti {m : ℂ} (hm : 0 < m.im) {u u' : ℝ} (h : u ≤ u') :
    etaOf m u' ≤ etaOf m u := by
  unfold etaOf
  nlinarith

/-- **The shift of the gradient**: `‖Der_{u'} - Der_u‖ ≤ 6 (u' - u) η_{u'}⁻⁴` for `u ≤ u'`, `‖m‖ ≤ 1`. -/
private theorem TwistGridTail_Der_shift {u u' : ℝ} (hu : u ≤ u') (hη' : 0 < etaOf (BAmF sz lam0 E n) u')
    (hm : 0 < (BAmF sz lam0 E n).im) (hmn : ‖BAmF sz lam0 E n‖ ≤ 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) :
    ‖TwistGridTail_Der sz lam0 E n u' H σ b c₁ c₂ - TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂‖ ≤
      6 * ((u' - u) * (etaOf (BAmF sz lam0 E n) u')⁻¹ ^ 4) := by
  set η' := etaOf (BAmF sz lam0 E n) u' with hη'def
  have hη : 0 < etaOf (BAmF sz lam0 E n) u := lt_of_lt_of_le hη' (TwistGridTail_eta_anti hm hu)
  have hηle : η' ≤ etaOf (BAmF sz lam0 E n) u := TwistGridTail_eta_anti hm hu
  have hz0 : (ztOf (BAmF sz lam0 E n) (E n) u).im ≠ 0 := by rw [ztOf_im]; exact hη.ne'
  have hz0' : (ztOf (BAmF sz lam0 E n) (E n) u').im ≠ 0 := by rw [ztOf_im]; exact hη'.ne'
  have hzη : η' ≤ |(ztOf (BAmF sz lam0 E n) (E n) u).im| := by rw [ztOf_im, abs_of_pos hη]; exact hηle
  have hzη' : η' ≤ |(ztOf (BAmF sz lam0 E n) (E n) u').im| := by rw [ztOf_im, abs_of_pos hη']
  have hG : ∀ τ : Bool, ‖Gres H (ztOf (BAmF sz lam0 E n) (E n) u) τ‖ ≤ η'⁻¹ := fun τ => norm_Gsig_le_inv_eta hH hη' hzη τ
  have hG' : ∀ τ : Bool, ‖Gres H (ztOf (BAmF sz lam0 E n) (E n) u') τ‖ ≤ η'⁻¹ := fun τ => norm_Gsig_le_inv_eta hH hη' hzη' τ
  have hzz : ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ ≤ u' - u := by
    have : ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u = ((u - u' : ℝ) : ℂ) * BAmF sz lam0 E n := by
      simp only [ztOf]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    calc -(u - u') * ‖BAmF sz lam0 E n‖ ≤ -(u - u') * 1 :=
          mul_le_mul_of_nonneg_left hmn (by linarith)
      _ = u' - u := by ring
  have hdiff : ∀ τ : Bool, ‖Gres H (ztOf (BAmF sz lam0 E n) (E n) u') τ - Gres H (ztOf (BAmF sz lam0 E n) (E n) u) τ‖ ≤
      (u' - u) * η'⁻¹ * η'⁻¹ := fun τ =>
    (TwistGridTail_Gres_diff_norm hH hz0 hz0' τ (hG τ) (hG' τ)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzz (by positivity)) (by positivity))
  have he := TwistGridTail_e_nonneg (sz := sz) (d := d) n
  have he1 := TwistGridTail_e_le_one (sz := sz) (d := d) n
  rw [TwistGridTail_Der_eq sz lam0 E n u' hH σ b c₁ c₂, TwistGridTail_Der_eq sz lam0 E n u hH σ b c₁ c₂]
  have w1 := TwistGridTail_word_sub (Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 0)) (Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 1))
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 0)) (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0))
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)) (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0))
    (TwistGridTail_Ea n b) (TwistGridTail_Q n c₁ c₂) (hG' _) (hG' _) (hG _) (hG _) (hdiff _) (hdiff _) (hdiff _)
    (TwistGridTail_norm_Ea n b) (TwistGridTail_norm_Q n c₁ c₂)
  have w2 := TwistGridTail_word_sub (Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 1)) (Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 0))
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 1)) (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1))
    (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0)) (Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1))
    (TwistGridTail_Q n c₁ c₂) (TwistGridTail_Ea n b) (hG' _) (hG' _) (hG _) (hG _) (hdiff _) (hdiff _) (hdiff _)
    (TwistGridTail_norm_Q n c₁ c₂) (TwistGridTail_norm_Ea n b)
  have hid : ∀ (P P' Q Q' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      -(P' + Q') - -(P + Q) = -((P' - P) + (Q' - Q)) := fun P P' Q Q' => by abel
  rw [hid, norm_neg]
  refine (norm_add_le _ _).trans ?_
  have hee : ((sz.W n : ℝ) ^ d)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ he he1
  have hK : (0 : ℝ) ≤ η'⁻¹ := by positivity
  have hδ : (0 : ℝ) ≤ (u' - u) * η'⁻¹ * η'⁻¹ := by
    have := sub_nonneg.2 hu
    positivity
  have hfin : 3 * ((u' - u) * η'⁻¹ * η'⁻¹ * η'⁻¹ ^ 2 * ((sz.W n : ℝ) ^ d)⁻¹ ^ 2) ≤ 3 * ((u' - u) * η'⁻¹ ^ 4) := by
    have : (u' - u) * η'⁻¹ * η'⁻¹ * η'⁻¹ ^ 2 * ((sz.W n : ℝ) ^ d)⁻¹ ^ 2 ≤ (u' - u) * η'⁻¹ ^ 4 := by
      calc (u' - u) * η'⁻¹ * η'⁻¹ * η'⁻¹ ^ 2 * ((sz.W n : ℝ) ^ d)⁻¹ ^ 2 =
          ((u' - u) * η'⁻¹ ^ 4) * ((sz.W n : ℝ) ^ d)⁻¹ ^ 2 := by ring
        _ ≤ ((u' - u) * η'⁻¹ ^ 4) * 1 := mul_le_mul_of_nonneg_left hee (by
            have := sub_nonneg.2 hu
            positivity)
        _ = (u' - u) * η'⁻¹ ^ 4 := mul_one _
    linarith
  linarith [w1, w2, hfin]

private theorem TwistGridTail_twDerM_norm {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖twDerM sz lam0 E n u H σ b c₁ c₂ x y‖ ≤ 2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3 :=
  (norm_matrix_entry_le_opNorm (TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂) y x).trans
    (TwistGridTail_Der_norm sz lam0 E n hη hH σ b c₁ c₂)

private theorem TwistGridTail_S_norm_le (p q : Zd d (sz.L n)) : ‖(baFM sz lam0 E).S n p q‖ ≤ 1 := by
  change ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) p q‖ ≤ 1
  by_cases h : p = q <;> simp [Matrix.one_apply, h]

private theorem TwistGridTail_norm_e : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ ≤ 1 := by
  have h := TwistGridTail_e_le_one (sz := sz) (d := d) n
  simpa using h

/-- **Crude bound**: `‖twEEM_{u}(H)(b,b')‖ ≤ N² (2 η_u⁻³)²` (twin of `difRep2_norm_STeeM_le_N`). -/
private theorem TwistGridTail_norm_twEEM {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (b b' c₁ c₂ : Zd d (sz.L n)) :
    ‖twEEM sz lam0 E n u H σ b b' c₁ c₂‖ ≤ (sz.size n : ℝ) ^ 2 * (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2 := by
  have hD := TwistGridTail_twDerM_norm sz lam0 E n hη hH σ
  have hterm : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (twDerM sz lam0 E n u H σ b c₁ c₂ x y * (starRingEnd ℂ) (twDerM sz lam0 E n u H σ b' c₁ c₂ x y))‖ ≤
      (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2 := by
    intro x y
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, sq]
    have h1 := TwistGridTail_norm_e (sz := sz) (d := d) n
    have h2 := TwistGridTail_S_norm_le sz lam0 E n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1
    have h3 := hD b c₁ c₂ x y
    have h4 := hD b' c₁ c₂ x y
    calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ * ‖(baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1‖ *
          (‖twDerM sz lam0 E n u H σ b c₁ c₂ x y‖ * ‖twDerM sz lam0 E n u H σ b' c₁ c₂ x y‖)
        ≤ 1 * 1 * ((2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) * (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3)) := by
          gcongr
      _ = _ := by ring
  unfold twEEM
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖∑ y, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (twDerM sz lam0 E n u H σ b c₁ c₂ x y * (starRingEnd ℂ) (twDerM sz lam0 E n u H σ b' c₁ c₂ x y))‖
      ≤ ∑ x : Idx d (sz.L n) (sz.W n), ∑ y : Idx d (sz.L n) (sz.W n), (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2 :=
        Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hterm x y)
    _ = (sz.size n : ℝ) ^ 2 * (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Sizes.card_Idx]
        ring

/-- **The shift of the QV**: for `u ≤ u'`, `‖twEEM_{u'}(H)(b,b) - twEEM_u(H)(b,b)‖ ≤ N² · 24 (u' - u) η_{u'}⁻⁷`
(twin of `difRep2_eeShiftErrN_le`; `(|D'|+|D|) |D'-D|` with `|D| ≤ 2 η⁻³`, `‖Der_{u'} - Der_u‖ ≤ 6 (u'-u) η'⁻⁴`). -/
private theorem TwistGridTail_norm_twEEM_shift {u u' : ℝ} (hu : u ≤ u') (hη' : 0 < etaOf (BAmF sz lam0 E n) u')
    (hm : 0 < (BAmF sz lam0 E n).im) (hmn : ‖BAmF sz lam0 E n‖ ≤ 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) :
    ‖twEEM sz lam0 E n u' H σ b b c₁ c₂ - twEEM sz lam0 E n u H σ b b c₁ c₂‖ ≤
      (sz.size n : ℝ) ^ 2 * (24 * ((u' - u) * (etaOf (BAmF sz lam0 E n) u')⁻¹ ^ 7)) := by
  set η' := etaOf (BAmF sz lam0 E n) u' with hη'def
  have hηle : η' ≤ etaOf (BAmF sz lam0 E n) u := TwistGridTail_eta_anti hm hu
  have hη : 0 < etaOf (BAmF sz lam0 E n) u := lt_of_lt_of_le hη' hηle
  have hΔ : 0 ≤ u' - u := sub_nonneg.2 hu
  have hD' := TwistGridTail_twDerM_norm sz lam0 E n hη' hH σ b c₁ c₂
  have hD : ∀ x y, ‖twDerM sz lam0 E n u H σ b c₁ c₂ x y‖ ≤ 2 * η'⁻¹ ^ 3 := fun x y =>
    (TwistGridTail_twDerM_norm sz lam0 E n hη hH σ b c₁ c₂ x y).trans (by
      gcongr)
  have hdiff : ∀ x y, ‖twDerM sz lam0 E n u' H σ b c₁ c₂ x y - twDerM sz lam0 E n u H σ b c₁ c₂ x y‖ ≤
      6 * ((u' - u) * η'⁻¹ ^ 4) := fun x y =>
    (norm_matrix_entry_le_opNorm (TwistGridTail_Der sz lam0 E n u' H σ b c₁ c₂ - TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂) y x).trans
      (TwistGridTail_Der_shift sz lam0 E n hu hη' hm hmn hH σ b c₁ c₂)
  have hterm : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (twDerM sz lam0 E n u' H σ b c₁ c₂ x y * (starRingEnd ℂ) (twDerM sz lam0 E n u' H σ b c₁ c₂ x y)) -
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
        (twDerM sz lam0 E n u H σ b c₁ c₂ x y * (starRingEnd ℂ) (twDerM sz lam0 E n u H σ b c₁ c₂ x y))‖ ≤
      24 * ((u' - u) * η'⁻¹ ^ 7) := by
    intro x y
    set a := twDerM sz lam0 E n u' H σ b c₁ c₂ x y with ha
    set a0 := twDerM sz lam0 E n u H σ b c₁ c₂ x y with ha0
    have hid : a * (starRingEnd ℂ) a - a0 * (starRingEnd ℂ) a0 = a * (starRingEnd ℂ) (a - a0) + (a - a0) * (starRingEnd ℂ) a0 := by
      rw [map_sub]; ring
    have h1 := TwistGridTail_norm_e (sz := sz) (d := d) n
    have h2 := TwistGridTail_S_norm_le sz lam0 E n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1
    rw [← mul_sub, norm_mul, norm_mul, hid]
    have h3 : ‖a * (starRingEnd ℂ) (a - a0) + (a - a0) * (starRingEnd ℂ) a0‖ ≤ 24 * ((u' - u) * η'⁻¹ ^ 7) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      have hda := hdiff x y
      have hdb := hD' x y
      have hdc := hD x y
      have hnn : 0 ≤ ‖a - a0‖ := norm_nonneg _
      calc ‖a‖ * ‖a - a0‖ + ‖a - a0‖ * ‖a0‖ ≤ (2 * η'⁻¹ ^ 3) * (6 * ((u' - u) * η'⁻¹ ^ 4)) +
            (6 * ((u' - u) * η'⁻¹ ^ 4)) * (2 * η'⁻¹ ^ 3) := by
            gcongr
        _ = 24 * ((u' - u) * η'⁻¹ ^ 7) := by ring
    calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ * ‖(baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1‖ *
          ‖a * (starRingEnd ℂ) (a - a0) + (a - a0) * (starRingEnd ℂ) a0‖ ≤ 1 * 1 * (24 * ((u' - u) * η'⁻¹ ^ 7)) := by
          gcongr
      _ = _ := by ring
  unfold twEEM
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖∑ y, _ - ∑ y, _‖ ≤ ∑ x : Idx d (sz.L n) (sz.W n), ∑ y : Idx d (sz.L n) (sz.W n), 24 * ((u' - u) * η'⁻¹ ^ 7) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hterm x y)
    _ = (sz.size n : ℝ) ^ 2 * (24 * ((u' - u) * η'⁻¹ ^ 7)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Sizes.card_Idx]
        ring

end Crude

/-! ## 5. Measurability in the matrix argument -/

section Meas

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

private theorem TwistGridTail_measurable_twChg (u : ℝ) (τ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twChg (twGM sz lam0 E n u H) τ x y) := by
  cases τ
  · simp only [twChg, Bool.false_eq_true, ite_false]
    exact Complex.continuous_conj.measurable.comp
      (walk_measurable_Gres_apply (ztOf (BAmF sz lam0 E n) (E n) u) true y x)
  · simp only [twChg, ite_true]
    exact walk_measurable_Gres_apply (ztOf (BAmF sz lam0 E n) (E n) u) true x y

private theorem TwistGridTail_measurable_twL2M (u : ℝ) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twL2M sz lam0 E n u H σ b c₁ c₂) := by
  unfold twL2M twLoopX
  refine Measurable.const_mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun w _ => ?_) _
  exact (TwistGridTail_measurable_twChg sz lam0 E n u (σ 1) x w).mul
    (TwistGridTail_measurable_twChg sz lam0 E n u (σ 0) (twShift n c₂ w) x)

private theorem TwistGridTail_measurable_twDerM (u : ℝ) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n))
    (x y : Idx d (sz.L n) (sz.W n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twDerM sz lam0 E n u H σ b c₁ c₂ x y) := by
  unfold twDerM
  simp only []
  refine Measurable.const_mul (Measurable.add (Finset.measurable_sum _ fun z _ => Finset.measurable_sum _ fun w _ => ?_)
    (Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun z _ => ?_)) _
  · exact ((TwistGridTail_measurable_twChg sz lam0 E n u (σ 0) y z).mul
      (TwistGridTail_measurable_twChg sz lam0 E n u (σ 1) z w)).mul
      (TwistGridTail_measurable_twChg sz lam0 E n u (σ 0) (twShift n c₂ w) x)
  · exact ((TwistGridTail_measurable_twChg sz lam0 E n u (σ 1) y w).mul
      (TwistGridTail_measurable_twChg sz lam0 E n u (σ 0) (twShift n c₂ w) z)).mul
      (TwistGridTail_measurable_twChg sz lam0 E n u (σ 1) z x)

private theorem TwistGridTail_measurable_twEEM (u : ℝ) (σ : Fin 2 → Bool) (b b' c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twEEM sz lam0 E n u H σ b b' c₁ c₂) := by
  unfold twEEM
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => Measurable.const_mul ?_ _
  exact (TwistGridTail_measurable_twDerM sz lam0 E n u σ b c₁ c₂ x y).mul
    (Complex.continuous_conj.measurable.comp (TwistGridTail_measurable_twDerM sz lam0 E n u σ b' c₁ c₂ x y))

private theorem TwistGridTail_measurable_phi (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n)) :
    Measurable (TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b) := by
  unfold TwistGridTail_phi
  refine (TwistGridTail_measurable_twL2M sz lam0 E n u σ b c₁ c₂).comp ?_
  exact Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.add_apply]
    exact measurable_const.add (measurable_id.eval_matrix)

end Meas

/-! ## 6. Target (b): the conditional mgf of the first-chaos increment `Σ_b κ_b Z_b` -/

section CondMGF

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

private theorem TwistGridTail_eta_pos {m : ℂ} (hm : 0 < m.im) {u : ℝ} (hu : u < 1) : 0 < etaOf m u := by
  unfold etaOf
  exact mul_pos (by linarith) hm

private theorem TwistGridTail_hC₂ {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) :
    ∀ (b : Zd d (sz.L n)) (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ (TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b)) M y y‖ ≤
        (6 * (sz.size n : ℝ) * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 4) * ‖y‖ ^ 2 := fun b M y hM hy =>
  (TwistGridTail_second_deriv_bound sz lam0 E n hη σ c₁ c₂ b hM hy).trans (le_of_eq (by ring))

/-- Test: the family at `sz.withLam 0` (same `L`, `W`). -/
private theorem TwistGridTail_hΦ' {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) :
    ∀ b : Zd d (sz.L n), HermTestFun (sz.withLam 0) n (TwistGridTail_phi sz lam0 E n u σ c₁ c₂ b) := fun b =>
  ⟨fun M hM => (TwistGridTail_hermTestFun sz lam0 E n hη σ c₁ c₂ b).contDiffAt M hM,
    (TwistGridTail_hermTestFun sz lam0 E n hη σ c₁ c₂ b).bdd₀⟩

/-- `Re Σ_{b,b'} κ_b conj κ_{b'} twEEM(b,b') ≤ (Σ ‖κ‖)² N² (2 η⁻³)²` (the crude deterministic bound). -/
private theorem TwistGridTail_re_QV_le {u : ℝ} (hη : 0 < etaOf (BAmF sz lam0 E n) u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (κ : Zd d (sz.L n) → ℂ) :
    (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u H σ b b' c₁ c₂).re ≤
      (∑ b, ‖κ b‖) ^ 2 * ((sz.size n : ℝ) ^ 2 * (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2) := by
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u H σ b b' c₁ c₂‖
      ≤ ∑ b, ∑ b', ‖κ b‖ * ‖κ b'‖ * ((sz.size n : ℝ) ^ 2 * (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2) := by
        refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (TwistGridTail_norm_twEEM sz lam0 E n hη hH σ b b' c₁ c₂) (by positivity)
    _ = (∑ b, ‖κ b‖) ^ 2 * ((sz.size n : ℝ) ^ 2 * (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2) := by
        rw [sq (∑ b, ‖κ b‖), Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]

/-- **The conditional exponential moment of the first-chaos increment** (twin of `difRepTail_condMGF_Z`,
`Path/DifREP2.lean:1404`): for weights `κ`, `Z = Σ_b κ_b Z_{j,b} = stepZCN` of the twisted family
`Φ_b(M) = L̃_{u_{j+1}}(g₀ Ψ + M)` with the kernel `(·, a) ↦ κ_a`, the real and imaginary parts are exponentially
integrable and have the conditional mgf at most `exp (r² Δ Re Σ_{b,b'} κ_b conj κ_{b'} twEEM_{u_{j+1}}(H_j)(b,b') / 2)`
given `F_j` (variance constant `1`: `TwistGridTail_quadVar`).  Hypotheses: `Im m_F > 0`, `u_{j+1} < 1`, `Δ ≥ 0`. -/
theorem TwistGridTail_condMGF_Z (j : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n))
    (hm : 0 < (BAmF sz lam0 E n).im) (hu : gridTime s t K n (j + 1) < 1) (hΔ : 0 ≤ gridStep s t K n)
    (κ : Zd d (sz.L n) → ℂ) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * (stepZCN (sz.withLam 0) s t K n j
        (TwistGridTail_phi sz lam0 E n (gridTime s t K n (j + 1)) σ c₁ c₂) (fun _ a => κ a) 0 ω).re))
      ((baStep2Mat sz lam0 E).Pp) ∧
    Integrable (fun ω => Real.exp (r * (stepZCN (sz.withLam 0) s t K n j
        (TwistGridTail_phi sz lam0 E n (gridTime s t K n (j + 1)) σ c₁ c₂) (fun _ a => κ a) 0 ω).im))
      ((baStep2Mat sz lam0 E).Pp) ∧
    ((baStep2Mat sz lam0 E).Pp)[fun ω => Real.exp (r * (stepZCN (sz.withLam 0) s t K n j
        (TwistGridTail_phi sz lam0 E n (gridTime s t K n (j + 1)) σ c₁ c₂) (fun _ a => κ a) 0 ω).re)
        | filt (sz.withLam 0) j] ≤ᵐ[(baStep2Mat sz lam0 E).Pp]
      (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') *
        twEEM sz lam0 E n (gridTime s t K n (j + 1)) ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b b' c₁ c₂).re) / 2)) ∧
    ((baStep2Mat sz lam0 E).Pp)[fun ω => Real.exp (r * (stepZCN (sz.withLam 0) s t K n j
        (TwistGridTail_phi sz lam0 E n (gridTime s t K n (j + 1)) σ c₁ c₂) (fun _ a => κ a) 0 ω).im)
        | filt (sz.withLam 0) j] ≤ᵐ[(baStep2Mat sz lam0 E).Pp]
      (fun ω => Real.exp (r ^ 2 * (gridStep s t K n * (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') *
        twEEM sz lam0 E n (gridTime s t K n (j + 1)) ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b b' c₁ c₂).re) / 2)) := by
  set u := gridTime s t K n (j + 1) with hudef
  have hη : 0 < etaOf (BAmF sz lam0 E n) u := TwistGridTail_eta_pos hm hu
  set Φ := TwistGridTail_phi sz lam0 E n u σ c₁ c₂ with hΦdef
  have hΦ := TwistGridTail_hΦ' sz lam0 E n hη σ c₁ c₂
  have hC₂ := TwistGridTail_hC₂ sz lam0 E n hη σ c₁ c₂
  set U : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun _ a => κ a with hU
  have hIntRe := integrable_stepZCN_re_of_hermTestFun (sz.withLam 0) s t K n j hΦ hC₂ hΔ U 0
  have hIntIm := integrable_stepZCN_im_of_hermTestFun (sz.withLam 0) s t K n j hΦ hC₂ hΔ U 0
  obtain ⟨-, hAm, -, -⟩ := stepDecompCN (sz.withLam 0) s t K n j hΦ hC₂ hΔ U 0 hIntRe hIntIm
  have hHpath : ∀ ω : PathΩ (sz.withLam 0), ((baStep2Mat sz lam0 E).Hpath s t K n j ω).IsHermitian := fun ω =>
    TwistGridTail_Hh_herm sz lam0 n (pathH_isHermitian (sz.withLam 0) s t K n j ω)
  -- the variance of the frozen gradient
  have hvar : ∀ ω : PathΩ (sz.withLam 0),
      linTrVar n (AbCN (sz.withLam 0) s t K n j Φ U 0 ω) ≤ (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') *
        twEEM sz lam0 E n u ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b b' c₁ c₂).re ∧
      linTrVar n ((-Complex.I) • AbCN (sz.withLam 0) s t K n j Φ U 0 ω) ≤ (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') *
        twEEM sz lam0 E n u ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b b' c₁ c₂).re := by
    intro ω
    have hM : (pathH (sz.withLam 0) s t K n j ω).IsHermitian := pathH_isHermitian (sz.withLam 0) s t K n j ω
    have hDeq : ∀ c : CoordF d ((sz.withLam 0).L n) ((sz.withLam 0).W n),
        Matrix.trace (AbCN (sz.withLam 0) s t K n j Φ U 0 ω * coordinateMatrix d ((sz.withLam 0).L n) ((sz.withLam 0).W n) c) =
        ∑ b, κ b * Matrix.trace (TwistGridTail_Der sz lam0 E n u ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b c₁ c₂ *
          coordinateMatrix d (sz.L n) (sz.W n) c) := by
      intro c
      have hX := coordinateMatrix_isHermitian d ((sz.withLam 0).L n) ((sz.withLam 0).W n) c
      have h1 := difRepTail_trace_eq (sz.withLam 0) hΦ κ hM hX
      have hA : AbCN (sz.withLam 0) s t K n j Φ U 0 ω = ∑ a, κ a • gradMat (Φ a) (pathH (sz.withLam 0) s t K n j ω) := rfl
      rw [hA]
      refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
      exact congrArg (κ b * ·) (TwistGridTail_dirDeriv sz lam0 E n hη σ c₁ c₂ b hM hX)
    obtain ⟨h1, h2⟩ := difRepTail_linTrVar_le (sz.withLam 0) n _ _ hDeq
    have hq := TwistGridTail_quadVar sz lam0 E n u ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ c₁ c₂ κ
    exact ⟨h1.trans (le_of_eq hq), h2.trans (le_of_eq hq)⟩
  -- the deterministic bound and sub-Gaussianity
  set S1 : ℝ := ∑ b, ‖κ b‖ with hS1
  set Bd : ℝ := (sz.size n : ℝ) ^ 2 * (2 * (etaOf (BAmF sz lam0 E n) u)⁻¹ ^ 3) ^ 2 with hBd
  set c0 : ℝ := gridStep s t K n * (S1 ^ 2 * Bd) with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  have hZ := stepDecompCN_Z_subG (sz.withLam 0) s t K n j hΦ U 0 Set.univ MeasurableSet.univ c0 hc0
    (fun ω _ => mul_le_mul_of_nonneg_left
      ((hvar ω).1.trans (TwistGridTail_re_QV_le sz lam0 E n hη (hHpath ω) σ c₁ c₂ κ)) hΔ)
    (fun ω _ => mul_le_mul_of_nonneg_left
      ((hvar ω).2.trans (TwistGridTail_re_QV_le sz lam0 E n hη (hHpath ω) σ c₁ c₂ κ)) hΔ)
  have hre_eq : ∀ ω, (stepZCN (sz.withLam 0) s t K n j Φ U 0 ω).re =
      Real.sqrt (gridStep s t K n) * linTr n (AbCN (sz.withLam 0) s t K n j Φ U 0 ω)
        (Sizes.seqXmat (sz.withLam 0) n (ω (j + 1))) := fun ω => by
    simp [stepZCN, stepZCN_re, stepZCN_im]
  have him_eq : ∀ ω, (stepZCN (sz.withLam 0) s t K n j Φ U 0 ω).im =
      Real.sqrt (gridStep s t K n) * linTr n ((-Complex.I) • AbCN (sz.withLam 0) s t K n j Φ U 0 ω)
        (Sizes.seqXmat (sz.withLam 0) n (ω (j + 1))) := fun ω => by
    simp [stepZCN, stepZCN_re, stepZCN_im]
  have hfre : (fun ω => Real.exp (r * (stepZCN (sz.withLam 0) s t K n j Φ U 0 ω).re)) =
      fun ω => Real.exp (r * (Real.sqrt (gridStep s t K n) * linTr n (AbCN (sz.withLam 0) s t K n j Φ U 0 ω)
        (Sizes.seqXmat (sz.withLam 0) n (ω (j + 1))))) := funext fun ω => by rw [hre_eq]
  have hfim : (fun ω => Real.exp (r * (stepZCN (sz.withLam 0) s t K n j Φ U 0 ω).im)) =
      fun ω => Real.exp (r * (Real.sqrt (gridStep s t K n) * linTr n ((-Complex.I) • AbCN (sz.withLam 0) s t K n j Φ U 0 ω)
        (Sizes.seqXmat (sz.withLam 0) n (ω (j + 1))))) := funext fun ω => by rw [him_eq]
  have hIre : Integrable (fun ω => Real.exp (r * (Real.sqrt (gridStep s t K n) *
      linTr n (AbCN (sz.withLam 0) s t K n j Φ U 0 ω) (Sizes.seqXmat (sz.withLam 0) n (ω (j + 1)))))) (pathP (sz.withLam 0)) := by
    have := hZ.1.integrable_exp_mul r
    simpa [Set.indicator_univ, stepZCN_re] using this
  have hIim : Integrable (fun ω => Real.exp (r * (Real.sqrt (gridStep s t K n) *
      linTr n ((-Complex.I) • AbCN (sz.withLam 0) s t K n j Φ U 0 ω) (Sizes.seqXmat (sz.withLam 0) n (ω (j + 1))))))
      (pathP (sz.withLam 0)) := by
    have := hZ.2.integrable_exp_mul r
    simpa [Set.indicator_univ, stepZCN_im] using this
  have hAm' : Measurable[filt (sz.withLam 0) j] (fun ω => (-Complex.I) • AbCN (sz.withLam 0) s t K n j Φ U 0 ω) :=
    hAm.const_smul (-Complex.I)
  have hce_re := difRepTail_condExp_exp hAm (gridStep s t K n) r hIre
  have hce_im := difRepTail_condExp_exp hAm' (gridStep s t K n) r hIim
  have hsq : (r * Real.sqrt (gridStep s t K n)) ^ 2 = r ^ 2 * gridStep s t K n := by
    rw [mul_pow, Real.sq_sqrt hΔ]
  refine ⟨by rw [hfre]; exact hIre, by rw [hfim]; exact hIim, ?_, ?_⟩
  · rw [hfre]
    refine hce_re.le.trans (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    refine Real.exp_le_exp.2 ?_
    rw [hsq]
    have hrr : 0 ≤ r ^ 2 * gridStep s t K n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (hvar ω).1 hrr]
  · rw [hfim]
    refine hce_im.le.trans (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    refine Real.exp_le_exp.2 ?_
    rw [hsq]
    have hrr : 0 ≤ r ^ 2 * gridStep s t K n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (hvar ω).2 hrr]

end CondMGF

/-! ## 7. The first-chaos and second-order parts of one step, for a generic Hermitian test family -/

section StepFields

variable {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)

private theorem TwistGridTail_measurable_pair (A : PathΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hA : Measurable[filt sz j] A) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => (A ω, ω (j + 1))) :=
  (hA.mono ((filt sz).mono (Nat.le_succ j)) le_rfl).prodMk (gridAsm_measurable_coord sz le_rfl)

variable {ι : Type} [Fintype ι]
  {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}

/-- `Z = stepZCN` is `filt sz (j+1)`-measurable. -/
private theorem TwistGridTail_measurable_stepZ (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ) (b : ι) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => stepZCN sz s t K n j Φ U b ω) := by
  have hAm := StepDecompN_measurable_AbCN sz s t K n j hΦ U b
  have hp := TwistGridTail_measurable_pair sz n j _ hAm
  have hre : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => stepZCN_re sz s t K n j Φ U b ω) := by
    have h0' := (difRepTail_measurable_linTr_uncurry (sz := sz) n).comp hp
    have h0 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz =>
        linTr n (AbCN sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1)))) := h0'
    exact h0.const_mul (Real.sqrt (gridStep s t K n))
  have hAm' : Measurable[filt sz j] (fun ω => (-Complex.I) • AbCN sz s t K n j Φ U b ω) := hAm.const_smul (-Complex.I)
  have hp' := TwistGridTail_measurable_pair sz n j _ hAm'
  have him : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => stepZCN_im sz s t K n j Φ U b ω) := by
    have h0' := (difRepTail_measurable_linTr_uncurry (sz := sz) n).comp hp'
    have h0 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz =>
        linTr n ((-Complex.I) • AbCN sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1)))) := h0'
    exact h0.const_mul (Real.sqrt (gridStep s t K n))
  have hre' : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ((stepZCN_re sz s t K n j Φ U b ω : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hre
  have him' : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ((stepZCN_im sz s t K n j Φ U b ω : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp him
  unfold stepZCN
  exact hre'.add (him'.const_mul _)

/-- `Y = stepYCN` is `filt sz (j+1)`-measurable, for measurable observables. -/
private theorem TwistGridTail_measurable_stepY (hΦ : ∀ a, HermTestFun sz n (Φ a)) (hΦm : ∀ a, Measurable (Φ a))
    (U : ι → ι → ℂ) (b : ι) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => stepYCN sz s t K n j Φ U b ω) := by
  have h1 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω)) :=
    Finset.measurable_sum _ fun a _ => ((hΦm a).comp (pathH_measurable_filt sz s t K n (j + 1))).const_mul _
  have h2 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz =>
      (pathP sz)[fun ω' => ∑ a, U b a * Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt sz).mono (Nat.le_succ j)) le_rfl
  unfold stepYCN stepXiCN
  exact (h1.sub h2).sub (TwistGridTail_measurable_stepZ sz s t K n j hΦ U b)

/-- **The `L²` data of `Re Y`, `Im Y`** for Doob's inequality: `L²`, conditionally centred, and `∫ (Re Y)² ≤ 768 C₂² Δ² N⁸`
(`stepDecompCN` (iii), (iv), `stepDecompCN_Y_sq`, `∫‖X_{j+1}‖⁴ ≤ 768 N⁸`). -/
private theorem TwistGridTail_Y_fields (hΦ : ∀ a, HermTestFun sz n (Φ a)) (hΦm : ∀ a, Measurable (Φ a)) {C₂ : ℝ}
    (hC₀ : 0 ≤ C₂)
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) (hU : ∑ a, ‖U b a‖ ≤ 1) :
    MemLp (fun ω => (stepYCN sz s t K n j Φ U b ω).re) 2 (pathP sz) ∧
    MemLp (fun ω => (stepYCN sz s t K n j Φ U b ω).im) 2 (pathP sz) ∧
    (pathP sz)[fun ω => (stepYCN sz s t K n j Φ U b ω).re | filt sz j] =ᵐ[pathP sz] 0 ∧
    (pathP sz)[fun ω => (stepYCN sz s t K n j Φ U b ω).im | filt sz j] =ᵐ[pathP sz] 0 ∧
    ∫ ω, ((stepYCN sz s t K n j Φ U b ω).re) ^ 2 ∂(pathP sz) ≤ 768 * C₂ ^ 2 * gridStep s t K n ^ 2 * (sz.size n : ℝ) ^ 8 ∧
    ∫ ω, ((stepYCN sz s t K n j Φ U b ω).im) ^ 2 ∂(pathP sz) ≤ 768 * C₂ ^ 2 * gridStep s t K n ^ 2 * (sz.size n : ℝ) ^ 8 := by
  have hIntRe := integrable_stepZCN_re_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b
  have hIntIm := integrable_stepZCN_im_of_hermTestFun sz s t K n j hΦ hC₂ hΔ U b
  obtain ⟨-, -, hbound, hmean⟩ := stepDecompCN sz s t K n j hΦ hC₂ hΔ U b hIntRe hIntIm
  set Y : PathΩ sz → ℂ := fun ω => stepYCN sz s t K n j Φ U b ω with hYdef
  have hYm : Measurable[filt sz (j + 1)] Y := TwistGridTail_measurable_stepY sz s t K n j hΦ hΦm U b
  have hYae : AEStronglyMeasurable Y (pathP sz) := (hYm.mono ((filt sz).le (j + 1)) le_rfl).aestronglyMeasurable
  set cc : ℝ := (∑ a, ‖U b a‖) * ((C₂ / 2) * gridStep s t K n) with hcc
  set g : PathΩ sz → ℝ := fun ω => cc * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 2 with hgdef
  have hg2int : Integrable (fun ω => g ω ^ 2) (pathP sz) := by
    have : (fun ω => g ω ^ 2) = fun ω => cc ^ 2 * ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 := by
      funext ω; simp only [hgdef]; ring
    rw [this]
    exact (integrable_normPow4_incr sz n j).const_mul _
  have hgm : AEStronglyMeasurable g (pathP sz) := by
    have : Measurable g := by
      have h1 : Measurable fun ω : PathΩ sz => Sizes.seqXmat sz n (ω (j + 1)) :=
        ((continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice sz n)).comp
          (measurable_pi_apply (j + 1))
      exact (h1.norm.pow_const 2).const_mul cc
    exact this.aestronglyMeasurable
  have hgL2 : MemLp g 2 (pathP sz) := (memLp_two_iff_integrable_sq hgm).2 hg2int
  have hhL2 : MemLp (fun ω => g ω + (pathP sz)[g | filt sz j] ω) 2 (pathP sz) :=
    hgL2.add (hgL2.condExp (m := filt sz j) (by norm_num))
  have hYL2 : MemLp Y 2 (pathP sz) := MemLp.mono' hhL2 hYae hbound
  have hReL2 : MemLp (fun ω => (Y ω).re) 2 (pathP sz) :=
    hYL2.of_le (Complex.continuous_re.comp_aestronglyMeasurable hYae)
      (Filter.Eventually.of_forall fun ω => by simpa using Complex.abs_re_le_norm (Y ω))
  have hImL2 : MemLp (fun ω => (Y ω).im) 2 (pathP sz) :=
    hYL2.of_le (Complex.continuous_im.comp_aestronglyMeasurable hYae)
      (Filter.Eventually.of_forall fun ω => by simpa using Complex.abs_im_le_norm (Y ω))
  have hYint : Integrable Y (pathP sz) := hYL2.integrable (by norm_num)
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt sz j) hYint
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt sz j) hYint
  have hmean' : (pathP sz)[Y | filt sz j] =ᵐ[pathP sz] fun _ => (0 : ℂ) := hmean
  have hmRe : (pathP sz)[fun ω => (Y ω).re | filt sz j] =ᵐ[pathP sz] 0 := by
    have h1 : (fun ω => ((pathP sz)[Y | filt sz j] ω).re) =ᵐ[pathP sz]
        (pathP sz)[fun ω => (Y ω).re | filt sz j] := hRe
    filter_upwards [h1, hmean'] with ω h1 h2
    rw [← h1, h2]
    simp
  have hmIm : (pathP sz)[fun ω => (Y ω).im | filt sz j] =ᵐ[pathP sz] 0 := by
    have h1 : (fun ω => ((pathP sz)[Y | filt sz j] ω).im) =ᵐ[pathP sz]
        (pathP sz)[fun ω => (Y ω).im | filt sz j] := hIm
    filter_upwards [h1, hmean'] with ω h1 h2
    rw [← h1, h2]
    simp
  have hYsq := stepDecompCN_Y_sq sz s t K n j hΦ hC₂ hΔ U b
  have h4 := integral_normPow4_incr_le sz n j
  have hint2 : Integrable (fun ω => ‖Y ω‖ ^ 2) (pathP sz) := hYL2.norm.integrable_sq
  have hq : ∫ ω, ‖Y ω‖ ^ 2 ∂(pathP sz) ≤ 768 * C₂ ^ 2 * gridStep s t K n ^ 2 * (sz.size n : ℝ) ^ 8 := by
    refine hYsq.trans ?_
    set S := ∑ a, ‖U b a‖
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => norm_nonneg _
    have h1 : 4 * (S * (C₂ / 2)) ^ 2 * gridStep s t K n ^ 2 ≤ 4 * (C₂ / 2) ^ 2 * gridStep s t K n ^ 2 := by
      have : (S * (C₂ / 2)) ^ 2 ≤ (C₂ / 2) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hU (by positivity : 0 ≤ C₂ / 2)
        nlinarith [mul_nonneg hS0 (by positivity : 0 ≤ C₂ / 2)]
      nlinarith [sq_nonneg (gridStep s t K n)]
    calc 4 * (S * (C₂ / 2)) ^ 2 * gridStep s t K n ^ 2 * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz)
        ≤ 4 * (C₂ / 2) ^ 2 * gridStep s t K n ^ 2 * (768 * (sz.size n : ℝ) ^ 8) :=
          mul_le_mul h1 h4 (integral_nonneg fun ω => by positivity) (by positivity)
      _ = 768 * C₂ ^ 2 * gridStep s t K n ^ 2 * (sz.size n : ℝ) ^ 8 := by ring
  refine ⟨hReL2, hImL2, hmRe, hmIm, ?_, ?_⟩
  · refine (integral_mono hReL2.integrable_sq hint2 fun ω => ?_).trans hq
    simp only
    have := Complex.abs_re_le_norm (Y ω)
    nlinarith [abs_nonneg (Y ω).re, sq_abs (Y ω).re]
  · refine (integral_mono hImL2.integrable_sq hint2 fun ω => ?_).trans hq
    simp only
    have := Complex.abs_im_le_norm (Y ω)
    nlinarith [abs_nonneg (Y ω).im, sq_abs (Y ω).im]

end StepFields

end RBM.BA
