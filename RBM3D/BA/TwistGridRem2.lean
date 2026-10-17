/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGridRem
import RBM3D.BA.TwistGrid2
import RBM3D.Path.LoopStep

/-!
# BA stage TL, row TL2a2 (T2437), path level: the grid remainder bound `‖twRem‖ ≤ N^{C₀} √Δ`

Ticket `docs/tickets/T2437.md` (clause (ii) of `docs/tickets/T2428-amend-1.md` item 3); the matrix
level is `RBM3D/BA/TwistGridRem.lean` (the twisted one-step envelope and the Taylor bound of `K̃`).
Paper arXiv:2507.20274, `docs/tickets/T2398-TL-proofs.md` (D.5).  Twin of `Path/DifREP1.lean` §3-§4
(`gridRepRemN_holds`, `:1159`).

* §1 the grid arithmetic and the flow bounds on `[0, t_n]` (`1 - v ≥ N⁻¹/2`, `η_v⁻¹ ≤ (2/κ) N`);
* §2 the freeze `TwistGridRem2_condExp_step`: the conditional mean of `A_{j+1}` given `F_j` is the
  Gaussian integral of the one-step law of the coupling `0` (`condExp_freeze`,
  `Sizes.seqP_map_slice`, `pathH_succ`; the observable of the Hermitian part `½ (A + Aᴴ)`);
* §3 the per-step bound `‖r_j‖ ≤ Z₁ Δ^{3/2} + Z₂ Δ²` from `TwistGridRem_step`, and the summation
  arithmetic (the twin of `difRep_rem_arith`);
* §4 the target `baTwistGridRem_holds`: `C₀ = 11`, `CK = 6`, every `d`;
* §5 the compiled nonempty instances at `d = 3`, `sz0`, `flow_sz0`.

Every statement is for every `d` (no `3 ≤ d`).  Every helper is `private` or prefixed
`TwistGridRem2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private LoopStep_condExp_freezeC LoopStep_measurable_pathH_filt LoopStep_herm LoopStep_herm_isHermitian
  LoopStep_herm_of_isHermitian LoopStep_continuous_herm from RBM3D.Path.LoopStep

open MeasureTheory Filter
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Grid arithmetic and the flow bounds -/

section Grid

private theorem TwistGridRem2_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem TwistGridRem2_gridTime_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j ≤ t n := by
  have hΔ := TwistGridRem2_gridStep_nonneg (s := s) (t := t) (K := K) hst
  have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' hΔ
  have hlast := gridTime_last s t K n hK0
  unfold gridTime at hlast ⊢
  nlinarith

private theorem TwistGridRem2_gridTime_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ := TwistGridRem2_gridStep_nonneg (s := s) (t := t) (K := K) hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

private theorem TwistGridRem2_gridTime_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
  unfold gridTime
  push_cast
  ring

private theorem TwistGridRem2_K_mul_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s t K n = t n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  field_simp

end Grid

section Flow

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- `1 - v ≥ N⁻¹ / 2` for `v ≤ t₀_n` on the flow (`1 - t₀ ≥ Im z / 2` and `Im z ≥ N^{-1+ε} ≥ N⁻¹`). -/
private theorem TwistGridRem2_one_sub_ge (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ}
    (hvT : v ≤ BAflowT0 sz z n) : ((sz.size n : ℕ) : ℝ)⁻¹ / 2 ≤ 1 - v := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have hNim' : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hT := EMn2BA_one_sub_T0 hκ sz hflow n
  rw [Real.rpow_neg_one] at hNim'
  linarith

/-- `η_v⁻¹ ≤ (2/κ) N` for `v ≤ t₀_n` (`η_v = (1 - v) Im m_F`, `Im m_F ≥ κ`; the shape of `TwistKer2_eta_inv_le`). -/
private theorem TwistGridRem2_eta_inv_le (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ}
    (hvT : v ≤ BAflowT0 sz z n) :
    (etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v)⁻¹ ≤ (2 / κ) * ((sz.size n : ℕ) : ℝ) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1v := TwistGridRem2_one_sub_ge hκ hε hflow n hvT
  have hm := EMn2BA_mF_data sz hflow n
  have hpos : 0 < ((sz.size n : ℕ) : ℝ)⁻¹ / 2 := by positivity
  have hη : κ * (((sz.size n : ℕ) : ℝ)⁻¹ / 2) ≤ etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v := by
    rw [etaOf]
    have := mul_le_mul h1v hm.1 hκ.le (by linarith)
    linarith
  have hκN : 0 < κ * (((sz.size n : ℕ) : ℝ)⁻¹ / 2) := by positivity
  calc (etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v)⁻¹ ≤ (κ * (((sz.size n : ℕ) : ℝ)⁻¹ / 2))⁻¹ :=
        inv_anti₀ hκN hη
    _ = (2 / κ) * ((sz.size n : ℕ) : ℝ) := by field_simp

end Flow

/-! ## 2. The freeze: the conditional mean of `A_{j+1}` given `F_j` -/

section Freeze

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- A private copy of the (private) `StandardBorelSpace` instance of `Path/LoopStep.lean:189`. -/
private instance TwistGridRem2_sbs :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

/-- `pathH` of the walk of `sz.withLam 0`, read at the sizes of `sz` (`(sz.withLam 0).L = sz.L`, `.W = sz.W`). -/
private def TwistGridRem2_pathH (k : ℕ) (ω : PathΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  pathH (sz.withLam 0) s t K n k ω

/-- The increment `X_{k+1}` of the walk of `sz.withLam 0`, read at the sizes of `sz`. -/
private def TwistGridRem2_X (x : Sizes.SeqΩ (sz.withLam 0)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Sizes.seqXmat (sz.withLam 0) n x

private theorem TwistGridRem2_Hpath_eq (k : ℕ) (ω : PathΩ sz) :
    (baStep2Mat sz lam0 E).Hpath s t K n k ω = (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + TwistGridRem2_pathH sz s t K n k ω := rfl

/-- The grid state `H_k = g₀ Ψ + pathH` is Hermitian. -/
private theorem TwistGridRem2_Hpath_herm (k : ℕ) (ω : PathΩ sz) :
    ((baStep2Mat sz lam0 E).Hpath s t K n k ω).IsHermitian := by
  rw [TwistGridRem2_Hpath_eq, add_comm]
  exact OneStep_isHermitian_add_realSmul (pathH_isHermitian (sz.withLam 0) s t K n k ω) (PsiI_isHermitian d _ _) (lam0 n)

private theorem TwistGridRem2_X_herm (x : Sizes.SeqΩ (sz.withLam 0)) : (TwistGridRem2_X sz n x).IsHermitian :=
  Sizes.seqXmat_isHermitian (sz.withLam 0) n x

/-- The one-step recursion `H_{k+1} = H_k + √Δ X_{k+1}` of the grid state (`pathH_succ`). -/
private theorem TwistGridRem2_Hpath_succ (k : ℕ) (ω : PathΩ sz) :
    (baStep2Mat sz lam0 E).Hpath s t K n (k + 1) ω = (baStep2Mat sz lam0 E).Hpath s t K n k ω +
      (Real.sqrt (gridStep s t K n) : ℂ) • TwistGridRem2_X sz n (ω (k + 1)) := by
  rw [TwistGridRem2_Hpath_eq, TwistGridRem2_Hpath_eq]
  have h : TwistGridRem2_pathH sz s t K n (k + 1) ω = TwistGridRem2_pathH sz s t K n k ω +
      (Real.sqrt (gridStep s t K n) : ℂ) • TwistGridRem2_X sz n (ω (k + 1)) := pathH_succ (sz.withLam 0) s t K n k ω
  rw [h, add_assoc]

/-- **The freeze** (the twin of `condExp_loop_step`, `Path/LoopStep.lean:206`, for `A_{j+1} = L̃_{u_{j+1}}(H_{j+1}) - K̃_{u_{j+1}}`): the conditional mean of
`A_{j+1}(a)` given `F_j` is the Gaussian integral over the one-step law of the coupling `0` (`PF d L W 0`) of the same observable at `H_j + √Δ X`.  Needs `u_{j+1} < 1`
and `0 < Im m_F`. -/
theorem TwistGridRem2_condExp_step (hm : 0 < (BAmF sz lam0 E n).im) (j : ℕ) (hu1 : gridTime s t K n (j + 1) < 1)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    ((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j]
      =ᵐ[(baStep2Mat sz lam0 E).Pp] fun ω => ∫ y : Ω d (sz.L n) (sz.W n),
        (twL2M sz lam0 E n (gridTime s t K n (j + 1))
          ((baStep2Mat sz lam0 E).Hpath s t K n j ω + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y) σ a c₁ c₂ -
          twK (baFM sz lam0 E) n (gridTime s t K n (j + 1)) σ a c₁ c₂) ∂(PF d (sz.L n) (sz.W n) 0) := by
  classical
  have hprob : IsProbabilityMeasure ((baStep2Mat sz lam0 E).Pp) := isProbabilityMeasure_pathP (sz.withLam 0)
  set u : ℝ := gridTime s t K n (j + 1) with hu
  set Δ : ℝ := gridStep s t K n with hΔ
  set Kt : ℂ := twK (baFM sz lam0 E) n u σ a c₁ c₂ with hKt
  have hz : (ztOf (BAmF sz lam0 E n) (E n) u).im ≠ 0 := by
    rw [ztOf_im]
    exact (TwistGridRem_eta_pos hm hu1).ne'
  have hη : 0 < |(ztOf (BAmF sz lam0 E n) (E n) u).im| := abs_pos.mpr hz
  -- the observable of the Hermitian part: continuous and bounded everywhere
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ := fun A =>
    TwistGridRem_F (TwistGridRem_letters d (sz.L n) (sz.W n) a c₁ c₂) (TwistGridRem_word σ)
      (blockMat d (sz.L n) (sz.W n) (LoopStep_herm A)) (ztOf (BAmF sz lam0 E n) (E n) u) with hΦ
  have hΦcont : Continuous Φ :=
    TwistGridRem_continuous_F (f := fun A => blockMat d (sz.L n) (sz.W n) (LoopStep_herm A))
      ((LoopStep_continuous_herm (d := d) (L := sz.L n) (W := sz.W n)).matrix_submatrix _ _)
      (fun A => (LoopStep_herm_isHermitian A).submatrix _) hz
  have hΦbd : ∀ A, ‖Φ A‖ ≤ (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) *
      (|(ztOf (BAmF sz lam0 E n) (E n) u).im|⁻¹) ^ (TwistGridRem_word σ).length :=
    fun A => TwistGridRem_norm_F_le (TwistGridRem_letters_norm sz n a c₁ c₂)
      ((LoopStep_herm_isHermitian A).submatrix _) hη le_rfl
  have hΦeq : ∀ A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, A.IsHermitian →
      Φ A = twL2M sz lam0 E n u A σ a c₁ c₂ := fun A hA => by
    rw [TwistGridRem_twL2M_eq sz lam0 E n hA u σ a c₁ c₂]
    simp only [hΦ, LoopStep_herm_of_isHermitian hA]
  -- the frozen function
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ (sz.withLam 0) → ℂ :=
    fun p x => Φ (p + (Real.sqrt Δ : ℂ) • TwistGridRem2_X sz n x) - Kt with hF
  have hXmeas : Measurable (TwistGridRem2_X sz n) :=
    (continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice (sz.withLam 0) n)
  have hFmeas : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ (sz.withLam 0) =>
      F p.1 p.2) := by
    have h2 : Measurable fun x : Sizes.SeqΩ (sz.withLam 0) => (Real.sqrt Δ : ℂ) • TwistGridRem2_X sz n x :=
      hXmeas.const_smul (Real.sqrt Δ : ℂ)
    have h3 : Measurable fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ (sz.withLam 0) =>
        p.1 + (Real.sqrt Δ : ℂ) • TwistGridRem2_X sz n p.2 :=
      measurable_fst.add (h2.comp measurable_snd)
    exact (hΦcont.measurable.comp h3).sub measurable_const
  have hFbdd : ∀ p x, ‖F p x‖ ≤ (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) *
      (|(ztOf (BAmF sz lam0 E n) (E n) u).im|⁻¹) ^ (TwistGridRem_word σ).length + ‖Kt‖ :=
    fun p x => (norm_sub_le _ _).trans (add_le_add (hΦbd _) le_rfl)
  have hY : Measurable[filt (sz.withLam 0) j] (fun ω : PathΩ sz => (baStep2Mat sz lam0 E).Hpath s t K n j ω) := by
    change Measurable[filt (sz.withLam 0) j] (fun ω : PathΩ sz =>
      (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + TwistGridRem2_pathH sz s t K n j ω)
    exact (LoopStep_measurable_pathH_filt (sz.withLam 0) s t K n j).const_add _
  have hYm : Measurable (fun ω : PathΩ sz => (baStep2Mat sz lam0 E).Hpath s t K n j ω) :=
    hY.mono ((filt (sz.withLam 0)).le j) le_rfl
  have hFInt : ∀ p, Integrable (F p) (Sizes.seqP (sz.withLam 0)) := by
    intro p
    have hpair : Measurable (fun x : Sizes.SeqΩ (sz.withLam 0) => (p, x)) :=
      measurable_const.prodMk measurable_id
    have hm' : Measurable (fun x : Sizes.SeqΩ (sz.withLam 0) => F p x) := by
      have h := hFmeas.comp hpair
      exact h
    exact (memLp_top_of_bound hm'.aestronglyMeasurable _
      (Eventually.of_forall fun x => hFbdd p x)).integrable le_top
  have hIntTarget : Integrable (fun ω : PathΩ sz => F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) (ω (j + 1)))
      ((baStep2Mat sz lam0 E).Pp) := by
    have hm' : Measurable (fun ω : PathΩ sz => F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) (ω (j + 1))) := by
      have h := hFmeas.comp (hYm.prodMk (measurable_pi_apply (j + 1)))
      exact h
    exact (memLp_top_of_bound hm'.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hEq : (fun ω' : PathΩ sz => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a) =
      fun ω => F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) (ω (j + 1)) := by
    funext ω
    have hp := TwistGridRem2_Hpath_herm sz lam0 E s t K n j ω
    have hh := OneStep_isHermitian_add_realSmul hp (TwistGridRem2_X_herm sz n (ω (j + 1))) (Real.sqrt Δ)
    change twL2M sz lam0 E n u ((baStep2Mat sz lam0 E).Hpath s t K n (j + 1) ω) σ a c₁ c₂ - Kt =
      Φ ((baStep2Mat sz lam0 E).Hpath s t K n j ω + (Real.sqrt Δ : ℂ) • TwistGridRem2_X sz n (ω (j + 1))) - Kt
    rw [TwistGridRem2_Hpath_succ, hΦeq _ hh]
  have h1 := LoopStep_condExp_freezeC (sz := sz.withLam 0) j hY hFmeas hFInt hIntTarget
  have h2 : ((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j]
      =ᵐ[(baStep2Mat sz lam0 E).Pp]
      ((baStep2Mat sz lam0 E).Pp)[fun ω => F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) (ω (j + 1)) | filt (sz.withLam 0) j] :=
    condExp_congr_ae (Eventually.of_forall fun ω => congrFun hEq ω)
  filter_upwards [h2, h1] with ω hω2 hω1
  refine hω2.trans (hω1.trans ?_)
  have hp := TwistGridRem2_Hpath_herm sz lam0 E s t K n j ω
  set f : Ω d (sz.L n) (sz.W n) → ℂ := fun y =>
    twL2M sz lam0 E n u ((baStep2Mat sz lam0 E).Hpath s t K n j ω + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) y) σ a c₁ c₂ - Kt
    with hfdef
  have hfeq : f = fun y => Φ ((baStep2Mat sz lam0 E).Hpath s t K n j ω + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) y) - Kt := by
    funext y
    have hh := OneStep_isHermitian_add_realSmul hp (Xmat_isHermitian d (sz.L n) (sz.W n) y) (Real.sqrt Δ)
    simp only [hfdef, hΦeq _ hh]
  have hfcont : Continuous f := by
    rw [hfeq]
    have h2 : Continuous fun y : Ω d (sz.L n) (sz.W n) => (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) y :=
      (continuous_Xmat d (sz.L n) (sz.W n)).const_smul (Real.sqrt Δ : ℂ)
    exact (hΦcont.comp (continuous_const.add h2)).sub continuous_const
  have hFf : ∀ x, F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) x = f (Sizes.slice (sz.withLam 0) n x) := by
    intro x
    have hh := OneStep_isHermitian_add_realSmul hp (TwistGridRem2_X_herm sz n x) (Real.sqrt Δ)
    simp only [hF, hfdef]
    rw [hΦeq _ hh]
    rfl
  calc ∫ x, F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) x ∂(Sizes.seqP (sz.withLam 0))
      = ∫ x, f (Sizes.slice (sz.withLam 0) n x) ∂(Sizes.seqP (sz.withLam 0)) := by simp only [hFf]
    _ = ∫ y, f y ∂((Sizes.seqP (sz.withLam 0)).map (Sizes.slice (sz.withLam 0) n)) :=
        (integral_map (Sizes.measurable_slice (sz.withLam 0) n).aemeasurable hfcont.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(PF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n)) := by
        rw [Sizes.seqP_map_slice]
        rfl

end Freeze

/-! ## 3. The per-step bound and the summation -/

section Step

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- **One grid step of the remainder** (`difRep_step_le`, `Path/DifREP1.lean:964`, for the twisted observable): `r_j = 𝔼[A_{j+1}|F_j] - A_j - Δ Drift_j` has
`‖r_j‖ ≤ 10⁴ N⁴ (1 + η_{u_{j+1}}⁻¹)⁶ Δ^{3/2} + (1 - u_{j+1})^{-3} Δ²` almost surely: the freeze (`TwistGridRem2_condExp_step`) and the one-step bound
`TwistGridRem_step` at the Hermitian matrix `H_j`, with `Drift = twDriftM` (`BATwistHier_holds`, inside `TwistGridRem_step`). -/
theorem TwistGridRem2_step_le {κ : ℝ} (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hg : 0 < lam0 n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (j : ℕ) (hu1 : gridTime s t K n (j + 1) < 1) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    ∀ᵐ ω ∂((baStep2Mat sz lam0 E).Pp),
      ‖((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω -
          twAk sz lam0 E s t K n σ c₁ c₂ j ω a - ((gridStep s t K n : ℝ) : ℂ) * twDriftk sz lam0 E s t K n σ a c₁ c₂ j ω‖ ≤
        10000 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (etaOf (BAmF sz lam0 E n) (gridTime s t K n (j + 1)))⁻¹) ^ 6 * gridStep s t K n ^ ((3 : ℝ) / 2) +
          ((1 - gridTime s t K n (j + 1))⁻¹) ^ 3 * gridStep s t K n ^ 2 := by
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hΔ : 0 ≤ gridStep s t K n := TwistGridRem2_gridStep_nonneg (K := K) hst
  have hu : 0 ≤ gridTime s t K n j := TwistGridRem2_gridTime_nonneg (K := K) hs0 hst j
  have hsucc := TwistGridRem2_gridTime_succ s t K n j
  filter_upwards [TwistGridRem2_condExp_step sz lam0 E s t K n hm j hu1 σ a c₁ c₂] with ω hω
  rw [hω]
  have hMh := TwistGridRem2_Hpath_herm sz lam0 E s t K n j ω
  have hstep := TwistGridRem_step sz lam0 E n hκ hr hg σ a c₁ c₂ hu hΔ (hsucc ▸ hu1) hMh
  rw [← hsucc] at hstep
  exact hstep

/-- `(1 - v)⁻¹ ≤ 2 N` for `v ≤ t₀_n` on the flow. -/
private theorem TwistGridRem2_one_sub_inv_le {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ} (hvT : v ≤ BAflowT0 sz z n) : (1 - v)⁻¹ ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1v := TwistGridRem2_one_sub_ge hκ hε hflow n hvT
  have hpos : 0 < ((sz.size n : ℕ) : ℝ)⁻¹ / 2 := by positivity
  calc (1 - v)⁻¹ ≤ (((sz.size n : ℕ) : ℝ)⁻¹ / 2)⁻¹ := inv_anti₀ hpos h1v
    _ = 2 * ((sz.size n : ℕ) : ℝ) := by field_simp

private theorem TwistGridRem2_rpow_three_halves {Δ : ℝ} (hΔ : 0 ≤ Δ) : Δ ^ ((3 : ℝ) / 2) = Δ * Real.sqrt Δ := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hΔ (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]

/-- **The summation arithmetic of the remainder** (the twin of `difRep_rem_arith`, `Path/DifREP1.lean:1089`, with `Z₁ = c₁ N^{10}`, `Z₂ = 8 N³`):
for `k ≤ K`, `K Δ ≤ 1`, `Δ N⁶ ≤ 1` and `N ≥ c₁ + 8`: `k (c₁ N^{10} Δ^{3/2} + 8 N³ Δ²) ≤ N^{11} √Δ`. -/
private theorem TwistGridRem2_rem_arith (c₁ N Δ : ℝ) (K k : ℕ) (hk : k ≤ K) (hN1 : 1 ≤ N) (hc₁ : 0 ≤ c₁) (hΔ0 : 0 ≤ Δ)
    (hKΔ : (K : ℝ) * Δ ≤ 1) (hΔN : Δ * N ^ 6 ≤ 1) (hN : c₁ + 8 ≤ N) :
    (k : ℝ) * (c₁ * N ^ 10 * Δ ^ ((3 : ℝ) / 2) + 8 * N ^ 3 * Δ ^ 2) ≤ N ^ 11 * Real.sqrt Δ := by
  set r := Real.sqrt Δ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = Δ := Real.mul_self_sqrt hΔ0
  have hN0 : 0 < N := by linarith
  -- `r N³ ≤ 1`
  have hrN : r * N ^ 3 ≤ 1 := by
    have h1 : (r * N ^ 3) ^ 2 ≤ 1 := by
      have e : (r * N ^ 3) ^ 2 = Δ * N ^ 6 := by
        rw [mul_pow, sq r, hrr, ← pow_mul]
      rw [e]
      exact hΔN
    exact (pow_le_one_iff_of_nonneg (by positivity) (by norm_num)).1 h1
  have hN10 : 1 ≤ N ^ 10 := one_le_pow₀ hN1
  -- `c₁ N^{10} + 8 r ≤ N^{11}` is not needed: bound `c₁ N^{10} + 8 ≤ N^{11}`
  have hbig : c₁ * N ^ 10 + 8 ≤ N ^ 11 := by
    calc c₁ * N ^ 10 + 8 ≤ c₁ * N ^ 10 + 8 * N ^ 10 := by nlinarith
      _ = (c₁ + 8) * N ^ 10 := by ring
      _ ≤ N * N ^ 10 := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = N ^ 11 := by ring
  have hΔ32 := TwistGridRem2_rpow_three_halves hΔ0
  rw [hΔ32]
  have hbr : 0 ≤ c₁ * N ^ 10 * (Δ * r) + 8 * N ^ 3 * Δ ^ 2 := by positivity
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
  have h8 : 8 * N ^ 3 * Δ ≤ 8 * r := by
    calc 8 * N ^ 3 * Δ = 8 * (r * N ^ 3) * r := by rw [← hrr]; ring
      _ ≤ 8 * 1 * r := by gcongr
      _ = 8 * r := by ring
  calc (k : ℝ) * (c₁ * N ^ 10 * (Δ * r) + 8 * N ^ 3 * Δ ^ 2)
      ≤ (K : ℝ) * (c₁ * N ^ 10 * (Δ * r) + 8 * N ^ 3 * Δ ^ 2) := mul_le_mul_of_nonneg_right hkK hbr
    _ = ((K : ℝ) * Δ) * (c₁ * N ^ 10 * r + 8 * N ^ 3 * Δ) := by ring
    _ ≤ 1 * (c₁ * N ^ 10 * r + 8 * N ^ 3 * Δ) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
    _ ≤ c₁ * N ^ 10 * r + 8 * r := by linarith
    _ ≤ N ^ 11 * r := by nlinarith

end Step

/-! ## 4. The target: `baTwistGridRem_holds` -/

section Target

/-- The per-step constants on the flow: with `q = η_v⁻¹ ≤ (2/κ) N` and `(1 - v)⁻¹ ≤ 2N` (`N ≥ 1`),
`10⁴ N⁴ (1 + q)⁶ Δ^{3/2} + (1 - v)^{-3} Δ² ≤ c₁ N^{10} Δ^{3/2} + 8 N³ Δ²`, `c₁ = 10⁴ (1 + 2/κ)⁶`. -/
private theorem TwistGridRem2_consts_le {κ N q h Δ : ℝ} (hκ : 0 < κ) (hN1 : 1 ≤ N) (hq0 : 0 ≤ q) (hq : q ≤ (2 / κ) * N) (hh0 : 0 ≤ h)
    (hh : h ≤ 2 * N) (hΔ : 0 ≤ Δ) :
    10000 * N ^ 4 * (1 + q) ^ 6 * Δ ^ ((3 : ℝ) / 2) + h ^ 3 * Δ ^ 2 ≤
      10000 * (1 + 2 / κ) ^ 6 * N ^ 10 * Δ ^ ((3 : ℝ) / 2) + 8 * N ^ 3 * Δ ^ 2 := by
  have hN0 : 0 < N := by linarith
  have h2κ : 0 ≤ 2 / κ := by positivity
  have h1q : 1 + q ≤ (1 + 2 / κ) * N := by nlinarith
  have hq6 : (1 + q) ^ 6 ≤ ((1 + 2 / κ) * N) ^ 6 := pow_le_pow_left₀ (by linarith) h1q 6
  have hr32 : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ _
  have hA : 10000 * N ^ 4 * (1 + q) ^ 6 * Δ ^ ((3 : ℝ) / 2) ≤
      10000 * (1 + 2 / κ) ^ 6 * N ^ 10 * Δ ^ ((3 : ℝ) / 2) := by
    have : 10000 * N ^ 4 * (1 + q) ^ 6 ≤ 10000 * N ^ 4 * ((1 + 2 / κ) * N) ^ 6 :=
      mul_le_mul_of_nonneg_left hq6 (by positivity)
    calc 10000 * N ^ 4 * (1 + q) ^ 6 * Δ ^ ((3 : ℝ) / 2) ≤ 10000 * N ^ 4 * ((1 + 2 / κ) * N) ^ 6 * Δ ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right this hr32
      _ = _ := by ring
  have hB : h ^ 3 * Δ ^ 2 ≤ 8 * N ^ 3 * Δ ^ 2 := by
    have : h ^ 3 ≤ (2 * N) ^ 3 := pow_le_pow_left₀ hh0 hh 3
    calc h ^ 3 * Δ ^ 2 ≤ (2 * N) ^ 3 * Δ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg Δ)
      _ = 8 * N ^ 3 * Δ ^ 2 := by ring
  linarith

/-- **Clause (ii) of 4 (b), the grid remainder** (the twisted twin of `gridRepRemN_holds`, `Path/DifREP1.lean:1159`): `C₀ = 11`, `CK = 6`, every `d`.
Clause (i) is `baTwistGrid_decomp_ae`; clause (ii) is the per-step bound `‖r_j‖ ≤ Z₁ Δ^{3/2} + Z₂ Δ²` (`TwistGridRem2_step_le`), `Z₁ = c₁ N^{10}`,
`c₁ = 10⁴ (1 + 2/κ)⁶`, `Z₂ = 8 N³`, summed over `j < k ≤ K` (`K Δ = t - s ≤ 1`, `Δ ≤ N^{-6}`, `N ≥ c₁ + 8`). -/
theorem baTwistGridRem_holds (d : ℕ) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridRem d C₀ := by
  refine ⟨11, by norm_num, ?_⟩
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  refine ⟨6, by norm_num, ?_⟩
  intro K hK0 hKN
  refine ⟨fun n i => baTwistGrid_decomp_ae sz _ _ s t K n i, ?_⟩
  have hT1 : ∀ n, BAflowT0 sz z n < 1 := fun n => EMn2BA_T0_lt_one hκ sz hz n
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hT1 n)
  have hsize : sz.SizeTendsto := hz.1.2.2.1
  have hwin := BAflow_lam0_window κ ε 𝔠 𝔡 sz z hz
  have hbig := hsize.eventually_ge_atTop (max 1 (10000 * (1 + 2 / κ) ^ 6 + 8))
  filter_upwards [hwin, hbig, hKN] with n hwn hbign hKNn
  intro i
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hz n
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNc : 10000 * (1 + 2 / κ) ^ 6 + 8 ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hbign
  have hc₁ : 0 ≤ 10000 * (1 + 2 / κ) ^ 6 := by positivity
  have hΔ0 : 0 ≤ gridStep s t K n := TwistGridRem2_gridStep_nonneg (K := K) (hst n)
  have hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1 := by
    rw [TwistGridRem2_K_mul_step s t K n (hK0 n)]
    linarith [hs n, ht1 n]
  have hKNn' : ((sz.size n : ℕ) : ℝ) ^ 6 ≤ K n := by
    have := hKNn
    rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hΔN : gridStep s t K n * ((sz.size n : ℕ) : ℝ) ^ 6 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hKNn' hΔ0).trans (by rw [mul_comm]; exact hKΔ)
  have hstep : ∀ j : ℕ, ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), j < K n →
      ‖((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp)[fun ω' => twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2
            (j + 1) ω' i.2.1 | filt (sz.withLam 0) j] ω -
          twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 j ω i.2.1 -
          ((gridStep s t K n : ℝ) : ℂ) * twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω‖ ≤
        10000 * (1 + 2 / κ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 10 * gridStep s t K n ^ ((3 : ℝ) / 2) +
          8 * ((sz.size n : ℕ) : ℝ) ^ 3 * gridStep s t K n ^ 2 := by
    intro j
    by_cases hj : j < K n
    · have hv : gridTime s t K n (j + 1) ≤ BAflowT0 sz z n :=
        (TwistGridRem2_gridTime_le (hst n) (hK0 n) (show j + 1 ≤ K n by omega)).trans (htT n)
      have hu1 : gridTime s t K n (j + 1) < 1 := lt_of_le_of_lt hv (hT1 n)
      have hq := TwistGridRem2_eta_inv_le hκ hε hz n hv
      have hh := TwistGridRem2_one_sub_inv_le hκ hε hz n hv
      have hq0 : 0 ≤ (etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (gridTime s t K n (j + 1)))⁻¹ :=
        inv_nonneg.2 (TwistGridRem_eta_pos (lt_of_lt_of_le hκ hr.2) hu1).le
      have hh0 : 0 ≤ (1 - gridTime s t K n (j + 1))⁻¹ := inv_nonneg.2 (by linarith)
      filter_upwards [TwistGridRem2_step_le sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n hκ hr hwn.1 (hs n) (hst n) j hu1
        i.1 i.2.1 i.2.2.1 i.2.2.2] with ω hω _
      exact hω.trans (TwistGridRem2_consts_le hκ hN1 hq0 hq hh0 hh hΔ0)
    · exact Eventually.of_forall fun ω h => absurd h hj
  filter_upwards [ae_all_iff.2 hstep] with ω hω k hk
  have hcast : ((sz.size n : ℕ) : ℝ) ^ (11 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 11 := by
    rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hcast]
  calc ‖twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖
      ≤ ∑ j ∈ Finset.range k, (10000 * (1 + 2 / κ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 10 * gridStep s t K n ^ ((3 : ℝ) / 2) +
          8 * ((sz.size n : ℕ) : ℝ) ^ 3 * gridStep s t K n ^ 2) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hω j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk))
    _ = (k : ℝ) * (10000 * (1 + 2 / κ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 10 * gridStep s t K n ^ ((3 : ℝ) / 2) +
          8 * ((sz.size n : ℕ) : ℝ) ^ 3 * gridStep s t K n ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ 11 * Real.sqrt (gridStep s t K n) :=
        TwistGridRem2_rem_arith _ _ _ (K n) k hk hN1 hc₁ hΔ0 hKΔ hΔN hNc

end Target

/-! ## 5. Compiled nonempty instances (`d = 3`, `sz0`: `L = 4`, `W = 32`, `lam = 1/64`; flow `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `z = zSeq`;
the window `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` by `t0_sz0`; the grid `K_n = ⌈N_n^{CK}⌉ + 1`, `N_n = (W_n L_n)^3`).  Every deterministic hypothesis is discharged; no external hypothesis occurs in
`baTwistGridRem_holds`; the two part pins `BATwistGridTail 3`, `BATwistGridWTail 3` of the assembly stay hypotheses (T2438, T2439). -/

end RBM.BA
