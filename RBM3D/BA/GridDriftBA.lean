/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.BA.Step2IterBA
import RBM3D.BA.KInduct
import RBM3D.BA.KTreeRep
import RBM3D.BA.TwistGridRem2
import RBM3D.BA.TwistGridWTail
import RBM3D.BA.EKPins
import RBM3D.BA.EMn2BA
import RBM3D.BA.SEforLnBA

/-!
# The block Anderson instances of the carrier classes of the step-2 drift

The BA instances of the classes of `Chain/StepDecompGen.lean` and `Chain/HierDriftGen.lean` at
`baStep2Mat sz lam0 E` (`BA/Step2BA.lean`), and their readings along the flow.

* §1 the walk `baStep2Mat_walkForm`, `Im m ≤ 1`, the variance law, the probability law, `HierDriftGen_KLink`, `HierDriftGen_KLoop`.
* §2 `HierDriftGen_KTwo`.
* §3 `HierDriftGen_UStep`.
* §4 `HierDriftGen_Expand`.
* §5 the classes along the flow `baHierDrift_classes`.

`HierDriftGen_KLoop` and `HierDriftGen_KTwo` at BA need `0 < BAflowLam0 sz z n`, which holds only eventually
(`BAflow_lam0_window`); `HierDriftGen_Expand`, `HierDriftGen_KLink`, `HierDriftGen_UStep`, `StepDecompGen_WalkForm` hold at every `n`.
Every helper is `private` or prefixed GridDriftBA_.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private LoopStep_condExp_freezeC LoopStep_measurable_pathH_filt LoopStep_herm LoopStep_herm_isHermitian
  LoopStep_herm_of_isHermitian LoopStep_continuous_herm from RBM3D.Path.LoopStep

open private TwistGridRem2_Hpath_succ TwistGridRem2_X TwistGridRem2_pathH TwistGridRem2_Hpath_eq TwistGridRem2_X_herm
  TwistGridRem2_Hpath_herm from RBM3D.BA.TwistGridRem2

open private gdn_time_facts gdn_loopOf_eq from RBM3D.Induction.GridDriftN

open private OneStep_norm_Eblk_le_one from RBM3D.Path.OneStep

open private HierAlgebra_cutGlueL_succ_eq HierAlgebra_cutGlueR_succ_eq HierAlgebra_cutGlueL_one_eq
  HierAlgebra_cutGlueR_one_eq HierAlgebra_sum_Icc_one_eq_range HierAlgebra_set_ofFn_eq_ofFn_update
  from RBM3D.Induction.HierAlgebra

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The walk, the small facts, the link and `HierDriftGen_KLoop` -/

section Small

variable {d : ℕ}

/-- **`baStep2Mat_walkForm`**: the walk class `StepDecompGen_WalkForm` at the BA carrier, for every `lam0, E`:
walk coupling `0`, shift `lam0 n • Ψ`.  `Pp` and `Hpath` are definitional (`BA/Step2BA.lean`); `Ψ` is Hermitian
(`PsiI_isHermitian`, real scalar). -/
theorem baStep2Mat_walkForm (sz : Sizes d) (lam0 E : ℕ → ℝ) :
    StepDecompGen_WalkForm (baStep2Mat sz lam0 E) 0 (fun n => ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) :=
  ⟨fun n => by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _],
   rfl, fun _ _ _ _ _ _ => rfl⟩

/-- **`baStep2Mat_S`**: the variance law of the BA walk, `S = SB d L 0` (`EMn2BA_SB_zero`). -/
theorem baStep2Mat_S (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) : (baStep2Mat sz lam0 E).S n = SB d (sz.L n) 0 :=
  (EMn2BA_SB_zero (sz.L n)).symm

/-- **`baStep2Mat_S_rowSum`**: the row sums of the BA kernel are `1`. -/
theorem baStep2Mat_S_rowSum (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (a : Zd d (sz.L n)) :
    ∑ b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).S n a b‖ ≤ 1 := by
  have h : (baStep2Mat sz lam0 E).S n = 1 := rfl
  rw [h]
  simp [Matrix.one_apply, apply_ite (fun x : ℂ => ‖x‖)]

/-- **`baStep2Mat_isProb`**: the law of the BA walk is a probability measure
(`isProbabilityMeasure_pathP (sz.withLam 0)`). -/
instance baStep2Mat_isProb (sz : Sizes d) (lam0 E : ℕ → ℝ) : IsProbabilityMeasure (baStep2Mat sz lam0 E).Pp :=
  isProbabilityMeasure_pathP (sz.withLam 0)

/-- **`baHierDrift_kLink`**: `HierDriftGen_KLink` at the BA carrier, every `lam0, E` (definitional). -/
theorem baHierDrift_kLink (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) : HierDriftGen_KLink (baStep2Mat sz lam0 E) n :=
  fun _ _ _ _ _ => rfl

/-- **`baHierDrift_kLoop`**: `HierDriftGen_KLoop` at one index with `0 < lam0 n` and `BAReal`
(`BAKsol_isKLoopS (baKsolve d)` at `Λ = g = lam0 n`; `S = 1`, `M0 = BAMLoop`). -/
theorem baHierDrift_kLoop (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : HierDriftGen_KLoop (baStep2Mat sz lam0 E) n :=
  ⟨_, BAKsol_isKLoopS (baKsolve d) hg hκ (sz.three_le_L n) hg le_rfl hr⟩

end Small

/-! ## 2. `HierDriftGen_KTwo` at BA (the `l = 2` coupling is `Θ^{(k)}`) -/

section Two

variable {d L : ℕ} [NeZero L] (W : ℕ)

/-- Only the wrap-around cut `(k,l) = (1,n)` has a left chain of length 2 (the kernel-`S` form of the `HierAlgebra` statement). -/
private theorem GridDriftBA_primBilLenS_two (S : Matrix (Zd d L) (Zd d L) ℂ) (K D : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) (hn : 2 ≤ I.length) :
    HierDriftGen_primBilLenS d L W S 2 K D I
      = (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
          K (I.cutGlueL 1 I.length a) * S a b * D (I.cutGlueR 1 I.length b) := by
  have hlenL : ∀ (k l : ℕ) (a : Zd d L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueL k l a).length = k + I.length - l + 1 :=
    fun k l a h1 h2 h3 => LoopIdx.length_cutGlueL I a h1 h2 h3
  rw [HierDriftGen_primBilLenS]
  congr 1
  rw [Finset.sum_eq_single_of_mem 1 (by simp [Finset.mem_Icc]; omega)]
  · rw [Finset.sum_eq_single_of_mem I.length (by simp [Finset.mem_Ioc]; omega)]
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [ite_eq_left (by rw [hlenL 1 I.length a le_rfl (by omega) le_rfl]; omega)]
    · intro l hl hne
      rw [Finset.mem_Ioc] at hl
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right (by rw [hlenL 1 l a le_rfl hl.1 hl.2]; omega)]
  · intro k hk hne
    rw [Finset.mem_Icc] at hk
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (by rw [hlenL k l a hk.1 hl.1 hl.2]; omega)]

/-- Only the adjacent cuts `(k, k+1)` have a right chain of length 2 (the kernel-`S` form of the `HierAlgebra` statement). -/
private theorem GridDriftBA_primBilLenRS_two (S : Matrix (Zd d L) (Zd d L) ℂ) (F G : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) (hn : 2 ≤ I.length) :
    HierDriftGen_primBilLenRS d L W S 2 F G I
      = (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 (I.length - 1), ∑ a : Zd d L, ∑ b : Zd d L,
          F (I.cutGlueL k (k + 1) a) * S a b * G (I.cutGlueR k (k + 1) b) := by
  have hlenR : ∀ (k l : ℕ) (b : Zd d L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueR k l b).length = l - k + 1 :=
    fun k l b h1 h2 h3 => LoopIdx.length_cutGlueR I b h1 h2 h3
  rw [HierDriftGen_primBilLenRS]
  congr 1
  have key : ∀ k ∈ Finset.Icc 1 I.length,
      (∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        (if (I.cutGlueR k l b).length = 2 then
          F (I.cutGlueL k l a) * S a b * G (I.cutGlueR k l b) else 0))
      = if k ∈ Finset.Icc 1 (I.length - 1) then
          (∑ a : Zd d L, ∑ b : Zd d L,
            F (I.cutGlueL k (k + 1) a) * S a b * G (I.cutGlueR k (k + 1) b)) else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hlt : k < I.length
    · rw [ite_eq_left (by rw [Finset.mem_Icc]; omega)]
      rw [Finset.sum_eq_single_of_mem (k + 1) (by rw [Finset.mem_Ioc]; omega)]
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [ite_eq_left (by rw [hlenR k (k + 1) b hk.1 (by omega) (by omega)]; omega)]
      · intro l hl hne
        rw [Finset.mem_Ioc] at hl
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right (by rw [hlenR k l b hk.1 hl.1 hl.2]; omega)]
    · have hkn : k = I.length := by omega
      subst hkn
      rw [ite_eq_right (by rw [Finset.mem_Icc]; omega), Finset.Ioc_self, Finset.sum_empty]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (by intro x hx; rw [Finset.mem_Icc] at *; omega)]

/-- The right-chain terms of the `l = 2` coupling at `S = 1`. -/
private theorem GridDriftBA_Rterm [NeZero W] (T : Bool → Bool → Matrix (Zd d L) (Zd d L) ℂ) (K D : LoopIdx (Zd d L) → ℂ)
    (hK : ∀ s₁ s₂ x y, K ⟨[s₁, s₂], [x, y]⟩ = ((W : ℂ) ^ d)⁻¹ * T s₁ s₂ x y)
    (I : LoopIdx (Zd d L)) (hwf : I.WF) {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ I.length) :
    (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        D (I.cutGlueL k (k + 1) a) * (1 : Matrix (Zd d L) (Zd d L) ℂ) a b * K (I.cutGlueR k (k + 1) b)
      = ∑ c : Zd d L, T (I.σ.getD (k - 1) true) (I.σ.getD k true) (I.a.getD (k - 1) 0) c * D ⟨I.σ, I.a.set (k - 1) c⟩ := by
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne W))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [HierAlgebra_cutGlueL_succ_eq I hk hk']
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, HierAlgebra_cutGlueR_succ_eq I hwf hk hk', hK]
    field_simp
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]
    ring
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The wrap-around term of the `l = 2` coupling at `S = 1` (`K` of the 2-loop `(σ₀, σ_{n-1}), (a, a_{n-1})` is read through `hsym`). -/
private theorem GridDriftBA_Lterm [NeZero W] (T : Bool → Bool → Matrix (Zd d L) (Zd d L) ℂ) (K D : LoopIdx (Zd d L) → ℂ)
    (hK : ∀ s₁ s₂ x y, K ⟨[s₁, s₂], [x, y]⟩ = ((W : ℂ) ^ d)⁻¹ * T s₁ s₂ x y)
    (hsym : ∀ s₁ s₂ x y, T s₁ s₂ x y = T s₂ s₁ y x)
    (I : LoopIdx (Zd d L)) (hwf : I.WF) (hn : 2 ≤ I.length) :
    (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        K (I.cutGlueL 1 I.length a) * (1 : Matrix (Zd d L) (Zd d L) ℂ) a b * D (I.cutGlueR 1 I.length b)
      = ∑ c : Zd d L, T (I.σ.getD (I.length - 1) true) (I.σ.getD 0 true) (I.a.getD (I.length - 1) 0) c *
          D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne W))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, HierAlgebra_cutGlueL_one_eq I hwf hn, HierAlgebra_cutGlueR_one_eq I hwf hn, hK, hsym]
    field_simp
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]
    ring
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The `l = 2` coupling at `S = 1`, as a sum over the slots of the loop. -/
private theorem GridDriftBA_coupling_two [NeZero W] (T : Bool → Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (K D : LoopIdx (Zd d L) → ℂ) (hK : ∀ s₁ s₂ x y, K ⟨[s₁, s₂], [x, y]⟩ = ((W : ℂ) ^ d)⁻¹ * T s₁ s₂ x y)
    (hsym : ∀ s₁ s₂ x y, T s₁ s₂ x y = T s₂ s₁ y x)
    (I : LoopIdx (Zd d L)) (hwf : I.WF) (hn : 2 ≤ I.length) :
    HierDriftGen_couplingLenS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) 2 K D I
      = ∑ i ∈ Finset.range I.length, ∑ c : Zd d L,
          T (I.σ.getD i true) (I.σ.getD ((i + 1) % I.length) true) (I.a.getD i 0) c * D ⟨I.σ, I.a.set i c⟩ := by
  have hR : HierDriftGen_primBilLenRS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) 2 D K I
      = ∑ i ∈ Finset.range (I.length - 1), ∑ c : Zd d L,
          T (I.σ.getD i true) (I.σ.getD ((i + 1) % I.length) true) (I.a.getD i 0) c * D ⟨I.σ, I.a.set i c⟩ := by
    rw [GridDriftBA_primBilLenRS_two W _ D K I hn, Finset.mul_sum,
      HierAlgebra_sum_Icc_one_eq_range (I.length - 1)
        (fun k => (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
          D (I.cutGlueL k (k + 1) a) * (1 : Matrix (Zd d L) (Zd d L) ℂ) a b * K (I.cutGlueR k (k + 1) b))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [GridDriftBA_Rterm W T K D hK I hwf (by omega : 1 ≤ i + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mod_eq_of_lt (by omega : i + 1 < I.length)]
  have hL : HierDriftGen_primBilLenS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) 2 K D I
      = ∑ c : Zd d L, T (I.σ.getD (I.length - 1) true) (I.σ.getD ((I.length - 1 + 1) % I.length) true)
          (I.a.getD (I.length - 1) 0) c * D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
    rw [GridDriftBA_primBilLenS_two W _ K D I hn, GridDriftBA_Lterm W T K D hK hsym I hwf hn,
      show (I.length - 1 + 1) % I.length = 0 by
        rw [show I.length - 1 + 1 = I.length by omega, Nat.mod_self]]
  rw [HierDriftGen_couplingLenS, hR, hL, show I.length = (I.length - 1) + 1 by omega, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  exact add_comm _ _

end Two

/-! ### `HierDriftGen_KTwo` at one index -/

section KTwoBA

variable {d : ℕ}

/-- **`baHierDrift_kTwo`**: `HierDriftGen_KTwo` at the BA carrier at one index with `0 < lam0 n` and
`BAReal`.  `baKsol_two` is `K^{(2)}_{s₁ s₂}(x, y) = W^{-d} (Θ_u M^{s₁ s₂})(x, y)` and `Step2Kern_thetaKer_BA` reads the right side
as the derived kernel `thetaKer` of the carrier; the rotation `BAKsol_rotate` supplies the symmetry
`thetaKer s₁ s₂ x y = thetaKer s₂ s₁ y x` that the wrap-around cut of the loop needs. -/
theorem baHierDrift_kTwo (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : HierDriftGen_KTwo (baStep2Mat sz lam0 E) n := by
  intro u hu H k hk σ a
  rw [← HierDriftGen_couplingLenS_eq_ksim]
  have hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by
    have := hr.2
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    linarith
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hK : ∀ s₁ s₂ x y, (baStep2Mat sz lam0 E).KI n u ⟨[s₁, s₂], [x, y]⟩ =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Step2Gen_thetaKer (baStep2Mat sz lam0 E).toFlowFM n s₁ s₂ u x y := by
    intro s₁ s₂ x y
    have h := baKsol_two d hκ hg (sz.three_le_L n) (sz.W n) hr hu ![s₁, s₂] ![x, y]
    have hloop : KLloopOf d (sz.L n) ![s₁, s₂] ![x, y] = ⟨[s₁, s₂], [x, y]⟩ := by
      simp [KLloopOf, List.ofFn_succ]
    rw [hloop] at h
    change BAKsol d (sz.L n) (sz.W n) _ _ u ⟨[s₁, s₂], [x, y]⟩ = _
    rw [h]
    change _ = _ * Step2Gen_thetaKer (baFM sz lam0 E) n s₁ s₂ u x y
    rw [Step2Kern_thetaKer_BA sz lam0 E n hIm s₁ s₂ u]
    rfl
  have hsym : ∀ s₁ s₂ x y, Step2Gen_thetaKer (baStep2Mat sz lam0 E).toFlowFM n s₁ s₂ u x y =
      Step2Gen_thetaKer (baStep2Mat sz lam0 E).toFlowFM n s₂ s₁ u y x := by
    intro s₁ s₂ x y
    have hrot := BAKsol_rotate (baKsolve d) hg hκ (sz.three_le_L n) hg le_rfl hr (W := sz.W n) u hu s₁ x [s₂] [y] rfl
    have h1 := hK s₁ s₂ x y
    have h2 := hK s₂ s₁ y x
    change BAKsol d (sz.L n) (sz.W n) _ _ u ⟨[s₁, s₂], [x, y]⟩ = _ at h1
    change BAKsol d (sz.L n) (sz.W n) _ _ u ⟨[s₂, s₁], [y, x]⟩ = _ at h2
    have h3 : BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
        (PropSpin (BAmF sz lam0 E n)) u ⟨[s₁, s₂], [x, y]⟩ =
        BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
        (PropSpin (BAmF sz lam0 E n)) u ⟨[s₂, s₁], [y, x]⟩ := hrot
    rw [h1, h2] at h3
    exact mul_left_cancel₀ (inv_ne_zero hW) h3
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hwf : (KLloopOf d (sz.L n) σ a).WF := by
    change (List.ofFn σ).length = (List.ofFn a).length
    simp
  have hlen : (KLloopOf d (sz.L n) σ a).length = k' + 1 := by
    change (List.ofFn a).length = k' + 1
    simp
  rw [show (baStep2Mat sz lam0 E).S n = 1 from rfl,
    GridDriftBA_coupling_two (sz.W n) (fun s₁ s₂ => Step2Gen_thetaKer (baStep2Mat sz lam0 E).toFlowFM n s₁ s₂ u) _ _ hK hsym
      _ hwf (by rw [hlen]; omega), hlen]
  have hget : ∀ (j : ℕ) (hj : j < k' + 1), (List.ofFn σ).getD j true = σ ⟨j, hj⟩ := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  have hrot : ∀ i : Fin (k' + 1), (⟨((i : ℕ) + 1) % (k' + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k' + 1))
      = finRotate (k' + 1) i := by
    intro i
    refine Fin.ext ?_
    rw [coe_finRotate]
    split_ifs with h
    · have : (i : ℕ) = k' := by rw [h]; rfl
      simp [this]
    · have : (i : ℕ) ≠ k' := fun h' => h (Fin.ext (by simpa using h'))
      change ((i : ℕ) + 1) % (k' + 1) = (i : ℕ) + 1
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
  refine (Finset.sum_range _).trans ?_
  unfold Step2Gen_ThetaN
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  have hget' : (List.ofFn a).getD (i : ℕ) 0 = a i := by
    rw [List.getD_eq_getElem (List.ofFn a) 0 (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  change Step2Gen_thetaKer _ n ((List.ofFn σ).getD (i : ℕ) true) ((List.ofFn σ).getD (((i : ℕ) + 1) % (k' + 1)) true) u
      ((List.ofFn a).getD (i : ℕ) 0) c * STLKIMg (baStep2Mat sz lam0 E) n u H ⟨List.ofFn σ, (List.ofFn a).set (i : ℕ) c⟩ = _
  rw [hget i i.isLt, hget _ (Nat.mod_lt _ (by omega)), hrot i, hget', HierAlgebra_set_ofFn_eq_ofFn_update]
  rfl

end KTwoBA

/-! ## 3. `HierDriftGen_UStep` at BA -/

section UStepBA

variable {d : ℕ}

/-- `(E + m).im ≠ 0` under `BAReal` and `0 < κ`. -/
private theorem GridDriftBA_hIm {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hκ : 0 < κ) (hr : BAReal d L g κ E m) :
    (((E : ℝ) : ℂ) + m).im ≠ 0 := by
  have := hr.2
  simp only [Complex.add_im, Complex.ofReal_im, zero_add]
  linarith

open scoped Matrix.Norms.Operator in
/-- The order-2 identity of the BA drift kernel: `uKer_{u,u+Δ} - 1 - Δ Θ_u M = Δ² M Θ_{u+Δ} M Θ_u`
(`BAuKer_eq_one_add`, the resolvent identities `Θ = 1 + tMΘ = 1 + tΘM` and `[M, Θ_u] = 0`). -/
private theorem GridDriftBA_uKer_second {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {u Δ : ℝ}
    (hu : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (σ₁ σ₂ : Bool) :
    BAuKer d L g E m u (u + Δ) σ₁ σ₂ - 1 - (Δ : ℂ) • (BATheta d L g E m u σ₁ σ₂ *
        BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) =
      ((Δ : ℂ) ^ 2) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m (u + Δ) σ₁ σ₂ *
        BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m u σ₁ σ₂) := by
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ with hQ
  set Θa := BATheta d L g E m (u + Δ) σ₁ σ₂ with hΘa
  set Θb := BATheta d L g E m u σ₁ σ₂ with hΘb
  have hv0 : 0 ≤ u + Δ := by linarith
  have hA := (BATheta_resolvent d L g κ E m hr (u + Δ) hv0 hv σ₁ σ₂).2
  have hB := (BATheta_resolvent d L g κ E m hr u hu (by linarith) σ₁ σ₂).1
  have hU := BAuKer_eq_one_add hr (s := u) hv0 hv σ₁ σ₂
  have hbc : Q * Θb = Θb * Q := Step2Kern_Theta_comm Q (u : ℂ)
  have h1 : ((u + Δ : ℝ) : ℂ) • (Θa * Q) = Θa - 1 := (sub_eq_of_eq_add' hA).symm
  have h2 : (u : ℂ) • (Q * Θb) = Θb - 1 := (sub_eq_of_eq_add' hB).symm
  have hdiff : (Δ : ℂ) • (Θa * Q * Θb) = Θa - Θb := by
    have e : (Δ : ℂ) = ((u + Δ : ℝ) : ℂ) - (u : ℂ) := by push_cast; ring
    calc (Δ : ℂ) • (Θa * Q * Θb)
        = (((u + Δ : ℝ) : ℂ) • (Θa * Q)) * Θb - Θa * ((u : ℂ) • (Q * Θb)) := by
          rw [e, sub_smul, smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = Θa - Θb := by rw [h1, h2]; noncomm_ring
  rw [hU]
  have e2 : (((u + Δ : ℝ) : ℂ) - (u : ℂ)) = (Δ : ℂ) := by push_cast; ring
  rw [e2, ← hbc]
  have h3 : Q * Θa - Q * Θb = (Δ : ℂ) • (Q * (Θa * Q * Θb)) := by
    rw [← mul_sub, ← hdiff, mul_smul_comm]
  calc 1 + (Δ : ℂ) • (Q * Θa) - 1 - (Δ : ℂ) • (Q * Θb)
      = (Δ : ℂ) • (Q * Θa - Q * Θb) := by rw [smul_sub]; abel
    _ = (Δ : ℂ) • ((Δ : ℂ) • (Q * (Θa * Q * Θb))) := by rw [h3]
    _ = ((Δ : ℂ) ^ 2) • (Q * Θa * Q * Θb) := by
        rw [smul_smul, ← pow_two]
        congr 1
        simp only [mul_assoc]

open scoped Matrix.Norms.Operator in
/-- **`baHierDrift_uStep`**: `HierDriftGen_UStep` at the BA carrier at every index under `BAReal` and `0 < κ` (no `0 < lam0 n`).
Field 1 is `TwistGridWTail_norm_twU_sub_one_le` through `twU_eq_uKer`, as row sums; field 2 (order 2) is
`GridDriftBA_uKer_second` with `‖M‖ ≤ 1` (`EKPins_norm_Q_le`) and `‖Θ_t‖ ≤ (1 - t)⁻¹` (`EKPins_norm_Theta_le`). -/
theorem baHierDrift_uStep (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : HierDriftGen_UStep (baFM sz lam0 E) n := by
  have hIm := GridDriftBA_hIm hκ hr
  refine ⟨fun σ σ' s t ht0 ht1 a => ?_, fun σ σ' u Δ hu hΔ hv a => ?_⟩
  · have h := TwistGridWTail_norm_twU_sub_one_le sz lam0 E n hr ![σ, σ'] s ht0 ht1
    rw [twU_eq_uKer sz lam0 E n hIm] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact (sum_norm_row_le (Step2Gen_uKer (baFM sz lam0 E) n σ σ' s t - 1) a).trans h
  · have hid := GridDriftBA_uKer_second hr hu hΔ hv σ σ'
    have hv0 : 0 ≤ u + Δ := by linarith
    have hnorm : ‖Step2Gen_uKer (baFM sz lam0 E) n σ σ' u (u + Δ) - 1 -
        (Δ : ℂ) • Step2Gen_thetaKer (baFM sz lam0 E) n σ σ' u‖ ≤ Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by
      rw [Step2Kern_uKer_BA sz lam0 E n hIm, Step2Kern_thetaKer_BA sz lam0 E n hIm, hid, norm_smul]
      have hc : ‖((Δ : ℂ) ^ 2)‖ = Δ ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hΔ]
      rw [hc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hQ := EKPins_norm_Q_le hr σ σ'
      have hTa := EKPins_norm_Theta_le hr hv0 hv σ σ'
      have hTb := EKPins_norm_Theta_le hr hu (by linarith) σ σ'
      have hpos : 0 < 1 - (u + Δ) := by linarith
      have hmono : (1 - u)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ hpos (by linarith)
      calc ‖BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ' *
            BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (u + Δ) σ σ' *
            BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ' *
            BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u σ σ'‖
          ≤ ‖BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ'‖ *
            ‖BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (u + Δ) σ σ'‖ *
            ‖BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) σ σ'‖ *
            ‖BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) u σ σ'‖ := by
            refine (norm_mul_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            refine (norm_mul_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact norm_mul_le _ _
        _ ≤ 1 * (1 - (u + Δ))⁻¹ * 1 * (1 - u)⁻¹ := by gcongr
        _ ≤ 1 * (1 - (u + Δ))⁻¹ * 1 * (1 - (u + Δ))⁻¹ := by gcongr
        _ = (1 - (u + Δ))⁻¹ ^ 2 := by ring
    refine (sum_norm_row_le (Step2Gen_uKer (baFM sz lam0 E) n σ σ' u (u + Δ) - 1 -
      (Δ : ℂ) • Step2Gen_thetaKer (baFM sz lam0 E) n σ σ' u) a).trans' ?_ |>.trans hnorm
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact le_rfl

end UStepBA

/-! ## 4. `HierDriftGen_Expand` at BA -/

section ExpandBA

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- A private version of the (private) `StandardBorelSpace` instance of `Path/LoopStep.lean` (as in `TwistGridRem2`). -/
private instance GridDriftBA_sbs (sz : Sizes d) (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

/-- **The freezing of the BA walk step at coupling `0`** (the pattern of `TwistGridRem2_condExp_step`, `BA/TwistGridRem2.lean`, for an arbitrary
bounded continuous observable `Φ`): the conditional mean of `Φ (H_{j+1})` given `F_j` is the Gaussian integral over the one-step law of
the coupling `0` (`PF d L W 0`) of `Φ (H_j + √Δ X)`.  `filt sz j` and `filt (sz.withLam 0) j` are the same σ-algebra (`PathΩ` and `SeqΩ`
depend on `(L, W)` only). -/
private theorem GridDriftBA_condExp_step (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (hΦc : Continuous Φ) {B : ℝ}
    (hΦb : ∀ A, ‖Φ A‖ ≤ B) :
    ((baStep2Mat sz lam0 E).Pp)[fun ω' => Φ ((baStep2Mat sz lam0 E).Hpath s t K n (j + 1) ω') | filt sz j]
      =ᵐ[(baStep2Mat sz lam0 E).Pp] fun ω => ∫ y : Ω d (sz.L n) (sz.W n),
        Φ ((baStep2Mat sz lam0 E).Hpath s t K n j ω + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y)
          ∂(PF d (sz.L n) (sz.W n) 0) := by
  classical
  have : IsProbabilityMeasure (baStep2Mat sz lam0 E).Pp := baStep2Mat_isProb sz lam0 E
  set Δ : ℝ := gridStep s t K n with hΔ
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ (sz.withLam 0) → ℂ :=
    fun p x => Φ (p + (Real.sqrt Δ : ℂ) • TwistGridRem2_X sz n x) with hF
  have hXmeas : Measurable (TwistGridRem2_X sz n) :=
    (continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice (sz.withLam 0) n)
  have hFmeas : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ (sz.withLam 0) =>
      F p.1 p.2) := by
    have h2 : Measurable fun x : Sizes.SeqΩ (sz.withLam 0) => (Real.sqrt Δ : ℂ) • TwistGridRem2_X sz n x :=
      hXmeas.const_smul (Real.sqrt Δ : ℂ)
    have h3 : Measurable fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ × Sizes.SeqΩ (sz.withLam 0) =>
        p.1 + (Real.sqrt Δ : ℂ) • TwistGridRem2_X sz n p.2 :=
      measurable_fst.add (h2.comp measurable_snd)
    exact hΦc.measurable.comp h3
  have hY : Measurable[filt (sz.withLam 0) j] (fun ω : PathΩ sz => (baStep2Mat sz lam0 E).Hpath s t K n j ω) := by
    change Measurable[filt (sz.withLam 0) j] (fun ω : PathΩ sz =>
      (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + TwistGridRem2_pathH sz s t K n j ω)
    exact (LoopStep_measurable_pathH_filt (sz.withLam 0) s t K n j).const_add _
  have hYm : Measurable (fun ω : PathΩ sz => (baStep2Mat sz lam0 E).Hpath s t K n j ω) :=
    hY.mono ((filt (sz.withLam 0)).le j) le_rfl
  have hFInt : ∀ p, Integrable (F p) (Sizes.seqP (sz.withLam 0)) := by
    intro p
    have hm' : Measurable (fun x : Sizes.SeqΩ (sz.withLam 0) => F p x) :=
      hFmeas.comp (measurable_const.prodMk measurable_id)
    exact (memLp_top_of_bound hm'.aestronglyMeasurable B
      (Eventually.of_forall fun x => hΦb _)).integrable le_top
  have hIntTarget : Integrable (fun ω : PathΩ sz => F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) (ω (j + 1)))
      ((baStep2Mat sz lam0 E).Pp) := by
    have hm' : Measurable (fun ω : PathΩ sz => F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) (ω (j + 1))) :=
      hFmeas.comp (hYm.prodMk (measurable_pi_apply (j + 1)))
    exact (memLp_top_of_bound hm'.aestronglyMeasurable B
      (Eventually.of_forall fun ω => hΦb _)).integrable le_top
  have hEq : (fun ω' : PathΩ sz => Φ ((baStep2Mat sz lam0 E).Hpath s t K n (j + 1) ω')) =
      fun ω => F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) (ω (j + 1)) := by
    funext ω
    change Φ _ = Φ _
    rw [TwistGridRem2_Hpath_succ]
  have h1 := LoopStep_condExp_freezeC (sz := sz.withLam 0) j hY hFmeas hFInt hIntTarget
  rw [hEq]
  filter_upwards [h1] with ω hω
  refine hω.trans ?_
  set f : Ω d (sz.L n) (sz.W n) → ℂ := fun y =>
    Φ ((baStep2Mat sz lam0 E).Hpath s t K n j ω + (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) y) with hfdef
  have hfcont : Continuous f := by
    have h2 : Continuous fun y : Ω d (sz.L n) (sz.W n) => (Real.sqrt Δ : ℂ) • Xmat d (sz.L n) (sz.W n) y :=
      (continuous_Xmat d (sz.L n) (sz.W n)).const_smul (Real.sqrt Δ : ℂ)
    exact hΦc.comp (continuous_const.add h2)
  have hFf : ∀ x, F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) x = f (Sizes.slice (sz.withLam 0) n x) := fun x => rfl
  calc ∫ x, F ((baStep2Mat sz lam0 E).Hpath s t K n j ω) x ∂(Sizes.seqP (sz.withLam 0))
      = ∫ x, f (Sizes.slice (sz.withLam 0) n x) ∂(Sizes.seqP (sz.withLam 0)) := by simp only [hFf]
    _ = ∫ y, f y ∂((Sizes.seqP (sz.withLam 0)).map (Sizes.slice (sz.withLam 0) n)) :=
        (integral_map (Sizes.measurable_slice (sz.withLam 0) n).aemeasurable hfcont.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(PF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n)) := by
        rw [Sizes.seqP_map_slice]
        rfl

/-- **The generator in the jets of a loop word** (`genMatOf`, `Induction/LoopGenN.lean`; the loop analogue of
`TwistGridRem_twGenM_eq`, `BA/TwistGridRem.lean`): for Hermitian `M`, `u < 1`, `0 < Im m`,
`genMatOf g m E u M I = g_z(M) + J1_z(M; Dsp)` for the word `(σ_i, a_i)` with letters `Eblk`. -/
private theorem GridDriftBA_genMatOf_eq {L W : ℕ} [NeZero L] [NeZero W] (g : ℝ) {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ}
    (hu1 : u < 1) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (I : LoopIdx (Zd d L)) :
    RBM.Ind.genMatOf d L W g m E u M I =
      TwistGridRem_g g (Eblk d L W) (I.σ.zip I.a) (ztOf m E u) M +
        TwistGridRem_J1 (Eblk d L W) (I.σ.zip I.a) (blockMat d L W M) (ztOf m E u) (TwistGridRem_Dsp d L W m) := by
  have hz : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im]
    exact (TwistGridRem_eta_pos hm hu1).ne'
  have hHb : (blockMat d L W M).IsHermitian := hM.submatrix _
  unfold RBM.Ind.genMatOf TwistGridRem_g
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    exact TwistGridRem_deriv_deriv (Ei := Eblk d L W) (l := I.σ.zip I.a) hM (coordinateMatrix_isHermitian d L W c) hz
  · exact (TwistGridRem_hasDerivAt_spec0 (Ei := Eblk d L W) (l := I.σ.zip I.a) hHb hm E hu1).deriv

/-- **The generator as the pair term plus `𝓔^{G̃}`** (the `hpair` step of the hierarchy statement of `Chain/HierDriftGen.lean`, at the BA
carrier: `loopGenNOf` at `g = 0`, `S = 1 = SB d L 0`; `LIM`, `m` are definitional, so no `LoopForm` is read). -/
private theorem GridDriftBA_genMatOf_pair (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (hm : 0 < (BAmF sz lam0 E n).im) {u : ℝ}
    (hu1 : u < 1) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    (I : LoopIdx (Zd d (sz.L n))) (hI : I.WF) :
    RBM.Ind.genMatOf d (sz.L n) (sz.W n) 0 (BAmF sz lam0 E n) (E n) u M I =
      treeEqRhsS d (sz.L n) (sz.W n) ((baStep2Mat sz lam0 E).S n) (STLIMg (baStep2Mat sz lam0 E) n u M) I +
        STegtMg (baStep2Mat sz lam0 E) n u M I := by
  have hI' := gdn_loopOf_eq I hI
  rw [← hI']
  have hgen := RBM.Ind.loopGenNOf d (sz.L n) (sz.W n) 0 (BAmF sz lam0 E n) (E n) (sz.three_le_L n) hm u hu1 M hM
    (fun i : Fin I.length => I.σ.getD i false) (fun i : Fin I.length => I.a.getD i (0 : Zd d (sz.L n)))
  refine hgen.trans ?_
  have hS : (baStep2Mat sz lam0 E).S n = SB d (sz.L n) 0 := baStep2Mat_S sz lam0 E n
  simp only [treeEqRhsS, STegtMg, STavgErrMg, STmsigg, STLIMg, hS, PropSpin]
  rfl

/-- **`baHierDrift_expand`**: `HierDriftGen_Expand` at the BA carrier at one index under `BAReal` and `0 < κ` (no `0 < lam0 n`; every
`s, t, K`).  The freezing of the walk step at coupling `0` (`GridDriftBA_condExp_step`), the word envelope `TwistGridRem_envelope_word`
for the loop word with letters `Eblk` (`‖Eblk‖ ≤ 1`, `0 < Im m`, `‖m‖ ≤ 1`), and the identification
`TwistGridRem_g 0 + J1 = genMatOf 0 m E u = treeEqRhsS S (𝓛) + 𝓔^{G̃}`. -/
theorem baHierDrift_expand (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    HierDriftGen_Expand (baStep2Mat sz lam0 E) s t K n := by
  intro hs0 hst ht1 hK j hj I hI h2
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := gdn_time_facts s t K n j hs0 hst ht1 hK hj
  have hm : 0 < (BAmF sz lam0 E n).im := lt_of_lt_of_le hκ hr.2
  have hmn : ‖BAmF sz lam0 E n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) _ ((E n : ℝ) : ℂ) _ (by simp) hr.1
  have hu1 : gridTime s t K n j < 1 := by linarith
  have : IsProbabilityMeasure (baStep2Mat sz lam0 E).Pp := baStep2Mat_isProb sz lam0 E
  have hE : ∀ i, ‖Eblk d (sz.L n) (sz.W n) i‖ ≤ 1 := fun i => OneStep_norm_Eblk_le_one i
  have hwlen : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, List.length_zip, hI.symm]
  set z : ℂ := ztOf (BAmF sz lam0 E n) (E n) (gridTime s t K n (j + 1)) with hzdef
  have hη : 0 < etaOf (BAmF sz lam0 E n) (gridTime s t K n (j + 1)) := TwistGridRem_eta_pos hm hv1
  have hz : z.im ≠ 0 := by
    rw [hzdef, ztOf_im]
    exact hη.ne'
  have hηz : 0 < |z.im| := abs_pos.mpr hz
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ := fun A =>
    TwistGridRem_F (Eblk d (sz.L n) (sz.W n)) (I.σ.zip I.a) (blockMat d (sz.L n) (sz.W n) (LoopStep_herm A)) z with hΦ
  have hΦcont : Continuous Φ :=
    TwistGridRem_continuous_F (f := fun A => blockMat d (sz.L n) (sz.W n) (LoopStep_herm A))
      ((LoopStep_continuous_herm (d := d) (L := sz.L n) (W := sz.W n)).matrix_submatrix _ _)
      (fun A => (LoopStep_herm_isHermitian A).submatrix _) hz
  have hΦbd : ∀ A, ‖Φ A‖ ≤ (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) * (|z.im|⁻¹) ^ (I.σ.zip I.a).length :=
    fun A => TwistGridRem_norm_F_le hE ((LoopStep_herm_isHermitian A).submatrix _) hηz le_rfl
  have hfr := GridDriftBA_condExp_step sz lam0 E s t K n j Φ hΦcont hΦbd
  have hΦeq : ∀ A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, A.IsHermitian →
      Φ A = STLIMg (baStep2Mat sz lam0 E) n (gridTime s t K n (j + 1)) A I := fun A hA => by
    simp only [hΦ, LoopStep_herm_of_isHermitian hA]
    rfl
  have hce : ((baStep2Mat sz lam0 E).Pp)[fun ω' => STLIMg (baStep2Mat sz lam0 E) n (gridTime s t K n (j + 1))
        ((baStep2Mat sz lam0 E).Hpath s t K n (j + 1) ω') I | filt sz j]
      =ᵐ[(baStep2Mat sz lam0 E).Pp] ((baStep2Mat sz lam0 E).Pp)[fun ω' => Φ ((baStep2Mat sz lam0 E).Hpath s t K n (j + 1) ω')
        | filt sz j] :=
    condExp_congr_ae (Eventually.of_forall fun ω' => (hΦeq _ (TwistGridRem2_Hpath_herm sz lam0 E s t K n (j + 1) ω')).symm)
  filter_upwards [hfr, hce] with ω hω hω'
  rw [hω', hω]
  have hHj := TwistGridRem2_Hpath_herm sz lam0 E s t K n j ω
  have key := TwistGridRem_envelope_word (g := 0) (Ei := Eblk d (sz.L n) (sz.W n)) (l := I.σ.zip I.a) hE hm hmn (E n)
    hu0 hΔ0 (by rw [← hvu]; exact hv1) hHj
  rw [← hvu, hwlen] at key
  have hint : ∫ y : Ω d (sz.L n) (sz.W n),
        Φ ((baStep2Mat sz lam0 E).Hpath s t K n j ω + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y)
          ∂(PF d (sz.L n) (sz.W n) 0) =
      ∫ y : Ω d (sz.L n) (sz.W n), TwistGridRem_F (Eblk d (sz.L n) (sz.W n)) (I.σ.zip I.a)
        (blockMat d (sz.L n) (sz.W n) ((baStep2Mat sz lam0 E).Hpath s t K n j ω +
          (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y)) z ∂(PF d (sz.L n) (sz.W n) 0) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hh := OneStep_isHermitian_add_realSmul hHj (Xmat_isHermitian d (sz.L n) (sz.W n) y) (Real.sqrt (gridStep s t K n))
    simp only [hΦ, LoopStep_herm_of_isHermitian hh]
  have hpair := GridDriftBA_genMatOf_pair sz lam0 E n hm hu1 hHj I hI
  rw [GridDriftBA_genMatOf_eq 0 hm (E n) hu1 hHj I] at hpair
  rw [hint, ← hpair]
  exact key

end ExpandBA

/-! ## 5. The classes along the flow and the readings -/

section Flow

variable {d : ℕ}

/-- **The classes at one index**: `HierDriftGen_KLoop`, `HierDriftGen_KTwo`, `HierDriftGen_UStep` at the BA carrier at an index with `0 < lam0 n` and
`BAReal`. -/
theorem baHierDrift_kClasses (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : 0 < lam0 n)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) :
    HierDriftGen_KLoop (baStep2Mat sz lam0 E) n ∧ HierDriftGen_KTwo (baStep2Mat sz lam0 E) n ∧
      HierDriftGen_UStep (baFM sz lam0 E) n :=
  ⟨baHierDrift_kLoop sz lam0 E n κ hκ hg hr, baHierDrift_kTwo sz lam0 E n κ hκ hg hr, baHierDrift_uStep sz lam0 E n κ hκ hr⟩

/-- **`baHierDrift_classes`**: along the BA flow, `HierDriftGen_Expand`, `HierDriftGen_KLink` and the row sums at every index, and
`HierDriftGen_KLoop`, `HierDriftGen_KTwo`, `HierDriftGen_UStep` eventually (the window `0 < BAflowLam0 sz z n`, `BAflow_lam0_window`; `HierDriftGen_UStep` holds at every index
by `baHierDrift_uStep`, the eventual form is the one the drift reading takes). -/
theorem baHierDrift_classes (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) :
    (∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ),
        HierDriftGen_Expand (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n) ∧
      (∀ n : ℕ, HierDriftGen_KLink (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n) ∧
      (∀ (n : ℕ) (a : Zd d (sz.L n)),
        ∑ b : Zd d (sz.L n), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).S n a b‖ ≤ 1) ∧
      ∀ᶠ n in Filter.atTop,
        HierDriftGen_KLoop (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
          HierDriftGen_KTwo (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
          HierDriftGen_UStep (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n :=
  ⟨fun s t K n => baHierDrift_expand sz _ _ n κ hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) s t K,
    fun n => baHierDrift_kLink sz _ _ n, fun n a => baStep2Mat_S_rowSum sz _ _ n a,
    by
      filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
      exact baHierDrift_kClasses sz _ _ n κ hκ hn.1 (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)⟩

end Flow


end RBM.BA

end
