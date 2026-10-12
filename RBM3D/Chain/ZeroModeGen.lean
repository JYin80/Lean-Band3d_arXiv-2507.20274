/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopAlgebra

/-!
# The zero-mode layer over the carrier (BA-U row U1s1, ticket T2463)

Additive restatement of `Induction/ZeroModeCalc.lean`, `Induction/NewPQ.lean` and
`Induction/QopAlgebra.lean` (none edited) on the one kernel `Step2Gen_UN`, `Step2Gen_ThetaN` of
`Chain/Step2Gen.lean` (supervisor 1152 U-C4: no second kernel, no `Ugen` definition).
`Induction/QopNorm.lean` is model-free and gets no generic text.

* **The kernel premise.** `ZeroModeGen_KerSums C n`: for each charge pair `X = M^{(σσ')} S` has
  all row and all column sums equal to one constant.  It replaces `3 ≤ L`, the symmetric `Theta` and
  `‖t μ‖ < 1` of the band files; `zeroModeGen_kerSums_band` proves it at `bandFM`.
* **Commutation.** `zeroModeSet_UNg`, `zeroModeSet_ThetaNg` (every `s, t`: `Step2Gen_Theta` is
  `Ring.inverse`), and `(iisuwjyys)` with `Q^{(A)}` inside the kernel on the grid.
* **`lem: newPQ`.** `ZeroModeGen_WardFam`, `zeroModeGen_loopL_wardFam`, `zeroModeGen_newPQ`
  (model-free) and the carrier class `ZeroModeGen_WardCls` with the `(𝓛 - 𝒦)` expansions.
* **`QopAlgebra`.** Column sums, sum-zero preservation and the commutators for the carrier kernels.

Band sources: `ZeroModeCalc.lean` (ticket T2112), `NewPQ.lean` (T2086), `QopAlgebra.lean` (T2055).
Private band helpers are reused by `open private`; the ones that mention the band kernels are copied
under the stem `ZeroModeGen_`.
-/

set_option linter.style.longLine false

open private npq_main NPQTerm NPQTerm.val NPQTerm.k NPQTerm.ξ NPQTerm.σ NPQTerm.ι NPQTerm.A NPQFam NPQFam.mk
  npq_ward_of_fam npq_loopL_rotate npq_loopL_ward from RBM3D.Induction.NewPQ
open private zmcSlot zmcSlot_comm from RBM3D.Induction.ZeroModeCalc
open private qa_slot_zero qa_slot_succ qa_sum_filter_prod qa_sum_fiber0 from RBM3D.Induction.QopAlgebra

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### 1. The kernel premise -/

/-- **The one carrier fact of the zero-mode layer** (`T2463_KerSums`): for every charge pair the generator
`X = M^{(σσ')} S` of the carrier kernels has all row sums and all column sums equal to one constant `c`. -/
def ZeroModeGen_KerSums {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  ∀ σ σ' : Bool, ∃ c : ℂ,
    (∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c) ∧
      ∀ b : Zd d (sz.L n), ∑ a : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c

/-- At `bandFM`, `X = M^{(σσ')} S = m(σ) m(σ') S^{(B)}` (`Step2Kern_Mss_band`). -/
theorem zeroModeGen_X_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) :
    Step2Kern_Mss (bandFM sz E) n σ σ' * (bandFM sz E).S n =
      (mSigma (E n) σ * mSigma (E n) σ') • SB d (sz.L n) (sz.lam n) := by
  rw [Step2Kern_Mss_band, smul_mul_assoc, one_mul]; rfl

/-- The row sums of `X` at `bandFM` are `μ = m(σ) m(σ')` (`sum_SB_row`, `3 ≤ L`). -/
theorem zeroModeGen_rowSum_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool)
    (a : Zd d (sz.L n)) :
    ∑ b : Zd d (sz.L n), (Step2Kern_Mss (bandFM sz E) n σ σ' * (bandFM sz E).S n) a b =
      mSigma (E n) σ * mSigma (E n) σ' := by
  rw [zeroModeGen_X_band]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, sum_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) a, mul_one]

/-- The column sums of `X` at `bandFM` are `μ = m(σ) m(σ')` (`sum_SB_col`, `3 ≤ L`). -/
theorem zeroModeGen_colSum_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool)
    (b : Zd d (sz.L n)) :
    ∑ a : Zd d (sz.L n), (Step2Kern_Mss (bandFM sz E) n σ σ' * (bandFM sz E).S n) a b =
      mSigma (E n) σ * mSigma (E n) σ' := by
  rw [zeroModeGen_X_band]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, sum_SB_col (sz.three_le_L n) b, mul_one]

/-- **`KerSums` at `bandFM`, unconditional** (`T2463_KerSumsBand`): `X = m(σ) m(σ') S^{(B)}`
(`Step2Kern_Mss_band`), with the row and column sums `1` of `S^{(B)}` (`sum_SB_row`, `sum_SB_col`, `3 ≤ L`). -/
theorem zeroModeGen_kerSums_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) :
    ZeroModeGen_KerSums (bandFM sz E) n := by
  intro σ σ'
  exact ⟨mSigma (E n) σ * mSigma (E n) σ', zeroModeGen_rowSum_band sz E n σ σ',
    zeroModeGen_colSum_band sz E n σ σ'⟩

/-- At `bandFM`, `1 - t X` is invertible for `|E n| ≤ 2`, `0 ≤ t < 1` (`‖t μ‖ < 1`, `isUnit_one_sub_smul_SB`). -/
theorem zeroModeGen_isUnit_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) {t : ℝ}
    (hE : |E n| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IsUnit (1 - (t : ℂ) • (Step2Kern_Mss (bandFM sz E) n σ σ' * (bandFM sz E).S n)) := by
  rw [zeroModeGen_X_band, smul_smul]
  exact isUnit_one_sub_smul_SB d (sz.L n) (sz.lam n) (norm_SB d (sz.L n) (sz.lam n) (sz.three_le_L n))
    (norm_mul_mSigma_lt_one hE ht0 ht1 σ σ')

section KerRoute

variable {d : ℕ} {sz : Sizes d}

/-- `Ring.inverse` of an element that commutes with `a` commutes with `a`. -/
private theorem ZeroModeGen_commute_ringInverse {R : Type*} [Ring R] {a y : R} (h : Commute a y) :
    Commute a (Ring.inverse y) := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hy]
    exact Commute.zero_right _

/-- `Proj_{e^⊥}` commutes with `X = M^{(σσ')} S` as soon as `X` has constant row and column sums
(`ZeroModeCalc_projMat_comm_of_sums`, ZMC:297). -/
theorem zeroModeGen_projMat_comm_X (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n) (σ σ' : Bool) :
    projMat d (sz.L n) * (Step2Kern_Mss C n σ σ' * C.S n) =
      (Step2Kern_Mss C n σ σ' * C.S n) * projMat d (sz.L n) := by
  obtain ⟨c, hr, hc⟩ := hK σ σ'
  exact ZeroModeCalc_projMat_comm_of_sums _ c hr hc

/-- `Proj_{e^⊥}` commutes with `Step2Gen_uKer`, for every `s, t` (no window: `Θ_t` is `Ring.inverse`). -/
theorem zeroModeGen_projMat_comm_uKer (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    (σ σ' : Bool) (s t : ℝ) :
    projMat d (sz.L n) * Step2Gen_uKer C n σ σ' s t = Step2Gen_uKer C n σ σ' s t * projMat d (sz.L n) := by
  have hX : Commute (projMat d (sz.L n)) (Step2Kern_Mss C n σ σ' * C.S n) :=
    zeroModeGen_projMat_comm_X C n hK σ σ'
  have h1 : Commute (projMat d (sz.L n)) (1 - (s : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) :=
    (Commute.one_right _).sub_right (hX.smul_right _)
  have h2 : Commute (projMat d (sz.L n)) (Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ)) :=
    ZeroModeGen_commute_ringInverse ((Commute.one_right _).sub_right (hX.smul_right _))
  exact (h1.mul_right h2).eq

/-- `Proj_{e^⊥}` commutes with `Step2Gen_thetaKer`, for every `t`. -/
theorem zeroModeGen_projMat_comm_thetaKer (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    (σ σ' : Bool) (t : ℝ) :
    projMat d (sz.L n) * Step2Gen_thetaKer C n σ σ' t = Step2Gen_thetaKer C n σ σ' t * projMat d (sz.L n) := by
  have hX : Commute (projMat d (sz.L n)) (Step2Kern_Mss C n σ σ' * C.S n) :=
    zeroModeGen_projMat_comm_X C n hK σ σ'
  have h2 : Commute (projMat d (sz.L n)) (Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ)) :=
    ZeroModeGen_commute_ringInverse ((Commute.one_right _).sub_right (hX.smul_right _))
  exact (hX.mul_right h2).eq

end KerRoute

/-! ### 2. Commutation of `Q^{(A)}` with the one kernel -/

section Commute

variable {d : ℕ} {sz : Sizes d}

/-- `Step2Gen_ThetaN` is the sum of its slot kernels (`zmc_ThetaN_eq`). -/
private theorem ZeroModeGen_ThetaN_eq (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ)
    (T : (Fin k → Zd d (sz.L n)) → ℂ) :
    Step2Gen_ThetaN C n σ t T =
      ∑ i, zmcSlot i (Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t) T := by
  funext a
  simp only [Step2Gen_ThetaN, zmcSlot, Finset.sum_apply]

/-- **`Q^{(A)}` commutes with `Step2Gen_UN`** (`T2463_ZeroModeSetUNg`; band `zeroModeSet_UN`, ZMC:332), every
`s, t`, no window. -/
theorem zeroModeSet_UNg (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ) :
    zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ s t T) =
      Step2Gen_UN C n σ s t (zeroModeSet d (sz.L n) A T) :=
  ZeroModeCalc_zeroModeSet_tensorKer_comm (d := d) (L := sz.L n) A
    (fun i => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) s t)
    (fun _ _ => zeroModeGen_projMat_comm_uKer C n hK _ _ s t) T

/-- The single-index form: `Q^{(j)}` commutes with `Step2Gen_ThetaN`. -/
theorem zeroModeOp_ThetaNg (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (j : Fin k) (T : (Fin k → Zd d (sz.L n)) → ℂ) :
    zeroModeOp d (sz.L n) j (Step2Gen_ThetaN C n σ t T) =
      Step2Gen_ThetaN C n σ t (zeroModeOp d (sz.L n) j T) := by
  rw [ZeroModeGen_ThetaN_eq, ZeroModeGen_ThetaN_eq, ZeroModeCalc_zeroModeOp_sum]
  exact Finset.sum_congr rfl fun i _ =>
    zmcSlot_comm i j _ (fun _ => zeroModeGen_projMat_comm_thetaKer C n hK _ _ t) T

/-- **`Q^{(A)}` commutes with `Step2Gen_ThetaN`** (`T2463_ZeroModeSetThetaNg`; band `zeroModeSet_ThetaN`, ZMC:395). -/
theorem zeroModeSet_ThetaNg (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ) :
    zeroModeSet d (sz.L n) A (Step2Gen_ThetaN C n σ t T) =
      Step2Gen_ThetaN C n σ t (zeroModeSet d (sz.L n) A T) :=
  ZeroModeCalc_zeroModeSet_comm_of_comm (Step2Gen_ThetaN C n σ t) A
    (fun j _ T' => zeroModeOp_ThetaNg C n hK σ t j T') T

end Commute

/-! ### 3. `(iisuwjyys)` on the grid, `Q^{(A)}` inside the kernel -/

section GridDuhamel

variable {d : ℕ} {sz : Sizes d}

/-- **`(iisuwjyys)` on the grid, `Q^{(A)}` inside `Step2Gen_UN`** (`T2463_DuhamelInsideAtg`; band
`Ind.zeroModeCalc_duhamel_inside_at`, ZMC:522): `stoppedDuhamelNg_at`, additivity of `Q^{(A)}` and of
`Step2Gen_UN`, and `zeroModeSet_UNg` (the carrier fact replaces `3 ≤ L`, `|E n| < 2`). -/
theorem zeroModeCalc_duhamel_inside_atg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hS : Step2Gen_USemigroup Cm.toFlowFM n) (hKer : ZeroModeGen_KerSums Cm.toFlowFM n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ}
    (σ : Fin k → Bool) (A : Finset (Fin k)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz)
    (hjτ : min j (τ ω) ≤ K n) :
    zeroModeSet d (sz.L n) A (AvecNg Cm s t K n (min j (τ ω)) σ ω) =
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
          (zeroModeSet d (sz.L n) A (AvecNg Cm s t K n 0 σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
            (zeroModeSet d (sz.L n) A (predIncNg Cm s t K n i σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
            (zeroModeSet d (sz.L n) A (martIncNg Cm s t K n i σ ω)) := by
  have h := stoppedDuhamelNg_at Cm s t K n hS hs0 hst ht1 hK σ τ j ω hjτ
  rw [h, zeroModeSet_add, zeroModeSet_sum, zeroModeSet_UNg Cm.toFlowFM n hKer]
  simp only [zeroModeSet_UNg Cm.toFlowFM n hKer, zeroModeSet_add, Step2Gen_UN_add,
    Finset.sum_add_distrib]
  abel

end GridDuhamel

/-! ### 4. `lem: newPQ`, model-free -/

section NewPQ

/-- **A Ward family on list indices** (`T2463_WardFam`; the content of the private `NPQFam`, NPQ:257, and the
conclusion shape of `KLK_rotate`, `KLK_ward`): cyclic rotation and the Ward identity at the last index, both
charge orders, with the constant `κ`. -/
def ZeroModeGen_WardFam (d L : ℕ) [NeZero L] (κ : ℂ) (T : LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      T ⟨s :: σ, b :: a⟩ = T ⟨σ ++ [s], a ++ [b]⟩) ∧
    ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, T ⟨s :: μ ++ [!s], a ++ [x]⟩ = κ * (T ⟨true :: μ, a⟩ - T ⟨false :: μ, a⟩)

/-- **G-loops of any Hermitian matrix at `Im z ≠ 0` form a Ward family** with `κ = (2 i W^d Im z)⁻¹`
(`T2463_LoopLWardFam`; the private `npq_loopL_rotate`, `npq_loopL_ward`, NPQ:183, :211, made public). -/
theorem zeroModeGen_loopL_wardFam {d L W : ℕ} [NeZero L] [NeZero W]
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (hH : H.IsHermitian) (hz : z.im ≠ 0) :
    ZeroModeGen_WardFam d L ((2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ))⁻¹) (loopL d L W H z) :=
  ⟨fun s b σ a h => npq_loopL_rotate H z s b σ a h, fun s μ a ha => npq_loopL_ward hH hz s μ a ha⟩

/-- The sum over the list of terms is the sum over `Fin ℓ` (`npq_sum_get`, NPQ:572). -/
private theorem ZeroModeGen_sum_get {α β : Type*} [AddCommMonoid β] (Ls : List α) (F : α → β) :
    ∑ i : Fin Ls.length, F (Ls.get i) = (Ls.map F).sum := by
  calc ∑ i : Fin Ls.length, F (Ls.get i) = (List.ofFn (F ∘ Ls.get)).sum := List.sum_ofFn.symm
    _ = ((List.ofFn Ls.get).map F).sum := by rw [List.map_ofFn]
    _ = (Ls.map F).sum := by rw [List.ofFn_get]

/-- **`lem: newPQ`, model-free** (`T2463_NewPQExpansion`; `(yurenAL)`, `(yurenAK)`; the private `npq_main`,
NPQ:479, with `npq_ward_of_fam`, :404): the data `(ℓ, k, ξ, σ', ι, A')` come before `L`, `κ`, `T`; the coefficient
is `(L^{-d} κ)^{m - k_α}`. -/
theorem zeroModeGen_newPQ (d : ℕ) (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (L : ℕ) [NeZero L] (κ : ℂ) (T : LoopIdx (Zd d L) → ℂ), ZeroModeGen_WardFam d L κ T →
        ∀ a : Fin m → Zd d L,
          zeroModeSet d L A (fun a' => T (loopOf σ a')) a =
            zeroModeSet d L (A ∪ STIdiff σ) (fun a' => T (loopOf σ a')) a +
              ∑ α : Fin ℓ, (ξ α : ℂ) * (((L : ℂ) ^ d)⁻¹ * κ) ^ (m - k α) *
                zeroModeSet d L (A' α) (fun a' => T (loopOf (σ' α) a')) (a ∘ ι α) := by
  obtain ⟨Ls, hf, h⟩ := npq_main d m σ (STIdiff σ) (Finset.Subset.refl _) A
  refine ⟨Ls.length, fun α => NPQTerm.k (Ls.get α), fun α => NPQTerm.ξ (Ls.get α),
    fun α => NPQTerm.σ (Ls.get α), fun α => NPQTerm.ι (Ls.get α), fun α => NPQTerm.A (Ls.get α), ?_, ?_, ?_⟩
  · intro α
    have := hf _ (List.get_mem Ls α)
    exact ⟨this.1, this.2.1⟩
  · intro α
    exact (hf _ (List.get_mem Ls α)).2.2
  · intro L _ κ T hT a
    have hfam : NPQFam d L κ T := NPQFam.mk hT.1 hT.2
    have hward := npq_ward_of_fam hfam (((L : ℂ) ^ d)⁻¹ * κ) rfl
    have key := h L (((L : ℂ) ^ d)⁻¹ * κ) (fun k σ a => T ⟨List.ofFn σ, List.ofFn a⟩) hward a
    have hsum : ∑ α : Fin Ls.length, ((NPQTerm.ξ (Ls.get α) : ℤ) : ℂ) *
          (((L : ℂ) ^ d)⁻¹ * κ) ^ (m - NPQTerm.k (Ls.get α)) *
          zeroModeSet d L (NPQTerm.A (Ls.get α))
            (fun a' => T (loopOf (NPQTerm.σ (Ls.get α)) a')) (a ∘ NPQTerm.ι (Ls.get α))
        = (Ls.map (NPQTerm.val d L (((L : ℂ) ^ d)⁻¹ * κ) (fun k σ a => T ⟨List.ofFn σ, List.ofFn a⟩) a)).sum := by
      rw [← ZeroModeGen_sum_get Ls (NPQTerm.val d L (((L : ℂ) ^ d)⁻¹ * κ) (fun k σ a => T ⟨List.ofFn σ, List.ofFn a⟩) a)]
      exact Finset.sum_congr rfl fun α _ => rfl
    rw [hsum]
    exact key

end NewPQ

/-! ### 5. The carrier class and the `(𝓛 − 𝒦)` expansion -/

section WardCls

/-- **The carrier class of `lem: newPQ`** (`T2463_WardCls`): at every size index, time `τ ∈ [0,1)` and sample,
`C.L` and `C.K` read through `loopOf` are Ward families with `κ = (2 i W^d η_τ)⁻¹`, `η_τ = C.eta n τ`. -/
def ZeroModeGen_WardCls {d : ℕ} (sz : Sizes d) (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ < 1 → ∀ ω : sz.SeqΩ,
    ∃ TL TK : LoopIdx (Zd d (sz.L n)) → ℂ,
      (∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), C.L n τ σ a ω = TL (loopOf σ a)) ∧
      (∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), C.K n τ σ a = TK (loopOf σ a)) ∧
      ZeroModeGen_WardFam d (sz.L n) ((2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n τ : ℂ))⁻¹) TL ∧
      ZeroModeGen_WardFam d (sz.L n) ((2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n τ : ℂ))⁻¹) TK

/-- **`bandFM` is in the class for `|E n| < 2`** (`T2463_WardClsBand`): `TL` is the G-loop of `H_τ` at
`z_τ` (`zeroModeGen_loopL_wardFam`, `etaT_eq_zt_im`), `TK = KLK` (`KLK_rotate`, `KLK_ward`). -/
theorem zeroModeGen_wardCls_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) :
    ZeroModeGen_WardCls sz (bandFM sz E) := by
  intro n τ hτ0 hτ1 ω
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hW : 1 ≤ sz.W n := sz.W_pos n
  have hη : 0 < etaT (E n) τ := etaT_pos (hE n) hτ1
  have hz : (zt (E n) τ).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
  have hHerm : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n τ ω)).IsHermitian :=
    (Sizes.gLoopFlow_seqHflow_isHermitian sz n τ ω).submatrix _
  refine ⟨loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n τ ω)) (zt (E n) τ),
    KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) τ, fun k σ a => ?_, fun k σ a => rfl, ?_, ?_⟩
  · exact loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
  · have := zeroModeGen_loopL_wardFam (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n τ ω)) (zt (E n) τ)
      hHerm hz
    rwa [← etaT_eq_zt_im] at this
  · exact ⟨fun s b σ a h => KLK_rotate d (sz.L n) (sz.W n) (sz.lam n) (E n) hL hW (hE n) τ ⟨hτ0, hτ1⟩ s b σ a h,
      fun s μ a ha => KLK_ward d (sz.L n) (sz.W n) (sz.lam n) (E n) hL hW (hE n) τ hτ0 hτ1 s μ a ha⟩

/-- The coefficient of the Ward step: `L^{-d} (2 i W^d η)⁻¹ = (2 i N η)⁻¹`, `N = (W L)^d`. -/
private theorem ZeroModeGen_coef {d : ℕ} (sz : Sizes d) (n : ℕ) (η : ℂ) :
    (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * η)⁻¹ =
      (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * η)⁻¹ := by
  rw [← mul_inv]
  congr 1
  simp only [Sizes.size]
  push_cast
  ring

/-- **`(𝓛 − 𝒦)` through `lem: newPQ`** (`T2463_LKExpansiongL`; band `Gauss.Sizes.zeroModeCalc_LK_expansion`,
ZMC:563): model-level `C.L − C.K` over the class, `C.eta` for `etaT`. -/
theorem zeroModeCalc_LK_expansiong (d m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (C : FlowFM sz), ZeroModeGen_WardCls sz C → ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ < 1 →
        ∀ (ω : sz.SeqΩ) (a : Fin m → Zd d (sz.L n)),
          zeroModeSet d (sz.L n) A (fun a' => C.L n τ σ a' ω - C.K n τ σ a') a =
            zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => C.L n τ σ a' ω - C.K n τ σ a') a +
              ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α)) *
                zeroModeSet d (sz.L n) (A' α) (fun a' => C.L n τ (σ' α) a' ω - C.K n τ (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeGen_newPQ d m σ A
  refine ⟨ℓ, k, ξ, σ', ι, A', hk, hA, ?_⟩
  intro sz C hC n τ hτ0 hτ1 ω a
  obtain ⟨TL, TK, hL, hK, hwL, hwK⟩ := hC n τ hτ0 hτ1 ω
  have eL := h (sz.L n) _ TL hwL a
  have eK := h (sz.L n) _ TK hwK a
  have hsub : ∀ {k' : ℕ} (A'' : Finset (Fin k')) (σ'' : Fin k' → Bool) (b : Fin k' → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A'' (fun a' => C.L n τ σ'' a' ω - C.K n τ σ'' a') b
        = zeroModeSet d (sz.L n) A'' (fun a' => TL (loopOf σ'' a')) b
          - zeroModeSet d (sz.L n) A'' (fun a' => TK (loopOf σ'' a')) b := by
    intro k' A'' σ'' b
    simp only [hL, hK]
    exact congrFun (zeroModeSet_sub (d := d) (L := sz.L n) A''
      (fun a' => TL (loopOf σ'' a')) (fun a' => TK (loopOf σ'' a'))) b
  have hcoef : ∀ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α))
      = (ξ α : ℂ) * ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n τ : ℂ))⁻¹) ^ (m - k α) := by
    intro α
    rw [ZeroModeGen_coef, div_eq_mul_inv, inv_pow]
  simp only [hsub, hcoef]
  rw [eL, eK]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **`(𝓛 − 𝒦)` through `lem: newPQ`, `A = ∅`** (`T2463_LKExpansionEmptygL`; band
`zeroModeCalc_LK_expansion_empty`, ZMC:595). -/
theorem zeroModeCalc_LK_expansion_emptyg (d m : ℕ) (σ : Fin m → Bool) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (C : FlowFM sz), ZeroModeGen_WardCls sz C → ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ < 1 →
        ∀ (ω : sz.SeqΩ) (a : Fin m → Zd d (sz.L n)),
          C.L n τ σ a ω - C.K n τ σ a =
            zeroModeSet d (sz.L n) (STIdiff σ) (fun a' => C.L n τ σ a' ω - C.K n τ σ a') a +
              ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α)) *
                zeroModeSet d (sz.L n) (A' α) (fun a' => C.L n τ (σ' α) a' ω - C.K n τ (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansiong d m σ ∅
  refine ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun sz C hC n τ hτ0 hτ1 ω a => ?_⟩
  simpa using h sz C hC n τ hτ0 hτ1 ω a

end WardCls

/-! ### 6. `QopAlgebra`'s kernel readings -/

section QopKernels

variable {d : ℕ} {sz : Sizes d}

/-- `Σ_x (X Θ)_{xy} = c Σ_x Θ_{xy}` for column sums `c` of `X`. -/
private theorem ZeroModeGen_colSum_XTheta {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (X Θ : Matrix Λ Λ ℂ)
    (c : ℂ) (hcol : ∀ b, ∑ a, X a b = c) (y : Λ) :
    ∑ x, (X * Θ) x y = c * ∑ x, Θ x y := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_mul, hcol z]

/-- `Σ_x ((1 - r X) Θ)_{xy} = (1 - r c) Σ_x Θ_{xy}`. -/
private theorem ZeroModeGen_colSum_oneSub {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (X Θ : Matrix Λ Λ ℂ)
    (c r : ℂ) (hcol : ∀ b, ∑ a, X a b = c) (y : Λ) :
    ∑ x, ((1 - r • X) * Θ) x y = (1 - r * c) * ∑ x, Θ x y := by
  have h := ZeroModeGen_colSum_XTheta X Θ c hcol y
  simp only [sub_mul, one_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h]
  ring

/-- `Σ_x Θ_{xy} = (1 - t c)⁻¹` for column sums `c` of `X` and an invertible `1 - t X`. -/
private theorem ZeroModeGen_colSum_Theta {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (X : Matrix Λ Λ ℂ)
    (c t : ℂ) (hcol : ∀ b, ∑ a, X a b = c) (hu : IsUnit (1 - t • X)) (y : Λ) :
    ∑ x, Step2Gen_Theta X t x y = (1 - t * c)⁻¹ := by
  have hmul : (1 - t • X) * Step2Gen_Theta X t = 1 := Ring.mul_inverse_cancel _ hu
  have h1 : ∑ x, ((1 - t • X) * Step2Gen_Theta X t) x y = 1 := by
    rw [hmul]
    simp [Matrix.one_apply]
  rw [ZeroModeGen_colSum_oneSub X _ c t hcol y] at h1
  exact eq_inv_of_mul_eq_one_right h1

/-- **Column sums of `Step2Gen_thetaKer`** (`T2463_ColSumThetaKerg`; band `QopAlgebra_col_sum_thetaKer`, QA:697):
column sums `c` of `X` and `IsUnit (1 - t X)` give `c (1 - t c)⁻¹`. -/
theorem QopAlgebra_col_sum_thetaKerg (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (t : ℝ) (c : ℂ)
    (hcol : ∀ b : Zd d (sz.L n), ∑ a : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c)
    (hu : IsUnit (1 - (t : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n))) (y : Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t x y = c * (1 - (t : ℂ) * c)⁻¹ := by
  unfold Step2Gen_thetaKer
  rw [ZeroModeGen_colSum_XTheta _ _ c hcol y, ZeroModeGen_colSum_Theta _ c _ hcol hu y]

/-- **Column sums of `Step2Gen_uKer`** (`T2463_ColSumUKerg`; band `QopAlgebra_col_sum_uKer`, QA:704). -/
theorem QopAlgebra_col_sum_uKerg (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (s t : ℝ) (c : ℂ)
    (hcol : ∀ b : Zd d (sz.L n), ∑ a : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c)
    (hu : IsUnit (1 - (t : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n))) (y : Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), Step2Gen_uKer C n σ σ' s t x y = (1 - (s : ℂ) * c) * (1 - (t : ℂ) * c)⁻¹ := by
  unfold Step2Gen_uKer
  rw [ZeroModeGen_colSum_oneSub _ _ c _ hcol y, ZeroModeGen_colSum_Theta _ c _ hcol hu y]

/-- The column sums of `Step2Gen_thetaKer` are constant in `y`, for every `t` (a non-unit `1 - t X` gives
`Θ = 0`, `Ring.inverse_non_unit`). -/
private theorem ZeroModeGen_thetaKer_colConst (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    (σ σ' : Bool) (t : ℝ) : ∃ κ : ℂ, ∀ y : Zd d (sz.L n),
      ∑ x : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t x y = κ := by
  obtain ⟨c, _, hc⟩ := hK σ σ'
  by_cases hu : IsUnit (1 - (t : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n))
  · exact ⟨c * (1 - (t : ℂ) * c)⁻¹, fun y => QopAlgebra_col_sum_thetaKerg C n σ σ' t c hc hu y⟩
  · refine ⟨0, fun y => ?_⟩
    unfold Step2Gen_thetaKer Step2Gen_Theta
    rw [Ring.inverse_non_unit _ hu]
    simp

/-- The same for `Step2Gen_uKer`. -/
private theorem ZeroModeGen_uKer_colConst (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    (σ σ' : Bool) (s t : ℝ) : ∃ κ : ℂ, ∀ y : Zd d (sz.L n),
      ∑ x : Zd d (sz.L n), Step2Gen_uKer C n σ σ' s t x y = κ := by
  obtain ⟨c, _, hc⟩ := hK σ σ'
  by_cases hu : IsUnit (1 - (t : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n))
  · exact ⟨(1 - (s : ℂ) * c) * (1 - (t : ℂ) * c)⁻¹, fun y => QopAlgebra_col_sum_uKerg C n σ σ' s t c hc hu y⟩
  · refine ⟨0, fun y => ?_⟩
    unfold Step2Gen_uKer Step2Gen_Theta
    rw [Ring.inverse_non_unit _ hu]
    simp

/-- **`Step2Gen_ThetaN` preserves sum-zero tensors** (`T2463_ThetaNSumZerog`; band `QopAlgebra_ThetaN_sumZero`,
QA:786): target 1 only, no window.  Slot `0` gives `Σ_b K(a₁, b)(𝒫A)_b = 0`, every slot `i ≥ 1` the constant column
sum of the slot kernel times `(𝒫A)_{a₁} = 0`. -/
theorem QopAlgebra_ThetaN_sumZerog (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    {m : ℕ} (σ : Fin (m + 1) → Bool) (t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (hA : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) A a₁ = 0) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (Step2Gen_ThetaN C n σ t A) a₁ = 0 := by
  choose κ hκ using fun i : Fin (m + 1) =>
    ZeroModeGen_thetaKer_colConst C n hK (σ i) (σ (finRotate (m + 1) i)) t
  unfold STPsum
  simp only [Step2Gen_ThetaN]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    refine (qa_slot_zero (d := d) (L := sz.L n)
      (fun x y => Step2Gen_thetaKer C n (σ 0) (σ (finRotate (m + 1) 0)) t x y) A a₁).trans ?_
    exact Finset.sum_eq_zero fun b _ => by rw [hA b, mul_zero]
  · refine (qa_slot_succ (d := d) (L := sz.L n) hi
      (fun x y => Step2Gen_thetaKer C n (σ i) (σ (finRotate (m + 1) i)) t x y) A a₁).trans ?_
    simp only [hκ i]
    rw [← Finset.mul_sum]
    have h : ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁), A a = 0 := hA a₁
    rw [h, mul_zero]

/-- **`Step2Gen_UN` preserves sum-zero tensors** (`T2463_UNSumZerog`; band `QopAlgebra_UN_sumZero`, QA:821). -/
theorem QopAlgebra_UN_sumZerog (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    {m : ℕ} (σ : Fin (m + 1) → Bool) (s t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (hA : ∀ a₁ : Zd d (sz.L n), STPsum (d := d) A a₁ = 0) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (Step2Gen_UN C n σ s t A) a₁ = 0 := by
  choose κ hcol using fun i : Fin (m + 1) =>
    ZeroModeGen_uKer_colConst C n hK (σ i) (σ (finRotate (m + 1) i)) s t
  set K : Fin (m + 1) → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
    fun i => Step2Gen_uKer C n (σ i) (σ (finRotate (m + 1) i)) s t with hKdef
  unfold STPsum
  simp only [Step2Gen_UN]
  rw [Finset.sum_comm]
  have h1 : ∀ b : Fin (m + 1) → Zd d (sz.L n),
      ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁), (∏ i, K i (a i) (b i)) * A b
        = (K 0 a₁ (b 0) * ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), κ i) * A b := by
    intro b
    rw [← Finset.sum_mul]
    congr 1
    have h2 : ∀ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁),
        ∏ i, K i (a i) (b i) = K 0 a₁ (b 0) * ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), K i (a i) (b i) := by
      intro a ha
      have ha0 : a 0 = a₁ := (Finset.mem_filter.1 ha).2
      rw [← Finset.mul_prod_erase Finset.univ (fun i => K i (a i) (b i)) (Finset.mem_univ (0 : Fin (m + 1))), ha0]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum,
      qa_sum_filter_prod (d := d) (L := sz.L n) (m := m) a₁ (fun i c => K i c (b i))]
    congr 1
    exact Finset.prod_congr rfl fun i _ => hcol i (b i)
  rw [Finset.sum_congr rfl fun b _ => h1 b]
  have h3 : ∀ b : Fin (m + 1) → Zd d (sz.L n),
      (K 0 a₁ (b 0) * ∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), κ i) * A b
        = (∏ i ∈ Finset.univ.erase (0 : Fin (m + 1)), κ i) * (K 0 a₁ (b 0) * A b) := fun b => by ring
  rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.mul_sum,
    qa_sum_fiber0 (d := d) (L := sz.L n) (fun b₀ => K 0 a₁ b₀) A]
  have : ∑ b₀ : Zd d (sz.L n), K 0 a₁ b₀ * STPsum (d := d) A b₀ = 0 :=
    Finset.sum_eq_zero fun b₀ _ => by rw [hA b₀, mul_zero]
  rw [this, mul_zero]

/-- Linearity of `Step2Gen_ThetaN` (`T2463_ThetaNSubg`; band `QopAlgebra_ThetaN_sub`, QA:860). -/
theorem QopAlgebra_ThetaN_subg (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (u : ℝ)
    (A B : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)) :
    Step2Gen_ThetaN C n σ u (fun b => A b - B b) a =
      Step2Gen_ThetaN C n σ u A a - Step2Gen_ThetaN C n σ u B a := by
  simp only [Step2Gen_ThetaN, mul_sub, Finset.sum_sub_distrib]

/-- Linearity of `Step2Gen_UN` (`T2463_UNSubg`; band `QopAlgebra_UN_sub`, QA:865). -/
theorem QopAlgebra_UN_subg (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (s u : ℝ)
    (A B : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)) :
    Step2Gen_UN C n σ s u (fun b => A b - B b) a =
      Step2Gen_UN C n σ s u A a - Step2Gen_UN C n σ s u B a := by
  simp only [Step2Gen_UN, mul_sub, Finset.sum_sub_distrib]

/-- The commutator `[𝒬_t, Θ^{(m+1)}_{t,σ}]` (`T2463_CommutatorThetaNg`; band `QopAlgebra_commutator_ThetaN`, QA:871). -/
theorem QopAlgebra_commutator_ThetaNg (C : FlowFM sz) (n : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    STQop (d := d) ϑ t (Step2Gen_ThetaN C n σ t A) a - Step2Gen_ThetaN C n σ t (STQop (d := d) ϑ t A) a =
      Step2Gen_ThetaN C n σ t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a -
        STPsum (d := d) (Step2Gen_ThetaN C n σ t A) (a 0) * ϑ t a := by
  have h : Step2Gen_ThetaN C n σ t (STQop (d := d) ϑ t A) a
      = Step2Gen_ThetaN C n σ t A a - Step2Gen_ThetaN C n σ t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a :=
    QopAlgebra_ThetaN_subg C n σ t A (fun b => STPsum (d := d) A (b 0) * ϑ t b) a
  rw [h]
  simp only [STQop]
  ring

/-- The commutator `[𝒬_t, U^{(m+1)}_{s,t,σ}]` (`T2463_CommutatorUNg`; band `QopAlgebra_commutator_UN`, QA:884). -/
theorem QopAlgebra_commutator_UNg (C : FlowFM sz) (n : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (s t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    STQop (d := d) ϑ t (Step2Gen_UN C n σ s t A) a - Step2Gen_UN C n σ s t (STQop (d := d) ϑ t A) a =
      Step2Gen_UN C n σ s t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a -
        STPsum (d := d) (Step2Gen_UN C n σ s t A) (a 0) * ϑ t a := by
  have h : Step2Gen_UN C n σ s t (STQop (d := d) ϑ t A) a
      = Step2Gen_UN C n σ s t A a - Step2Gen_UN C n σ s t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a :=
    QopAlgebra_UN_subg C n σ s t A (fun b => STPsum (d := d) A (b 0) * ϑ t b) a
  rw [h]
  simp only [STQop]
  ring

end QopKernels

/-! ### 7. Band corollaries (target 7 (a)): the band statements re-derived at `bandFM`, `bandStep2Mat` -/

section BandCorollaries

variable {d : ℕ}

/-- `Ind.zeroModeSet_Ugen` (ZMC:450) re-derived through `bandStep2_Ugen` and `zeroModeSet_UNg` at
`zeroModeGen_kerSums_band`: no `3 ≤ L`, `|E| ≤ 2`, `0 ≤ w < 1`. -/
example (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (v w : ℝ) (A : Finset (Fin k))
    (T : (Fin k → Zd d (sz.L n)) → ℂ) :
    zeroModeSet d (sz.L n) A (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v w T) =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v w (zeroModeSet d (sz.L n) A T) := by
  rw [bandStep2_Ugen, bandStep2_Ugen]
  exact zeroModeSet_UNg (bandFM sz E) n (zeroModeGen_kerSums_band sz E n) σ v w A T

/-- `Ind.zeroModeCalc_duhamel_inside_at` (ZMC:522) re-derived from `zeroModeCalc_duhamel_inside_atg` at
`bandStep2Mat` (`step2Gen_USemigroup_band`, `zeroModeGen_kerSums_band`, the bridges `bandStep2_*`). -/
example (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ} (σ : Fin k → Bool) (A : Finset (Fin k))
    (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hjτ : min j (τ ω) ≤ K n) :
    zeroModeSet d (sz.L n) A (RBM.Ind.AvecN sz E s t K n (min j (τ ω)) σ ω) =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
          (zeroModeSet d (sz.L n) A (RBM.Ind.AvecN sz E s t K n 0 σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
            (gridTime s t K n (min j (τ ω)))
            (zeroModeSet d (sz.L n) A (RBM.Ind.predIncN sz E s t K n i σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
            (gridTime s t K n (min j (τ ω)))
            (zeroModeSet d (sz.L n) A (RBM.Ind.martIncN sz E s t K n i σ ω)) := by
  have h := zeroModeCalc_duhamel_inside_atg (bandStep2Mat sz E) s t K n
    (step2Gen_USemigroup_band sz E n hE.le) (zeroModeGen_kerSums_band sz E n) hs0 hst ht1 hK σ A τ j ω hjτ
  simp only [bandStep2_Ugen, bandStep2_AvecN, bandStep2_predIncN, bandStep2_martIncN]
  exact h

/-- `Gauss.Sizes.zeroModeCalc_LK_expansion` (ZMC:563) re-derived from `zeroModeCalc_LK_expansiong` and
`zeroModeGen_wardCls_band` at the constant energy sequence `E` (`C.eta = etaT E`). -/
example (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ)
        (a : Fin m → Zd d (sz.L n)),
        zeroModeSet d (sz.L n) A (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ)
              (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) /
                (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α)
                (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansiong d m σ A
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun sz n E τ hE hτ0 hτ1 ω a =>
    h sz (bandFM sz fun _ => E) (zeroModeGen_wardCls_band sz _ fun _ => hE) n τ hτ0 hτ1 ω a⟩

/-- `Gauss.Sizes.zeroModeCalc_LK_expansion_empty` (ZMC:595) re-derived from `zeroModeCalc_LK_expansion_emptyg`. -/
example (m : ℕ) (σ : Fin m → Bool) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ)
        (a : Fin m → Zd d (sz.L n)),
        STLKM sz n E τ (sz.seqHflow n τ ω) σ a =
          zeroModeSet d (sz.L n) (STIdiff σ)
              (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) /
                (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α)
                (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansion_emptyg d m σ
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun sz n E τ hE hτ0 hτ1 ω a =>
    h sz (bandFM sz fun _ => E) (zeroModeGen_wardCls_band sz _ fun _ => hE) n τ hτ0 hτ1 ω a⟩

/-- `QopAlgebra_ThetaN_sumZero` (QA:786) re-derived at the sign data `mSigma (E n) ∘ σ` through
`Step2Kern_ThetaN_band` and `QopAlgebra_ThetaN_sumZerog`: no `3 ≤ L`, `‖μ_i‖ = 1`, `0 ≤ t < 1`. -/
example (sz : Sizes d) (E : ℕ → ℝ) (n m : ℕ) (σ : Fin (m + 1) → Bool) (t : ℝ)
    (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (hA : ∀ a₁, STPsum (d := d) A a₁ = 0) (a₁ : Zd d (sz.L n)) :
    STPsum (d := d) (ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) t A) a₁ = 0 := by
  rw [← Step2Kern_ThetaN_band]
  exact QopAlgebra_ThetaN_sumZerog (bandFM sz E) n (zeroModeGen_kerSums_band sz E n) σ t A hA a₁

/-- `QopAlgebra_col_sum_thetaKer` (QA:697) re-derived at `μ = m(σ) m(σ')` through `Step2Kern_thetaKer_band`,
`QopAlgebra_col_sum_thetaKerg` and `zeroModeGen_isUnit_band` (the band premise `‖t μ‖ < 1` is `0 ≤ t < 1`,
`|E n| ≤ 2`). -/
example (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) (t : ℝ) (hE : |E n| ≤ 2) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (y : Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), RBM.thetaKer d (sz.L n) (sz.lam n) (mSigma (E n) σ * mSigma (E n) σ') t x y =
      (mSigma (E n) σ * mSigma (E n) σ') * (1 - (t : ℂ) * (mSigma (E n) σ * mSigma (E n) σ'))⁻¹ := by
  rw [← Step2Kern_thetaKer_band]
  refine QopAlgebra_col_sum_thetaKerg (bandFM sz E) n σ σ' t _ (fun b => ?_)
    (zeroModeGen_isUnit_band sz E n σ σ' hE ht0 ht1) y
  exact zeroModeGen_colSum_band sz E n σ σ' b

end BandCorollaries

/-! ### 8. Compiled nonempty instances (target 7 (b)): `d = 3`, `sz0`, `n = 0`, `bandFM sz0 (fun _ => 0)`

`sz0` is the merged preflight sequence (`L_0 = 4`, `W_0 = 32`, `N = 2097152`, `lam_0 = 1/64`,
`RBM3D/Defs/Sizes.lean:260`), `E ≡ 0` (`|E| < 2`, `m(+) = i`), `σ = (+,-,+)` (`I_diff(σ) = {0, 1}`),
`τ = 1/2`.  Every deterministic hypothesis is discharged at these data: `ZeroModeGen_KerSums` by
`zeroModeGen_kerSums_band`, `Step2Gen_USemigroup` by `step2Gen_USemigroup_band`, `ZeroModeGen_WardCls` by
`zeroModeGen_wardCls_band`, `IsUnit (1 - t X)` by `zeroModeGen_isUnit_band`. -/

namespace ZeroModeGenInst

open RBM.Gauss.SizesInst

/-- `σ = (+,-,+)`: `I_diff(σ) = {0, 1}`. -/
private def zmgSigma : Fin 3 → Bool := ![true, false, true]

private noncomputable def zmgE : ℕ → ℝ := fun _ => 0
private noncomputable def zmgS : ℕ → ℝ := fun _ => 1 / 10
private noncomputable def zmgT : ℕ → ℝ := fun _ => 1 / 2
private def zmgK : ℕ → ℕ := fun _ => 4

/-- The point mass `δ₀` on `(Z_4^3)^3`. -/
private noncomputable def zmgDelta : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ := fun a => if a = 0 then 1 else 0

private theorem zmgDelta_ne : zmgDelta ≠ 0 := fun h => by
  have := congrFun h 0
  simp [zmgDelta] at this

private theorem zmgIdiff_card : (STIdiff zmgSigma).card = 2 := by decide

/-- Target 1 at `bandFM sz0`, `n = 0`. -/
example : ZeroModeGen_KerSums (bandFM sz0 zmgE) 0 := zeroModeGen_kerSums_band sz0 zmgE 0

/-- Target 2 (`Step2Gen_UN`): `Q^{(A)}`, `A = I_diff(σ)` (two indices), commutes with `U_{9/10, 99/100}` on the
nonzero tensor `δ₀`. -/
example : zmgDelta ≠ 0 ∧ (STIdiff zmgSigma).card = 2 ∧
    zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma)
        (Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (9 / 10) (99 / 100) zmgDelta)
      = Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (9 / 10) (99 / 100)
          (zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma) zmgDelta) :=
  ⟨zmgDelta_ne, zmgIdiff_card,
    zeroModeSet_UNg (bandFM sz0 zmgE) 0 (zeroModeGen_kerSums_band sz0 zmgE 0) zmgSigma _ _ _ _⟩

/-- Target 2 (`Step2Gen_ThetaN`), same data. -/
example : zmgDelta ≠ 0 ∧ (STIdiff zmgSigma).card = 2 ∧
    zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma)
        (Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (99 / 100) zmgDelta)
      = Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (99 / 100)
          (zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma) zmgDelta) :=
  ⟨zmgDelta_ne, zmgIdiff_card,
    zeroModeSet_ThetaNg (bandFM sz0 zmgE) 0 (zeroModeGen_kerSums_band sz0 zmgE 0) zmgSigma _ _ _⟩

/-- Target 3 at `bandStep2Mat sz0`: `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, `τ ≡ 3`, `j = 4` (`j ∧ τ = 3 ≤ K = 4`),
`σ = (+,-,+)`, `A = I_diff(σ)`, every sample `ω`; the sums have three terms. -/
example (ω : PathΩ sz0) :
    zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma)
        (AvecNg (bandStep2Mat sz0 zmgE) zmgS zmgT zmgK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)) zmgSigma ω) =
      Step2Gen_UN (bandStep2Mat sz0 zmgE).toFlowFM 0 zmgSigma (gridTime zmgS zmgT zmgK 0 0)
          (gridTime zmgS zmgT zmgK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
          (zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma)
            (AvecNg (bandStep2Mat sz0 zmgE) zmgS zmgT zmgK 0 0 zmgSigma ω)) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Step2Gen_UN (bandStep2Mat sz0 zmgE).toFlowFM 0 zmgSigma (gridTime zmgS zmgT zmgK 0 (i + 1))
            (gridTime zmgS zmgT zmgK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma)
              (predIncNg (bandStep2Mat sz0 zmgE) zmgS zmgT zmgK 0 i zmgSigma ω)) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Step2Gen_UN (bandStep2Mat sz0 zmgE).toFlowFM 0 zmgSigma (gridTime zmgS zmgT zmgK 0 (i + 1))
            (gridTime zmgS zmgT zmgK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma)
              (martIncNg (bandStep2Mat sz0 zmgE) zmgS zmgT zmgK 0 i zmgSigma ω)) :=
  zeroModeCalc_duhamel_inside_atg (bandStep2Mat sz0 zmgE) zmgS zmgT zmgK 0
    (step2Gen_USemigroup_band sz0 zmgE 0 (by norm_num [zmgE])) (zeroModeGen_kerSums_band sz0 zmgE 0)
    (by norm_num [zmgS]) (by norm_num [zmgS, zmgT]) (by norm_num [zmgT]) (by norm_num [zmgK]) zmgSigma
    (STIdiff zmgSigma) (fun _ => 3) 4 ω (by norm_num [zmgK])

/-- Target 4 (`zeroModeGen_loopL_wardFam`) at the Hermitian matrix `H_{1/2}(ω)` of the model on the block-product
index and `z = z_{1/2}`, `Im z = 1/2`. -/
example (ω : sz0.SeqΩ) :
    ZeroModeGen_WardFam 3 (sz0.L 0)
      ((2 * Complex.I * ((sz0.W 0 : ℕ) : ℂ) ^ 3 * ((zt 0 (1 / 2)).im : ℂ))⁻¹)
      (loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (sz0.seqHflow 0 (1 / 2) ω)) (zt 0 (1 / 2))) :=
  zeroModeGen_loopL_wardFam _ _ ((Sizes.gLoopFlow_seqHflow_isHermitian sz0 0 (1 / 2) ω).submatrix _)
    (by rw [← etaT_eq_zt_im]; exact (etaT_pos (by norm_num) (by norm_num)).ne')

/-- Target 4 (`zeroModeGen_newPQ`): `d = 3`, `m = 3`, `σ = (+,-,+)`, `A = ∅`, applied to the G-loops of the model at
`H_{1/2}(ω)`, `z_{1/2}`, every sample and every label vector; the Ward-family hypothesis is discharged. -/
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
    (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
    (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
    ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)),
      zeroModeSet 3 (sz0.L 0) ∅
          (fun a' => loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (sz0.seqHflow 0 (1 / 2) ω))
            (zt 0 (1 / 2)) (loopOf zmgSigma a')) a =
        zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff zmgSigma)
            (fun a' => loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (sz0.seqHflow 0 (1 / 2) ω))
              (zt 0 (1 / 2)) (loopOf zmgSigma a')) a +
          ∑ α : Fin ℓ, (ξ α : ℂ) *
              ((((sz0.L 0 : ℕ) : ℂ) ^ 3)⁻¹ * (2 * Complex.I * ((sz0.W 0 : ℕ) : ℂ) ^ 3 * ((zt 0 (1 / 2)).im : ℂ))⁻¹) ^
                (3 - k α) *
            zeroModeSet 3 (sz0.L 0) (A' α)
              (fun a' => loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (sz0.seqHflow 0 (1 / 2) ω))
                (zt 0 (1 / 2)) (loopOf (σ' α) a')) (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeGen_newPQ 3 3 zmgSigma ∅
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a =>
    h (sz0.L 0) _ _ (zeroModeGen_loopL_wardFam _ _
      ((Sizes.gLoopFlow_seqHflow_isHermitian sz0 0 (1 / 2) ω).submatrix _)
      (by rw [← etaT_eq_zt_im]; exact (etaT_pos (by norm_num) (by norm_num)).ne')) a⟩

/-- Target 5, the class at `bandFM sz0` (`|E n| < 2`). -/
example : ZeroModeGen_WardCls sz0 (bandFM sz0 zmgE) :=
  zeroModeGen_wardCls_band sz0 zmgE fun _ => by norm_num [zmgE]

/-- Target 5, `zeroModeCalc_LK_expansion_emptyg` (`A = ∅`) at `bandFM sz0`, `n = 0`, `τ = 1/2`, `m = 3`,
`σ = (+,-,+)`, every sample and every label vector. -/
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
    (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
    (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
    ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)),
      (bandFM sz0 zmgE).L 0 (1 / 2) zmgSigma a ω - (bandFM sz0 zmgE).K 0 (1 / 2) zmgSigma a =
        zeroModeSet 3 (sz0.L 0) (STIdiff zmgSigma)
            (fun a' => (bandFM sz0 zmgE).L 0 (1 / 2) zmgSigma a' ω - (bandFM sz0 zmgE).K 0 (1 / 2) zmgSigma a') a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                ((bandFM sz0 zmgE).eta 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α)
              (fun a' => (bandFM sz0 zmgE).L 0 (1 / 2) (σ' α) a' ω - (bandFM sz0 zmgE).K 0 (1 / 2) (σ' α) a')
              (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansion_emptyg 3 3 zmgSigma
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a =>
    h sz0 (bandFM sz0 zmgE) (zeroModeGen_wardCls_band sz0 zmgE fun _ => by norm_num [zmgE]) 0 (1 / 2)
      (by norm_num) (by norm_num) ω a⟩

/-- Target 5, `zeroModeCalc_LK_expansiong` for the nonempty `A = {2}` (`A ∪ I_diff(σ) = {0, 1, 2}`), same data. -/
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
    (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
    (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
    ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)),
      zeroModeSet 3 (sz0.L 0) ({2} : Finset (Fin 3))
          (fun a' => (bandFM sz0 zmgE).L 0 (1 / 2) zmgSigma a' ω - (bandFM sz0 zmgE).K 0 (1 / 2) zmgSigma a') a =
        zeroModeSet 3 (sz0.L 0) (({2} : Finset (Fin 3)) ∪ STIdiff zmgSigma)
            (fun a' => (bandFM sz0 zmgE).L 0 (1 / 2) zmgSigma a' ω - (bandFM sz0 zmgE).K 0 (1 / 2) zmgSigma a') a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                ((bandFM sz0 zmgE).eta 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α)
              (fun a' => (bandFM sz0 zmgE).L 0 (1 / 2) (σ' α) a' ω - (bandFM sz0 zmgE).K 0 (1 / 2) (σ' α) a')
              (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansiong 3 3 zmgSigma {2}
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a =>
    h sz0 (bandFM sz0 zmgE) (zeroModeGen_wardCls_band sz0 zmgE fun _ => by norm_num [zmgE]) 0 (1 / 2)
      (by norm_num) (by norm_num) ω a⟩

/-- Target 6, column sums of `Step2Gen_thetaKer` and `Step2Gen_uKer` at `bandFM sz0`, `n = 0`, charges
`(+,-)`, `s = 1/10`, `t = 1/2`: `c = m(+) m(-)`, `IsUnit (1 - t X)` from `zeroModeGen_isUnit_band`. -/
example (y : Zd 3 (sz0.L 0)) :
    ∑ x, Step2Gen_thetaKer (bandFM sz0 zmgE) 0 true false (1 / 2) x y =
        (mSigma 0 true * mSigma 0 false) * (1 - ((1 / 2 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false))⁻¹ ∧
      ∑ x, Step2Gen_uKer (bandFM sz0 zmgE) 0 true false (1 / 10) (1 / 2) x y =
        (1 - ((1 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) *
          (1 - ((1 / 2 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false))⁻¹ :=
  ⟨QopAlgebra_col_sum_thetaKerg (bandFM sz0 zmgE) 0 true false (1 / 2) _
      (zeroModeGen_colSum_band sz0 zmgE 0 true false)
      (zeroModeGen_isUnit_band sz0 zmgE 0 true false (by norm_num [zmgE]) (by norm_num) (by norm_num)) y,
    QopAlgebra_col_sum_uKerg (bandFM sz0 zmgE) 0 true false (1 / 10) (1 / 2) _
      (zeroModeGen_colSum_band sz0 zmgE 0 true false)
      (zeroModeGen_isUnit_band sz0 zmgE 0 true false (by norm_num [zmgE]) (by norm_num) (by norm_num)) y⟩

/-- The mollifier of `QopAlgebra` at `d = 3`, `L = 4`, three indices (`m = 2`), `g = lam_0`. -/
private noncomputable abbrev zmgVartheta : ℝ → (Fin (2 + 1) → Zd 3 (sz0.L 0)) → ℂ :=
  QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)

/-- The sum-zero tensor `𝒬_{1/2} 1`. -/
private noncomputable abbrev zmgA0 : (Fin (2 + 1) → Zd 3 (sz0.L 0)) → ℂ :=
  STQop (d := 3) zmgVartheta (1 / 2) (fun _ => (1 : ℂ))

private theorem zmgA0_sum (a₁ : Zd 3 (sz0.L 0)) : STPsum (d := 3) zmgA0 a₁ = 0 :=
  QopAlgebra_Psum_Qop zmgVartheta (fun a₁ => QopAlgebra_mollifier_sum 3 (sz0.L 0) 2 (sz0.lam 0) (1 / 2) a₁) _ a₁

/-- Target 6, `Θ^{(3)}` and `U^{(3)}` preserve the sum-zero tensor `𝒬_{1/2} 1` at `bandFM sz0`. -/
example (a₁ : Zd 3 (sz0.L 0)) :
    STPsum (d := 3) (Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) zmgA0) a₁ = 0 ∧
      STPsum (d := 3) (Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) zmgA0) a₁ = 0 :=
  ⟨QopAlgebra_ThetaN_sumZerog (bandFM sz0 zmgE) 0 (zeroModeGen_kerSums_band sz0 zmgE 0) zmgSigma _ _
      zmgA0_sum a₁,
    QopAlgebra_UN_sumZerog (bandFM sz0 zmgE) 0 (zeroModeGen_kerSums_band sz0 zmgE 0) zmgSigma _ _ _
      zmgA0_sum a₁⟩

/-- Target 6, linearity and the commutators at the same data (the tensor `δ₀`, the label `a = 0`). -/
example :
    Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) (fun b => zmgDelta b - zmgA0 b) 0 =
        Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) zmgDelta 0 -
          Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) zmgA0 0 ∧
      Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) (fun b => zmgDelta b - zmgA0 b) 0 =
        Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) zmgDelta 0 -
          Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) zmgA0 0 :=
  ⟨QopAlgebra_ThetaN_subg (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) zmgDelta zmgA0 0,
    QopAlgebra_UN_subg (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) zmgDelta zmgA0 0⟩

example :
    STQop (d := 3) zmgVartheta (1 / 2) (Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) zmgDelta) 0 -
        Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) (STQop (d := 3) zmgVartheta (1 / 2) zmgDelta) 0 =
      Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2)
          (fun b => STPsum (d := 3) zmgDelta (b 0) * zmgVartheta (1 / 2) b) 0 -
        STPsum (d := 3) (Step2Gen_ThetaN (bandFM sz0 zmgE) 0 zmgSigma (1 / 2) zmgDelta) ((0 : Fin 3 → Zd 3 (sz0.L 0)) 0) *
          zmgVartheta (1 / 2) 0 :=
  QopAlgebra_commutator_ThetaNg (bandFM sz0 zmgE) 0 zmgSigma zmgVartheta (1 / 2) zmgDelta 0

example :
    STQop (d := 3) zmgVartheta (1 / 2) (Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) zmgDelta) 0 -
        Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) (STQop (d := 3) zmgVartheta (1 / 2) zmgDelta) 0 =
      Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2)
          (fun b => STPsum (d := 3) zmgDelta (b 0) * zmgVartheta (1 / 2) b) 0 -
        STPsum (d := 3) (Step2Gen_UN (bandFM sz0 zmgE) 0 zmgSigma (1 / 10) (1 / 2) zmgDelta)
            ((0 : Fin 3 → Zd 3 (sz0.L 0)) 0) * zmgVartheta (1 / 2) 0 :=
  QopAlgebra_commutator_UNg (bandFM sz0 zmgE) 0 zmgSigma zmgVartheta (1 / 10) (1 / 2) zmgDelta 0

end ZeroModeGenInst

end RBM.BA

end
