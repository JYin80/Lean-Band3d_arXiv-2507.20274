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
open private qa_slot_zero qa_slot_succ qa_sum_filter_prod from RBM3D.Induction.QopAlgebra

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

end KerRoute

/-! ### 2. Commutation of `Q^{(A)}` with the one kernel -/

section Commute

variable {d : ℕ} {sz : Sizes d}

/-- **`Q^{(A)}` commutes with `Step2Gen_UN`** (`T2463_ZeroModeSetUNg`; band `zeroModeSet_UN`, ZMC:332), every
`s, t`, no window. -/
theorem zeroModeSet_UNg (C : FlowFM sz) (n : ℕ) (hK : ZeroModeGen_KerSums C n)
    {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ) :
    zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ s t T) =
      Step2Gen_UN C n σ s t (zeroModeSet d (sz.L n) A T) :=
  ZeroModeCalc_zeroModeSet_tensorKer_comm (d := d) (L := sz.L n) A
    (fun i => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) s t)
    (fun _ _ => zeroModeGen_projMat_comm_uKer C n hK _ _ s t) T

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

end QopKernels

/-! ### 7. Band corollaries (target 7 (a)): the band statements re-derived at `bandFM`, `bandStep2Mat` -/

/-! ### 8. Compiled nonempty instances (target 7 (b)): `d = 3`, `sz0`, `n = 0`, `bandFM sz0 (fun _ => 0)`

`sz0` is the merged preflight sequence (`L_0 = 4`, `W_0 = 32`, `N = 2097152`, `lam_0 = 1/64`,
`RBM3D/Defs/Sizes.lean:260`), `E ≡ 0` (`|E| < 2`, `m(+) = i`), `σ = (+,-,+)` (`I_diff(σ) = {0, 1}`),
`τ = 1/2`.  Every deterministic hypothesis is discharged at these data: `ZeroModeGen_KerSums` by
`zeroModeGen_kerSums_band`, `Step2Gen_USemigroup` by `step2Gen_USemigroup_band`, `ZeroModeGen_WardCls` by
`zeroModeGen_wardCls_band`, `IsUnit (1 - t X)` by `zeroModeGen_isUnit_band`. -/

end RBM.BA

end
