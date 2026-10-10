/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import RBM3D.Green.EntryCore

/-!
# `RBM3D.Universality.EigenInterlacing` (UN-10b, T2373): Cauchy interlacing, Stieltjes corollary

Port of `RBM2D/Universality/EigenInterlacing.lean` (588 lines; RBM2D `9e0f275`, file last touched
by `81fca44`; read-only), ticket T2373.  The file is generic (`n`, `m` arbitrary finite types), so
nothing depends on the dimension; `RBM.green` is the merged `Green/EntryCore.lean:34`.

* `eigenvalues₀_submatrix_interlace` -- Cauchy interlacing for a principal submatrix:
  `λ_i(A_e) ≤ λ_i(A)` and `λ_{i + (n - m)}(A) ≤ λ_i(A_e)`.
* `trace_green_submatrix_sub_le` -- `‖tr G_A(z) - tr G_{A_e}(z)‖ ≤ (n - m) (π + 1) / Im z`.

Changes against RBM2D: the private helpers `EI.x` are renamed `EigenInterlacing_x` (stem of the
ticket); `RBM.green_eq_spectral` (`RBM2D/Delocalization.lean:47`), the only `Delocalization` name
used, has no public RBM3D twin (private copies `Step1Good.lean:46`, `InjSum.lean:43`), so it is
copied once more here as `EigenInterlacing_green_eq_spectral`; `RBM.green_apply_self`,
`RBM.im_green_apply_self` are not used.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

noncomputable section

namespace RBM.Univ

open Matrix

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E}

private lemma EigenInterlacing_reInner_eq_sum {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (v : E) :
    RCLike.re (inner ℂ (T v) v) =
      ∑ j : Fin m, hT.eigenvalues hn j * ‖(hT.eigenvectorBasis hn).repr v j‖ ^ 2 := by
  have hb := (hT.eigenvectorBasis hn).repr.inner_map_map (T v) v
  rw [← hb, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hT.eigenvectorBasis_apply_self_apply hn v j, RCLike.inner_apply', map_mul (starRingEnd ℂ),
    RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul, RCLike.re_ofReal_mul, RCLike.re_ofReal_pow]

private lemma EigenInterlacing_norm_sq_eq_sum {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (v : E) :
    ‖v‖ ^ 2 = ∑ j : Fin m, ‖(hT.eigenvectorBasis hn).repr v j‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map v, EuclideanSpace.norm_sq_eq]

private lemma EigenInterlacing_repr_eq_zero_of_not_mem {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) {s : Finset (Fin m)} {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))))
    {j : Fin m} (hj : j ∉ s) :
    (hT.eigenvectorBasis hn).repr x j = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := ℂ)).mp hx
  rw [← hc, map_sum]
  simp only [map_smul]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkj : j ≠ k := fun h => hj (h ▸ hk)
  rw [(hT.eigenvectorBasis hn).repr_self k]
  simp [hkj]

private lemma EigenInterlacing_finrank_span_map_eigenvectorBasis
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    {m : ℕ} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = m) (s : Finset (Fin m))
    {f : E →ₗ[ℂ] E'} (hf : Function.Injective f) :
    Module.finrank ℂ (Submodule.span ℂ (f '' ((hT.eigenvectorBasis hn) '' (s : Set (Fin m)))))
      = s.card := by
  classical
  have hli : LinearIndependent ℂ (f ∘ (hT.eigenvectorBasis hn) ∘ ((↑) : s → Fin m)) :=
    ((hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp
      ((↑) : s → Fin m) Subtype.val_injective).map' f (LinearMap.ker_eq_bot.mpr hf)
  have hrange : Set.range (f ∘ (hT.eigenvectorBasis hn) ∘ ((↑) : s → Fin m))
      = f '' ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨(hT.eigenvectorBasis hn) (k : Fin m), ⟨(k : Fin m), k.2, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  have hfr := finrank_span_eq_card hli
  rw [hrange] at hfr
  rw [hfr, Fintype.card_coe]

private lemma EigenInterlacing_finrank_span_eigenvectorBasis {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (s : Finset (Fin m)) :
    Module.finrank ℂ (Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))))
      = s.card := by
  have h := EigenInterlacing_finrank_span_map_eigenvectorBasis (f := LinearMap.id) hT hn s Function.injective_id
  rw [show ((LinearMap.id : E →ₗ[ℂ] E) '' ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))))
      = (hT.eigenvectorBasis hn) '' (s : Set (Fin m)) from Set.image_id _] at h
  exact h

private lemma EigenInterlacing_rayleigh_ge_of_mem_Iic {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))) :
    hT.eigenvalues hn i * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (T x) x) := by
  rw [EigenInterlacing_reInner_eq_sum hT hn x, EigenInterlacing_norm_sq_eq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ (Finset.Iic i)
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hj))
      (sq_nonneg _)
  · rw [EigenInterlacing_repr_eq_zero_of_not_mem hT hn hx hj]; simp

private lemma EigenInterlacing_rayleigh_le_of_mem_Ici {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Ici i : Set (Fin m)))) :
    RCLike.re (inner ℂ (T x) x) ≤ hT.eigenvalues hn i * ‖x‖ ^ 2 := by
  rw [EigenInterlacing_reInner_eq_sum hT hn x, EigenInterlacing_norm_sq_eq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ (Finset.Ici i)
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj))
      (sq_nonneg _)
  · rw [EigenInterlacing_repr_eq_zero_of_not_mem hT hn hx hj]; simp

private lemma EigenInterlacing_exists_ne_zero_mem_inf_of_finrank_lt_add
    {W1 W2 : Submodule ℂ E} (h : Module.finrank ℂ E < Module.finrank ℂ W1 + Module.finrank ℂ W2) :
    ∃ x ∈ W1 ⊓ W2, x ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hbot : W1 ⊓ W2 = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq W1 W2
  rw [hbot, finrank_bot, add_zero] at hfin
  have hsup_le : Module.finrank ℂ (↥(W1 ⊔ W2)) ≤ Module.finrank ℂ E := Submodule.finrank_le _
  omega

end Abstract

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem EigenInterlacing_sym {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr hA

private lemma EigenInterlacing_eigenvalues₀_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hA.eigenvalues₀ = (EigenInterlacing_sym hA).eigenvalues finrank_euclideanSpace := rfl

end Matrices

section Push

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

private noncomputable def EigenInterlacing_extMat (e : m ↪ n) : Matrix n m ℂ :=
  Matrix.of (fun k j => if k = e j then (1:ℂ) else 0)

private noncomputable def EigenInterlacing_push (e : m ↪ n) :
    EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n :=
  Matrix.toEuclideanLin (EigenInterlacing_extMat e)

omit [Fintype m] in
private lemma EigenInterlacing_extMat_conjTranspose_mul_self (e : m ↪ n) :
    (EigenInterlacing_extMat e)ᴴ * (EigenInterlacing_extMat e) = (1 : Matrix m m ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, EigenInterlacing_extMat, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    have : ∀ k : n, star (if k = e i then (1:ℂ) else 0) * (if k = e i then (1:ℂ) else 0)
        = if k = e i then (1:ℂ) else 0 := fun k => by by_cases h : k = e i <;> simp [h]
    simp_rw [this]
    exact Finset.sum_ite_eq' Finset.univ (e i) (fun _ => (1:ℂ)) ▸ by simp
  · rw [Matrix.one_apply_ne hij]
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with h1 h2 h2
    · exact absurd (e.injective (h1 ▸ h2 : e i = e j)) hij
    · simp
    · simp
    · simp

omit [Fintype m] [DecidableEq m] in
private lemma EigenInterlacing_extMat_conjTranspose_mul_mul (e : m ↪ n) (A : Matrix n n ℂ) :
    (EigenInterlacing_extMat e)ᴴ * A * (EigenInterlacing_extMat e) = A.submatrix e e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, EigenInterlacing_extMat, Matrix.of_apply,
    Matrix.submatrix_apply]
  have hinner : ∀ l : n, (∑ k : n, star (if k = e i then (1:ℂ) else 0) * A k l) = A (e i) l := by
    intro l
    have : ∀ k : n, star (if k = e i then (1:ℂ) else 0) * A k l
        = if k = e i then A (e i) l else 0 := fun k => by by_cases h : k = e i <;> simp [h]
    simp_rw [this]
    exact Finset.sum_ite_eq' Finset.univ (e i) (fun _ => A (e i) l) ▸ by simp
  simp_rw [hinner]
  have : ∀ l : n, A (e i) l * (if l = e j then (1:ℂ) else 0)
      = if l = e j then A (e i) (e j) else 0 := fun l => by by_cases h : l = e j <;> simp [h]
  simp_rw [this]
  exact Finset.sum_ite_eq' Finset.univ (e j) (fun _ => A (e i) (e j)) ▸ by simp

private lemma EigenInterlacing_inner_toEuclideanLin_push (e : m ↪ n) (A : Matrix n n ℂ)
    (w : EuclideanSpace ℂ m) :
    (inner ℂ (Matrix.toEuclideanLin A (EigenInterlacing_push e w)) (EigenInterlacing_push e w) : ℂ)
      = inner ℂ (Matrix.toEuclideanLin (A.submatrix e e) w) w := by
  unfold EigenInterlacing_push
  have h1 : Matrix.toEuclideanLin A (Matrix.toEuclideanLin (EigenInterlacing_extMat e) w)
      = Matrix.toEuclideanLin (A * EigenInterlacing_extMat e) w :=
    LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2 A (EigenInterlacing_extMat e)).symm w
  rw [h1]
  rw [← LinearMap.adjoint_inner_left (Matrix.toEuclideanLin (EigenInterlacing_extMat e))]
  have h2 : (Matrix.toEuclideanLin (EigenInterlacing_extMat e)).adjoint
      = Matrix.toEuclideanLin (EigenInterlacing_extMat e)ᴴ :=
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (EigenInterlacing_extMat e)).symm
  rw [h2]
  have h3 : Matrix.toEuclideanLin (EigenInterlacing_extMat e)ᴴ (Matrix.toEuclideanLin (A * EigenInterlacing_extMat e) w)
      = Matrix.toEuclideanLin ((EigenInterlacing_extMat e)ᴴ * (A * EigenInterlacing_extMat e)) w :=
    LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2 (EigenInterlacing_extMat e)ᴴ (A * EigenInterlacing_extMat e)).symm w
  rw [h3, ← Matrix.mul_assoc, EigenInterlacing_extMat_conjTranspose_mul_mul]

private lemma EigenInterlacing_norm_push (e : m ↪ n) (w : EuclideanSpace ℂ m) :
    ‖EigenInterlacing_push e w‖ = ‖w‖ := by
  have hinner : (inner ℂ (EigenInterlacing_push e w) (EigenInterlacing_push e w) : ℂ) = inner ℂ w w := by
    unfold EigenInterlacing_push
    have h3 : Matrix.toEuclideanLin (EigenInterlacing_extMat e)ᴴ (Matrix.toEuclideanLin (EigenInterlacing_extMat e) w)
        = Matrix.toEuclideanLin ((EigenInterlacing_extMat e)ᴴ * (EigenInterlacing_extMat e)) w :=
      LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2 (EigenInterlacing_extMat e)ᴴ (EigenInterlacing_extMat e)).symm w
    rw [← LinearMap.adjoint_inner_left (Matrix.toEuclideanLin (EigenInterlacing_extMat e)),
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (EigenInterlacing_extMat e)).symm, h3,
      EigenInterlacing_extMat_conjTranspose_mul_self, Matrix.toLpLin_one]
    rfl
  have hre := congrArg RCLike.re hinner
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at hre
  nlinarith [norm_nonneg (EigenInterlacing_push e w), norm_nonneg w, hre]

private lemma EigenInterlacing_push_injective (e : m ↪ n) : Function.Injective (EigenInterlacing_push e) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have := EigenInterlacing_norm_push e w
  rw [hw, norm_zero] at this
  exact norm_eq_zero.mp this.symm

end Push

theorem eigenvalues₀_submatrix_interlace {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (e : m ↪ n)
    (i : ℕ) (hi : i < Fintype.card m) :
    (hA.submatrix e).eigenvalues₀ ⟨i, hi⟩ ≤
        hA.eigenvalues₀ ⟨i, hi.trans_le (Fintype.card_le_of_embedding e)⟩ ∧
      hA.eigenvalues₀ ⟨i + (Fintype.card n - Fintype.card m), by
          have := Fintype.card_le_of_embedding e; omega⟩ ≤
        (hA.submatrix e).eigenvalues₀ ⟨i, hi⟩ := by
  classical
  set B := A.submatrix e e with hB_def
  have hB : B.IsHermitian := hA.submatrix e
  set hnm : Fin (Fintype.card m) := ⟨i, hi⟩ with hnm_def
  have hcardmn : Fintype.card m ≤ Fintype.card n := Fintype.card_le_of_embedding e
  have hiN : i < Fintype.card n := hi.trans_le hcardmn
  set hnn : Fin (Fintype.card n) := ⟨i, hiN⟩ with hnn_def
  set r := Fintype.card n - Fintype.card m with hr_def
  have hiRN : i + r < Fintype.card n := by have := hcardmn; omega
  set hnn2 : Fin (Fintype.card n) := ⟨i + r, hiRN⟩ with hnn2_def
  have hTB := EigenInterlacing_sym hB
  have hTA := EigenInterlacing_sym hA
  set hnB : Module.finrank ℂ (EuclideanSpace ℂ m) = Fintype.card m := finrank_euclideanSpace
  set hnA : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
  have hAle_eq : ∀ i' : Fin (Fintype.card n), hTA.eigenvalues hnA i' = hA.eigenvalues₀ i' := by
    intro i'; rw [EigenInterlacing_eigenvalues₀_eq hA]
  have hBle_eq : ∀ i' : Fin (Fintype.card m), hTB.eigenvalues hnB i' = hB.eigenvalues₀ i' := by
    intro i'; rw [EigenInterlacing_eigenvalues₀_eq hB]
  have key1 : hB.eigenvalues₀ hnm ≤ hA.eigenvalues₀ hnn := by
    rw [← hBle_eq, ← hAle_eq]
    set W1 : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (EigenInterlacing_push e '' (hTB.eigenvectorBasis hnB
        '' (Finset.Iic hnm : Set (Fin (Fintype.card m))))) with hW1_def
    set W2 : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (hTA.eigenvectorBasis hnA
        '' (Finset.Ici hnn : Set (Fin (Fintype.card n)))) with hW2_def
    have hW1dim : Module.finrank ℂ W1 = i + 1 := by
      rw [hW1_def, EigenInterlacing_finrank_span_map_eigenvectorBasis hTB hnB (Finset.Iic hnm)
        (EigenInterlacing_push_injective e), Fin.card_Iic]
    have hW2dim : Module.finrank ℂ W2 = Fintype.card n - i := by
      rw [hW2_def, EigenInterlacing_finrank_span_eigenvectorBasis hTA hnA (Finset.Ici hnn), Fin.card_Ici]
    have hdimlt :
        Module.finrank ℂ (EuclideanSpace ℂ n) < Module.finrank ℂ W1 + Module.finrank ℂ W2 := by
      rw [finrank_euclideanSpace, hW1dim, hW2dim]; omega
    obtain ⟨x, hxmem, hx0⟩ := EigenInterlacing_exists_ne_zero_mem_inf_of_finrank_lt_add hdimlt
    obtain ⟨hxW1, hxW2⟩ := Submodule.mem_inf.mp hxmem
    rw [hW1_def, ← Submodule.map_span] at hxW1
    obtain ⟨w, hwmem, hweq⟩ := Submodule.mem_map.mp hxW1
    have hw0 : w ≠ 0 := by
      intro h; apply hx0; rw [← hweq, h]; exact map_zero _
    have hBrayleigh := EigenInterlacing_rayleigh_ge_of_mem_Iic hTB hnB hnm hwmem
    have hAle := EigenInterlacing_rayleigh_le_of_mem_Ici hTA hnA hnn hxW2
    have hnormeq : ‖x‖ = ‖w‖ := by rw [← hweq]; exact EigenInterlacing_norm_push e w
    rw [hnormeq] at hAle
    have hinnereq : RCLike.re (inner ℂ (Matrix.toEuclideanLin A x) x)
        = RCLike.re (inner ℂ (Matrix.toEuclideanLin B w) w) := by
      have hh := EigenInterlacing_inner_toEuclideanLin_push e A w
      rw [hweq] at hh
      exact congrArg RCLike.re hh
    have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw0) 2
    have hchain : hTB.eigenvalues hnB hnm * ‖w‖ ^ 2 ≤ hTA.eigenvalues hnA hnn * ‖w‖ ^ 2 :=
      hBrayleigh.trans (hinnereq.symm.trans_le hAle)
    exact le_of_mul_le_mul_right hchain hwpos
  have key2 : hA.eigenvalues₀ hnn2 ≤ hB.eigenvalues₀ hnm := by
    rw [← hBle_eq, ← hAle_eq]
    set W1 : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (EigenInterlacing_push e '' (hTB.eigenvectorBasis hnB
        '' (Finset.Ici hnm : Set (Fin (Fintype.card m))))) with hW1_def
    set W2 : Submodule ℂ (EuclideanSpace ℂ n) :=
      Submodule.span ℂ (hTA.eigenvectorBasis hnA
        '' (Finset.Iic hnn2 : Set (Fin (Fintype.card n)))) with hW2_def
    have hW1dim : Module.finrank ℂ W1 = Fintype.card m - i := by
      rw [hW1_def, EigenInterlacing_finrank_span_map_eigenvectorBasis hTB hnB (Finset.Ici hnm)
        (EigenInterlacing_push_injective e), Fin.card_Ici]
    have hW2dim : Module.finrank ℂ W2 = i + r + 1 := by
      rw [hW2_def, EigenInterlacing_finrank_span_eigenvectorBasis hTA hnA (Finset.Iic hnn2), Fin.card_Iic]
    have hdimlt :
        Module.finrank ℂ (EuclideanSpace ℂ n) < Module.finrank ℂ W1 + Module.finrank ℂ W2 := by
      rw [finrank_euclideanSpace, hW1dim, hW2dim]; omega
    obtain ⟨x, hxmem, hx0⟩ := EigenInterlacing_exists_ne_zero_mem_inf_of_finrank_lt_add hdimlt
    obtain ⟨hxW1, hxW2⟩ := Submodule.mem_inf.mp hxmem
    rw [hW1_def, ← Submodule.map_span] at hxW1
    obtain ⟨w, hwmem, hweq⟩ := Submodule.mem_map.mp hxW1
    have hw0 : w ≠ 0 := by
      intro h; apply hx0; rw [← hweq, h]; exact map_zero _
    have hBrayleigh := EigenInterlacing_rayleigh_le_of_mem_Ici hTB hnB hnm hwmem
    have hAge := EigenInterlacing_rayleigh_ge_of_mem_Iic hTA hnA hnn2 hxW2
    have hnormeq : ‖x‖ = ‖w‖ := by rw [← hweq]; exact EigenInterlacing_norm_push e w
    rw [hnormeq] at hAge
    have hinnereq : RCLike.re (inner ℂ (Matrix.toEuclideanLin A x) x)
        = RCLike.re (inner ℂ (Matrix.toEuclideanLin B w) w) := by
      have hh := EigenInterlacing_inner_toEuclideanLin_push e A w
      rw [hweq] at hh
      exact congrArg RCLike.re hh
    have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw0) 2
    have hchain : hTA.eigenvalues hnA hnn2 * ‖w‖ ^ 2 ≤ hTB.eigenvalues hnB hnm * ‖w‖ ^ 2 :=
      hAge.trans (hinnereq.trans_le hBrayleigh)
    exact le_of_mul_le_mul_right hchain hwpos
  exact ⟨key1, key2⟩


section Trace

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Spectral decomposition of the Green's function `(H - z)⁻¹` (RBM2D `Delocalization.lean:47`,
`green_eq_spectral`; copy of the private `InjSum_green_eq_spectral`, `RBM3D/Universality/InjSum.lean:43`). -/
private lemma EigenInterlacing_green_eq_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) :
    RBM.green H z = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)
      * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun l => (hH.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hz1 : (z • 1 : Matrix n n ℂ) = U * diagonal (fun _ => z) * star U := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU']
  have hsub : H - z • 1 = U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U := by
    rw [hz1]
    conv_lhs => rw [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U
        * (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹) * star U)
      = U * (diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * (star U * U)
          * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => ((hH.eigenvalues l : ℂ) - z) * ((hH.eigenvalues l : ℂ) - z)⁻¹)
            = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

private lemma EigenInterlacing_trace_green_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    (RBM.green A z).trace = ∑ i : Fin (Fintype.card n), ((hA.eigenvalues₀ i : ℂ) - z)⁻¹ := by
  have hzne : ∀ l, (hA.eigenvalues l : ℂ) ≠ z := by
    intro l h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [EigenInterlacing_green_eq_spectral hA hzne]
  rw [Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
    (fun i => ((hA.eigenvalues₀ i : ℂ) - z)⁻¹)

private lemma EigenInterlacing_resolvent_hasDerivAt (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y:ℂ) - z)⁻¹) (-(1:ℂ) / ((x:ℂ) - z) ^ 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y:ℂ) - z) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const z
  have hne : (x:ℂ) - z ≠ 0 := by
    intro h
    apply hz
    have : ((x:ℂ) - z).im = 0 := by rw [h]; simp
    simpa using this
  exact h1.inv hne

private lemma EigenInterlacing_theta_hasDerivAt (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan ((y - z.re)/z.im)) (z.im/((x-z.re)^2+z.im^2)) x := by
  have hlin : HasDerivAt (fun y : ℝ => (y - z.re)/z.im) (1/z.im) x := by
    have := ((hasDerivAt_id x).sub_const z.re).div_const z.im
    simpa using this
  have harc := hlin.arctan
  have heq : 1 / (1 + ((x - z.re)/z.im) ^ 2) * (1/z.im) = z.im/((x-z.re)^2+z.im^2) := by
    field_simp
    ring
  rwa [heq] at harc

private lemma EigenInterlacing_norm_resolvent_deriv (z : ℂ) (x : ℝ) :
    ‖(-(1:ℂ) / ((x:ℂ) - z) ^ 2)‖ = 1/((x-z.re)^2+z.im^2) := by
  rw [norm_div, norm_neg, norm_one, norm_pow]
  congr 1
  rw [Complex.sq_norm]
  rw [Complex.normSq_apply]
  simp
  ring

private lemma EigenInterlacing_norm_resolvent_sub_le (z : ℂ) (hz : 0 < z.im) (a b : ℝ) (hab : b ≤ a) :
    ‖((a:ℂ)-z)⁻¹ - ((b:ℂ)-z)⁻¹‖
      ≤ (Real.arctan ((a - z.re)/z.im) - Real.arctan ((b - z.re)/z.im)) / z.im := by
  have hzne : z.im ≠ 0 := ne_of_gt hz
  have hfderiv : ∀ x ∈ Set.uIcc b a, HasDerivAt (fun y : ℝ => ((y:ℂ) - z)⁻¹)
      (-(1:ℂ) / ((x:ℂ) - z) ^ 2) x := fun x _ => EigenInterlacing_resolvent_hasDerivAt z hzne x
  have hfcont : ContinuousOn (fun x : ℝ => (-(1:ℂ) / ((x:ℂ) - z) ^ 2)) (Set.uIcc b a) := by
    apply ContinuousOn.div continuousOn_const
    · exact (Complex.continuous_ofReal.sub continuous_const).pow 2 |>.continuousOn
    · intro x _ h
      apply hzne
      have hx : (x:ℂ) - z = 0 := sq_eq_zero_iff.mp h
      have : ((x:ℂ) - z).im = 0 := by rw [hx]; simp
      simpa using this
  have hFTC : ∫ x in b..a, (-(1:ℂ) / ((x:ℂ) - z) ^ 2)
      = ((a:ℂ) - z)⁻¹ - ((b:ℂ) - z)⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hfderiv (hfcont.intervalIntegrable)
  rw [← hFTC]
  have hgderiv : ∀ x ∈ Set.uIcc b a, HasDerivAt (fun y : ℝ => Real.arctan ((y - z.re)/z.im))
      (z.im/((x-z.re)^2+z.im^2)) x := fun x _ => EigenInterlacing_theta_hasDerivAt z hzne x
  have hgcont : ContinuousOn (fun x : ℝ => z.im/((x-z.re)^2+z.im^2)) (Set.uIcc b a) := by
    apply Continuous.continuousOn
    apply continuous_const.div
    · exact (continuous_id.sub continuous_const).pow 2 |>.add continuous_const
    · intro x
      positivity
  have hGTC : ∫ x in b..a, z.im/((x-z.re)^2+z.im^2)
      = Real.arctan ((a - z.re)/z.im) - Real.arctan ((b - z.re)/z.im) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hgderiv (hgcont.intervalIntegrable)
  rw [← hGTC, ← intervalIntegral.integral_div]
  calc ‖∫ x in b..a, (-(1:ℂ) / ((x:ℂ) - z) ^ 2)‖
      ≤ ∫ x in b..a, ‖(-(1:ℂ) / ((x:ℂ) - z) ^ 2)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in b..a, (z.im/((x-z.re)^2+z.im^2))/z.im := by
        apply intervalIntegral.integral_mono_on hab
        · exact hfcont.norm.intervalIntegrable
        · exact hgcont.div_const _ |>.intervalIntegrable
        · intro x _
          rw [EigenInterlacing_norm_resolvent_deriv, div_div]
          have hpos : (0:ℝ) < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
          rw [le_div_iff₀ (by positivity)]
          have hcancel : 1 / ((x - z.re) ^ 2 + z.im ^ 2) * (((x - z.re) ^ 2 + z.im ^ 2) * z.im)
              = z.im := by field_simp
          rw [hcancel]

private lemma EigenInterlacing_norm_resolvent_le (z : ℂ) (hz : 0 < z.im) (x : ℝ) :
    ‖((x:ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
  rw [norm_inv, inv_eq_one_div]
  have himle : z.im ≤ ‖(x:ℂ) - z‖ := by
    have h1 : |((x:ℂ)-z).im| ≤ ‖(x:ℂ)-z‖ := Complex.abs_im_le_norm _
    have h2 : ((x:ℂ)-z).im = -z.im := by simp
    rw [h2, abs_neg, abs_of_pos hz] at h1
    exact h1
  exact one_div_le_one_div_of_le hz himle

end Trace


section TraceMain

private lemma EigenInterlacing_sum_range_swap_eq (g : ℕ → ℝ) (p q : ℕ) :
    (∑ k ∈ Finset.range p, g k) - (∑ k ∈ Finset.range p, g (k+q))
      = (∑ k ∈ Finset.range q, g k) - (∑ k ∈ Finset.range q, g (k+p)) := by
  have h1 : ∑ k ∈ Finset.range (p+q), g k
      = (∑ k ∈ Finset.range p, g k) + (∑ k ∈ Finset.range q, g (p+k)) :=
    Finset.sum_range_add g p q
  have h2 : ∑ k ∈ Finset.range (q+p), g k
      = (∑ k ∈ Finset.range q, g k) + (∑ k ∈ Finset.range p, g (q+k)) :=
    Finset.sum_range_add g q p
  rw [add_comm q p] at h2
  rw [h1] at h2
  have hgq : ∀ k, g (p+k) = g (k+p) := fun k => by rw [add_comm]
  have hgp : ∀ k, g (q+k) = g (k+q) := fun k => by rw [add_comm]
  simp_rw [hgq] at h2
  simp_rw [hgp] at h2
  linarith

theorem trace_green_submatrix_sub_le {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (e : m ↪ n)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(RBM.green A z).trace - (RBM.green (A.submatrix e e) z).trace‖ ≤
      ((Fintype.card n - Fintype.card m : ℕ) : ℝ) * (Real.pi + 1) / z.im := by
  classical
  set B := A.submatrix e e with hB_def
  have hB : B.IsHermitian := hA.submatrix e
  have hcardmn : Fintype.card m ≤ Fintype.card n := Fintype.card_le_of_embedding e
  set r := Fintype.card n - Fintype.card m with hr_def
  have hcardeq : Fintype.card n = Fintype.card m + r := by omega
  set lam : ℕ → ℝ := fun k => if h : k < Fintype.card n then hA.eigenvalues₀ ⟨k,h⟩ else 0
    with hlam_def
  set mu : ℕ → ℝ := fun k => if h : k < Fintype.card m then hB.eigenvalues₀ ⟨k,h⟩ else 0
    with hmu_def
  set F : ℝ → ℂ := fun x => ((x:ℂ) - z)⁻¹ with hF_def
  set θ : ℝ → ℝ := fun x => Real.arctan ((x - z.re)/z.im) with hθ_def
  have hAtr : (RBM.green A z).trace = ∑ k ∈ Finset.range (Fintype.card n), F (lam k) := by
    rw [EigenInterlacing_trace_green_eq_sum hA hz]
    rw [← Fin.sum_univ_eq_sum_range (fun k => F (lam k)) (Fintype.card n)]
    apply Finset.sum_congr rfl
    intro i _
    have hh : lam (i:ℕ) = hA.eigenvalues₀ i := by
      rw [hlam_def]; simp [i.2]
    rw [hh]
  have hBtr : (RBM.green B z).trace = ∑ k ∈ Finset.range (Fintype.card m), F (mu k) := by
    rw [EigenInterlacing_trace_green_eq_sum hB hz]
    rw [← Fin.sum_univ_eq_sum_range (fun k => F (mu k)) (Fintype.card m)]
    apply Finset.sum_congr rfl
    intro i _
    have hh : mu (i:ℕ) = hB.eigenvalues₀ i := by
      rw [hmu_def]; simp [i.2]
    rw [hh]
  have hAsplit : ∑ k ∈ Finset.range (Fintype.card n), F (lam k)
      = (∑ k ∈ Finset.range (Fintype.card m), F (lam k))
        + ∑ k ∈ Finset.range r, F (lam (Fintype.card m + k)) := by
    rw [hcardeq]; exact Finset.sum_range_add (fun k => F (lam k)) (Fintype.card m) r
  have hdiff : (RBM.green A z).trace - (RBM.green B z).trace
      = (∑ k ∈ Finset.range (Fintype.card m), (F (lam k) - F (mu k)))
        + ∑ k ∈ Finset.range r, F (lam (Fintype.card m + k)) := by
    rw [hAtr, hBtr, hAsplit, Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  have htail_bound : ‖∑ k ∈ Finset.range r, F (lam (Fintype.card m + k))‖
      ≤ (r:ℝ) / z.im := by
    calc ‖∑ k ∈ Finset.range r, F (lam (Fintype.card m + k))‖
        ≤ ∑ k ∈ Finset.range r, ‖F (lam (Fintype.card m + k))‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range r, (1/z.im) := by
          apply Finset.sum_le_sum
          intro k _
          exact EigenInterlacing_norm_resolvent_le z hz _
      _ = (r:ℝ) / z.im := by rw [Finset.sum_const, Finset.card_range]; ring
  have hkey : ∀ k < Fintype.card m, mu k ≤ lam k ∧ lam (k + r) ≤ mu k := by
    intro k hk
    have hint := eigenvalues₀_submatrix_interlace hA e k hk
    have hmuk : mu k = hB.eigenvalues₀ ⟨k, hk⟩ := by rw [hmu_def]; simp [hk]
    have hlamk : lam k = hA.eigenvalues₀ ⟨k, hk.trans_le hcardmn⟩ := by
      rw [hlam_def]; simp [hk.trans_le hcardmn]
    have hkrn : k + r < Fintype.card n := by omega
    have hlamkr : lam (k + r) = hA.eigenvalues₀ ⟨k + r, hkrn⟩ := by
      rw [hlam_def]; simp [hkrn]
    refine ⟨?_, ?_⟩
    · rw [hmuk, hlamk]; exact hint.1
    · rw [hlamkr, hmuk]; exact hint.2
  have hmono : ∀ k < Fintype.card m, θ (lam (k+r)) ≤ θ (mu k) := by
    intro k hk
    apply Real.arctan_mono
    have := (hkey k hk).2
    gcongr
  have hmain_bound : ‖∑ k ∈ Finset.range (Fintype.card m), (F (lam k) - F (mu k))‖
      ≤ (∑ k ∈ Finset.range (Fintype.card m), (θ (lam k) - θ (mu k))) / z.im := by
    calc ‖∑ k ∈ Finset.range (Fintype.card m), (F (lam k) - F (mu k))‖
        ≤ ∑ k ∈ Finset.range (Fintype.card m), ‖F (lam k) - F (mu k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (Fintype.card m), (θ (lam k) - θ (mu k)) / z.im := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_range] at hk
          exact EigenInterlacing_norm_resolvent_sub_le z hz (lam k) (mu k) (hkey k hk).1
      _ = (∑ k ∈ Finset.range (Fintype.card m), (θ (lam k) - θ (mu k))) / z.im := by
          rw [Finset.sum_div]
  have hswap_bound : (∑ k ∈ Finset.range (Fintype.card m), (θ (lam k) - θ (mu k)))
      ≤ ∑ k ∈ Finset.range r, (θ (lam k) - θ (lam (Fintype.card m + k))) := by
    calc ∑ k ∈ Finset.range (Fintype.card m), (θ (lam k) - θ (mu k))
        ≤ ∑ k ∈ Finset.range (Fintype.card m), (θ (lam k) - θ (lam (k+r))) := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_range] at hk
          have := hmono k hk
          linarith
      _ = ∑ k ∈ Finset.range (Fintype.card m), θ (lam k)
            - ∑ k ∈ Finset.range (Fintype.card m), θ (lam (k+r)) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ k ∈ Finset.range r, θ (lam k) - ∑ k ∈ Finset.range r, θ (lam (k + Fintype.card m)) :=
          EigenInterlacing_sum_range_swap_eq (fun k => θ (lam k)) (Fintype.card m) r
      _ = ∑ k ∈ Finset.range r, (θ (lam k) - θ (lam (Fintype.card m + k))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k _
          rw [add_comm k (Fintype.card m)]
  have hpi_bound : ∑ k ∈ Finset.range r, (θ (lam k) - θ (lam (Fintype.card m + k)))
      ≤ (r:ℝ) * Real.pi := by
    calc ∑ k ∈ Finset.range r, (θ (lam k) - θ (lam (Fintype.card m + k)))
        ≤ ∑ _k ∈ Finset.range r, Real.pi := by
          apply Finset.sum_le_sum
          intro k _
          have h1 := Real.arctan_lt_pi_div_two ((lam k - z.re)/z.im)
          have h2 := Real.neg_pi_div_two_lt_arctan ((lam (Fintype.card m + k) - z.re)/z.im)
          simp only [hθ_def]
          linarith
      _ = (r:ℝ) * Real.pi := by rw [Finset.sum_const, Finset.card_range]; ring
  calc ‖(∑ k ∈ Finset.range (Fintype.card m), (F (lam k) - F (mu k)))
        + ∑ k ∈ Finset.range r, F (lam (Fintype.card m + k))‖
      ≤ ‖∑ k ∈ Finset.range (Fintype.card m), (F (lam k) - F (mu k))‖
        + ‖∑ k ∈ Finset.range r, F (lam (Fintype.card m + k))‖ := norm_add_le _ _
    _ ≤ (∑ k ∈ Finset.range (Fintype.card m), (θ (lam k) - θ (mu k))) / z.im + (r:ℝ) / z.im := by
        gcongr
    _ ≤ ((r:ℝ) * Real.pi) / z.im + (r:ℝ) / z.im := by
        gcongr
        exact hswap_bound.trans hpi_bound
    _ = (r:ℝ) * (Real.pi + 1) / z.im := by ring

end TraceMain

/-! ## Compiled nonempty instances (ticket target 3; CLAUDE.md §4 step 2)

Data: `A = tridiag(1, 2, 1)`, a `3 × 3` Hermitian matrix with three distinct eigenvalues (the three
eigenpairs `A3_eigenpairs`, with eigenvalues `2 + √2, 2, 2 - √2`, are checked below), and its `2 × 2`
minor `[[2, 1], [1, 2]]` (delete row and column `0`, `e = Fin.succEmb 2 : Fin 2 ↪ Fin 3`, eigenpairs
`(1, 1) ↦ 3`, `(1, -1) ↦ 1`); `z = 3/10 + i`.  Both theorems are applied with every hypothesis
discharged; the conclusion of the interlacing stays an inequality between the `eigenvalues₀` of these
two matrices (the spectrum of `A3` is not evaluated in Lean). -/

namespace EigenInterlacingInst

/-- `tridiag(1, 2, 1)` on `Fin 3`. -/
def A3 : Matrix (Fin 3) (Fin 3) ℂ := !![2, 1, 0; 1, 2, 1; 0, 1, 2]

theorem A3_isHermitian : A3.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A3, Matrix.conjTranspose_apply]

/-- The minor is `[[2, 1], [1, 2]]` (the principal submatrix on `{1, 2}`). -/
theorem A3_minor : A3.submatrix (Fin.succEmb 2) (Fin.succEmb 2) = !![2, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A3, Fin.succEmb]

set_option linter.flexible false in
/-- Three eigenpairs of `A3` with pairwise distinct eigenvalues `2 + √2, 2, 2 - √2` (so the `3 × 3`
matrix has three distinct eigenvalues), and the two eigenpairs of the minor. -/
theorem A3_eigenpairs :
    (∀ s : ℂ, s ^ 2 = 2 → A3.mulVec ![1, s, 1] = (2 + s) • ![1, s, 1]) ∧
    A3.mulVec ![1, 0, -1] = (2 : ℂ) • ![1, 0, -1] ∧
    ((2 + Real.sqrt 2 : ℝ) ≠ 2 ∧ (2 : ℝ) ≠ 2 - Real.sqrt 2 ∧ (2 + Real.sqrt 2 : ℝ) ≠ 2 - Real.sqrt 2) ∧
    ((!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![1, 1] = (3 : ℂ) • ![1, 1] ∧
      (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![1, -1] = (1 : ℂ) • ![1, -1]) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨fun s hs2 => ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [A3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination (-1) * hs2
  · ext i
    fin_cases i <;> simp [A3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · linarith
  · linarith
  · linarith
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- Interlacing for `A3` and its `2 × 2` minor, `i = 0, 1`: both inequalities of each. -/
example :
    ((A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨0, by simp⟩ ≤
        A3_isHermitian.eigenvalues₀ ⟨0, by simp⟩ ∧
      A3_isHermitian.eigenvalues₀ ⟨1, by simp⟩ ≤
        (A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨0, by simp⟩) ∧
    ((A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨1, by simp⟩ ≤
        A3_isHermitian.eigenvalues₀ ⟨1, by simp⟩ ∧
      A3_isHermitian.eigenvalues₀ ⟨2, by simp⟩ ≤
        (A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨1, by simp⟩) :=
  ⟨eigenvalues₀_submatrix_interlace A3_isHermitian (Fin.succEmb 2) 0 (by simp),
    eigenvalues₀_submatrix_interlace A3_isHermitian (Fin.succEmb 2) 1 (by simp)⟩

/-- The trace corollary at `z = 3/10 + i` (`Im z = 1`, card difference `1`):
`‖tr G_A(z) - tr G_{A_e}(z)‖ ≤ π + 1`. -/
example :
    ‖(RBM.green A3 ((3 / 10 : ℂ) + Complex.I)).trace -
        (RBM.green (A3.submatrix (Fin.succEmb 2) (Fin.succEmb 2))
          ((3 / 10 : ℂ) + Complex.I)).trace‖ ≤ Real.pi + 1 := by
  have h := trace_green_submatrix_sub_le A3_isHermitian (Fin.succEmb 2)
    (z := (3 / 10 : ℂ) + Complex.I) (by simp)
  simpa using h

end EigenInterlacingInst

end RBM.Univ
