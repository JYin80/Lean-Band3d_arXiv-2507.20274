/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14b
import RBM3D.Graph.BAGGExp

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false

/-!
# BA-L L4b1 (T2434), part B: the law and the expansion identity `baExp14b_expand_holds`

(docstring to be completed)
-/

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

section PF

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem BAExp14b_BAlwH_herm (g0 t : ℝ) (ω : Ω d L W) : (BAlwH d L W g0 t ω).IsHermitian := by
  have h1 : ((g0 : ℂ) • PsiI d L W).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d L W).eq, show star (g0 : ℂ) = (g0 : ℂ) from Complex.conj_ofReal _]
  exact h1.add (Hflow_isHermitian d L W t ω)

/-- The resolvent polynomial of `f = X_{[α]} G(σ)_{yx}`: `X_c = W^{-d} Σ_{v ∈ [c]} (G_{vv} - M_{vv})`, `Md v = M_{vv}`. -/
def BAExp14b_Pf (Md : Idx d L W → ℂ) (c : Zd d L) (σ : Bool) (x y : Idx d L W) :
    MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
  (MvPolynomial.C ((((W : ℕ) : ℂ) ^ d)⁻¹) * ∑ v ∈ Iblk d L W c, (MvPolynomial.X (true, v, v) - MvPolynomial.C (Md v))) *
    MvPolynomial.X (σ, y, x)

theorem BAExp14b_f_eq (g0 E t : ℝ) (m : ℂ) (Md : Idx d L W → ℂ) (c : Zd d L) (σ : Bool) (x y : Idx d L W) (ω : Ω d L W) :
    BAlwf d L W g0 E t m (BAExp14b_Pf Md c σ x y) ω =
      ((((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d L W c, (BAlwG d L W g0 E t m ω v v - Md v)) *
        (if σ then BAlwG d L W g0 E t m ω y x else star (BAlwG d L W g0 E t m ω x y)) := by
  unfold BAlwf LWPins_resPoly BAExp14b_Pf
  simp only [map_mul, map_sum, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
  cases σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lwWx_Gres_false (BAExp14b_BAlwH_herm g0 t ω)]
    rfl
  · rfl

theorem BAExp14b_df_eq (g0 E t : ℝ) (m : ℂ) (hz : (ztOf m E t).im ≠ 0) (Md : Idx d L W → ℂ) (c : Zd d L) (σ : Bool)
    (x y : Idx d L W) (ω : Ω d L W) (β γ : Idx d L W) :
    BAlwdf d L W g0 E t m (BAExp14b_Pf Md c σ x y) ω β γ =
      (-((((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d L W c, BAlwG d L W g0 E t m ω v β * BAlwG d L W g0 E t m ω γ v)) *
          (if σ then BAlwG d L W g0 E t m ω y x else star (BAlwG d L W g0 E t m ω x y)) +
        ((((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d L W c, (BAlwG d L W g0 E t m ω v v - Md v)) *
          (if σ then -(BAlwG d L W g0 E t m ω y β * BAlwG d L W g0 E t m ω γ x)
            else -star (BAlwG d L W g0 E t m ω x γ * BAlwG d L W g0 E t m ω β y)) := by
  have hH := BAExp14b_BAlwH_herm g0 t ω
  unfold BAlwdf LWPins_dH
  have hX : HasDerivAt (fun s : ℂ => (((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d L W c,
      (Gres (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ)) (ztOf m E t) true v v - Md v))
      (-((((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d L W c, BAlwG d L W g0 E t m ω v β * BAlwG d L W g0 E t m ω γ v)) 0 := by
    have := HasDerivAt.const_mul ((((W : ℕ) : ℂ) ^ d)⁻¹)
      (HasDerivAt.fun_sum (u := Iblk d L W c) (fun v _ => (lwWx_hasDerivAt_Gres hH hz true β γ v v).sub_const (Md v)))
    refine this.congr_deriv ?_
    rw [Finset.sum_neg_distrib, mul_neg]
    rfl
  have hT : HasDerivAt (fun s : ℂ => Gres (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ)) (ztOf m E t) σ y x)
      (-(Gres (BAlwH d L W g0 t ω) (ztOf m E t) σ y β * Gres (BAlwH d L W g0 t ω) (ztOf m E t) σ γ x)) 0 :=
    lwWx_hasDerivAt_Gres hH hz σ β γ y x
  have hP : HasDerivAt (fun s : ℂ => ((((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d L W c,
      (Gres (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ)) (ztOf m E t) true v v - Md v)) *
        Gres (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ)) (ztOf m E t) σ y x) _ 0 := hX.mul hT
  have e : (fun s : ℂ => MvPolynomial.eval (fun v => Gres (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ)) (ztOf m E t) v.1 v.2.1 v.2.2)
      (BAExp14b_Pf Md c σ x y)) = fun s : ℂ => ((((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d L W c,
      (Gres (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ)) (ztOf m E t) true v v - Md v)) *
        Gres (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ)) (ztOf m E t) σ y x := by
    funext s
    unfold BAExp14b_Pf
    simp only [map_mul, map_sum, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
  change deriv (fun s : ℂ => LWPins_resPoly d L W (ztOf m E t) (BAExp14b_Pf Md c σ x y)
    (BAlwH d L W g0 t ω + s • Matrix.single β γ (1 : ℂ))) 0 = _
  unfold LWPins_resPoly
  rw [e, hP.deriv]
  simp only [zero_smul, add_zero]
  cases σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lwWx_Gres_false hH, lwWx_Gres_false hH, lwWx_Gres_false hH]
    simp only [star_mul']
    rw [mul_comm (star _) (star _)]
    rfl
  · rfl

end PF

section Loop3

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem BAExp14b_gres_blockMat (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ : Bool) :
    Gres (blockMat d L W H) z σ = Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) (Gres H z σ) := by
  unfold Gres blockMat
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix
        (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    ext i j
    cases σ <;> simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  simp

/-- The block weight `(E_a)_{xx} = W^{-d} 1[x ∈ [a]]` on the fine lattice. -/
private def BAExp14b_dw (a : Zd d L) (x : Idx d L W) : ℂ := if (split d L W x).1 = a then ((W : ℂ) ^ d)⁻¹ else 0

private theorem BAExp14b_Eblk_reindex (a : Zd d L) :
    Eblk d L W a = Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) (Matrix.diagonal (BAExp14b_dw a)) := by
  ext p q
  have h : split d L W ((splitEquiv d L W).symm p) = p := (splitEquiv d L W).apply_symm_apply p
  simp [Eblk, BAExp14b_dw, Matrix.diagonal_apply, h]

private theorem BAExp14b_trace_reindex (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  exact Equiv.sum_comp (splitEquiv d L W).symm (fun i => M i i) |>.symm ▸ rfl

private theorem BAExp14b_loop_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d L) :
    loopFine d L W H z σ a = Matrix.trace (List.ofFn fun i =>
      Gres H z (σ i) * Matrix.diagonal (BAExp14b_dw (a i))).prod := by
  unfold loopFine loopM
  simp only [BAExp14b_gres_blockMat, BAExp14b_Eblk_reindex, ← map_mul]
  have h : (List.ofFn fun i => Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W)
      (Gres H z (σ i) * Matrix.diagonal (BAExp14b_dw (a i)))) =
      (List.ofFn fun i => Gres H z (σ i) * Matrix.diagonal (BAExp14b_dw (a i))).map
        (Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W)) := List.map_ofFn.symm
  rw [h, ← map_list_prod, BAExp14b_trace_reindex]

private theorem BAExp14b_trace_prod3 {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Fin 3 → Matrix ι ι ℂ) :
    Matrix.trace (List.ofFn P).prod = ∑ x, ∑ y, ∑ z, P 0 x y * (P 1 y z * P 2 z x) := by
  simp [List.ofFn_succ, Matrix.trace, Matrix.mul_apply, Finset.mul_sum]

/-- **`𝓛^{(3)}` as a triple fine sum**: `tr(G(σ₁)E_a G(σ₂)E_b G(σ₃)E_c) = W^{-3d} Σ_{x ∈ [c]} Σ_{α ∈ [a]} Σ_{y ∈ [b]} G(σ₁)_{xα} G(σ₂)_{αy} G(σ₃)_{yx}`. -/
theorem BAExp14b_loop3 (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ₁ σ₂ σ₃ : Bool) (a b c : Zd d L) :
    loopFine d L W H z ![σ₁, σ₂, σ₃] ![a, b, c] =
      (((W : ℂ) ^ d)⁻¹) ^ 3 * ∑ x ∈ Iblk d L W c, ∑ α ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b,
        Gres H z σ₁ x α * Gres H z σ₂ α y * Gres H z σ₃ y x := by
  rw [BAExp14b_loop_eq, BAExp14b_trace_prod3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.mul_diagonal, BAExp14b_dw]
  have e : ∀ x x1 x2 : Idx d L W,
      (Gres H z σ₁ x x1 * if (split d L W x1).1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        ((Gres H z σ₂ x1 x2 * if (split d L W x2).1 = b then ((W : ℂ) ^ d)⁻¹ else 0) *
          (Gres H z σ₃ x2 x * if (split d L W x).1 = c then ((W : ℂ) ^ d)⁻¹ else 0)) =
      if (split d L W x).1 = c then (if (split d L W x1).1 = a then (if (split d L W x2).1 = b then
        (((W : ℂ) ^ d)⁻¹) ^ 3 * (Gres H z σ₁ x x1 * Gres H z σ₂ x1 x2 * Gres H z σ₃ x2 x) else 0) else 0) else 0 := by
    intro x x1 x2
    by_cases h1 : (split d L W x1).1 = a <;> by_cases h2 : (split d L W x2).1 = b <;>
      by_cases h3 : (split d L W x).1 = c <;> simp [h1, h2, h3] <;> ring
  simp only [e]
  simp only [Iblk, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (split d L W x).1 = c
  · simp only [hx, ite_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    by_cases h1 : (split d L W x1).1 = a
    · simp only [h1, ite_true]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x2 _ => ?_
      by_cases h2 : (split d L W x2).1 = b
      · simp [h2]
      · simp [h2]
    · simp [h1]
  · simp [hx]

private theorem BAExp14b_trace_prod1 {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Fin 1 → Matrix ι ι ℂ) :
    Matrix.trace (List.ofFn P).prod = ∑ x, P 0 x x := by
  simp [List.ofFn_succ, Matrix.trace]

/-- **`𝓛^{(1)}` as a fine sum**: `tr(G(σ) E_c) = W^{-d} Σ_{x ∈ [c]} G(σ)_{xx}`. -/
theorem BAExp14b_loop1 (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ : Bool) (c : Zd d L) :
    loopFine d L W H z ![σ] ![c] = (((W : ℂ) ^ d))⁻¹ * ∑ x ∈ Iblk d L W c, Gres H z σ x x := by
  rw [BAExp14b_loop_eq, BAExp14b_trace_prod1]
  simp only [Matrix.cons_val_zero, Matrix.mul_diagonal, BAExp14b_dw]
  simp only [Iblk, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : (split d L W x).1 = c <;> simp [h, mul_comm]

/-- `\overline{G(σ)_{ab}} = G(!σ)_{ba}` for Hermitian `H`. -/
theorem BAExp14b_star_Gres {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (a b : Idx d L W) :
    star (Gres H z σ a b) = Gres H z (!σ) b a := by
  cases σ
  · simp only [Bool.not_false]
    rw [lwWx_Gres_false hH z a b, star_star]
  · simp only [Bool.not_true]
    rw [lwWx_Gres_false hH z b a]

private theorem BAExp14b_star_winv : star (((W : ℂ) ^ d)⁻¹) = ((W : ℂ) ^ d)⁻¹ := by
  rw [star_inv₀, star_pow]; simp

theorem BAExp14b_loop1_conj {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (c : Zd d L) :
    star (loopFine d L W H z ![σ] ![c]) = loopFine d L W H z ![!σ] ![c] := by
  rw [BAExp14b_loop1, BAExp14b_loop1, star_mul', star_sum, BAExp14b_star_winv]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [BAExp14b_star_Gres hH]

private theorem BAExp14b_sum3_rev {γ : Type*} [AddCommMonoid γ] {ι₁ ι₂ ι₃ : Type*} (s : Finset ι₁) (t : Finset ι₂) (u : Finset ι₃)
    (f : ι₁ → ι₂ → ι₃ → γ) : ∑ x ∈ s, ∑ α ∈ t, ∑ y ∈ u, f x α y = ∑ y ∈ u, ∑ α ∈ t, ∑ x ∈ s, f x α y := by
  calc ∑ x ∈ s, ∑ α ∈ t, ∑ y ∈ u, f x α y = ∑ x ∈ s, ∑ y ∈ u, ∑ α ∈ t, f x α y :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ y ∈ u, ∑ x ∈ s, ∑ α ∈ t, f x α y := Finset.sum_comm
    _ = ∑ y ∈ u, ∑ α ∈ t, ∑ x ∈ s, f x α y := Finset.sum_congr rfl fun y _ => Finset.sum_comm

theorem BAExp14b_loop3_conj {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (a b c : Zd d L) :
    star (loopFine d L W H z ![true, true, σ] ![a, b, c]) = loopFine d L W H z ![false, false, !σ] ![a, c, b] := by
  rw [BAExp14b_loop3, BAExp14b_loop3, star_mul', star_pow, BAExp14b_star_winv]
  congr 1
  rw [star_sum]
  simp only [star_sum, star_mul', BAExp14b_star_Gres hH]
  rw [BAExp14b_sum3_rev]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Bool.not_true]
  ring

end Loop3

section Cut

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ}

/-- `W^{-2d} Σ_{x ∈ [a]} Σ_{y ∈ [b]} Σ_α J x y α`: the frame of the integrands at the labelling `(x, y, α)`. -/
def BAExp14b_fr (sz : Sizes d) (n : ℕ) (a b : Zd d (sz.L n))
    (J : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, ∑ α, J x y α

private theorem BAExp14b_vec1 {γ : Type*} (b : γ) : (![b] : Fin 1 → γ) = fun _ => b := by
  funext i; fin_cases i; rfl

/-- `Σ_{a} Σ_{α ∈ [a]} h(a, α) = Σ_α h([α], α)`. -/
private theorem BAExp14b_sum_fibre {d L W : ℕ} [NeZero L] [NeZero W] (h : Zd d L → Idx d L W → ℂ) :
    ∑ a : Zd d L, ∑ α ∈ Iblk d L W a, h a α = ∑ α : Idx d L W, h (split d L W α).1 α := by
  rw [← Finset.sum_fiberwise Finset.univ (fun α : Idx d L W => (split d L W α).1) (fun α => h (split d L W α).1 α)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr ?_ fun α hα => ?_
  · ext α; simp [Iblk]
  · have : (split d L W α).1 = a := by simpa [Iblk] using hα
    rw [this]

/-- **The cut at `σc = +` as a fine sum**: `LWcutg = W^{-2d} Σ_{x ∈ [ao]} Σ_{y ∈ [ac]} Σ_α G(σo)_{yx} X_{[α]} G_{xα} G_{αy}`. -/
theorem BAExp14b_cut_true (n : ℕ) (t : ℝ)
    (hSelf : BASelf d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) ((baFMz sz z).m n))
    (σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    LWcutg (baFMz sz z) n t true σo ac ao ω = BAExp14b_fr sz n ao ac (fun x y α =>
      BAExp14a_tail sz z n t ω σo x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
        ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y))) := by
  have hS : ∀ a₁ a₂ : Zd d (sz.L n), (baFMz sz z).S n a₁ a₂ = if a₁ = a₂ then 1 else 0 := fun a₁ a₂ => by
    change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a₁ a₂ = _
    rw [Matrix.one_apply]
  have hL1 : ∀ a₁ : Zd d (sz.L n), (baFMz sz z).L n t ![true] ![a₁] ω - (baFMz sz z).m n = BAExp14a_X sz z n t ω a₁ := by
    intro a₁
    rw [BAExp14a_X_eq n t ω hSelf a₁, BAExp14b_vec1 true, BAExp14b_vec1 a₁]
  have hT : ∀ x y : Idx d (sz.L n) (sz.W n), Gres (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω)
      (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) σo y x = BAExp14a_tail sz z n t ω σo x y := by
    intro x y
    cases σo
    · simp only [BAExp14a_tail, Bool.false_eq_true, ↓reduceIte]
      rw [lwWx_Gres_false (BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω)]
      rfl
    · rfl
  have hL3 : ∀ a₂ : Zd d (sz.L n), (baFMz sz z).L n t ![true, true, σo] ![a₂, ac, ao] ω =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) ao, ∑ α ∈ Iblk d (sz.L n) (sz.W n) a₂,
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac,
          (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y * BAExp14a_tail sz z n t ω σo x y := by
    intro a₂
    calc (baFMz sz z).L n t ![true, true, σo] ![a₂, ac, ao] ω
        = loopFine d (sz.L n) (sz.W n) (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω)
            (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) ![true, true, σo] ![a₂, ac, ao] := rfl
      _ = _ := by
        rw [BAExp14b_loop3]
        simp only [hT]
        rfl
  unfold LWcutg
  simp only [hS, ite_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  simp only [hL1, hL3]
  unfold BAExp14b_fr
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hc : ((sz.W n : ℕ) : ℂ) ^ d * (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 2 := by
    field_simp
  have e1 : ((sz.W n : ℕ) : ℂ) ^ d * ∑ a₁ : Zd d (sz.L n), BAExp14a_X sz z n t ω a₁ *
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) ao, ∑ α ∈ Iblk d (sz.L n) (sz.W n) a₁,
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac,
          (baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y * BAExp14a_tail sz z n t ω σo x y) =
      ∑ x ∈ Iblk d (sz.L n) (sz.W n) ao, ∑ a₁ : Zd d (sz.L n), ∑ α ∈ Iblk d (sz.L n) (sz.W n) a₁,
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 2 *
          (BAExp14a_X sz z n t ω a₁ * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y * BAExp14a_tail sz z n t ω σo x y)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun y _ => ?_
    rw [← hc]; ring
  rw [e1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [BAExp14b_sum_fibre (fun a₁ α => ∑ y ∈ Iblk d (sz.L n) (sz.W n) ac, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 2 *
    (BAExp14a_X sz z n t ω a₁ * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y * BAExp14a_tail sz z n t ω σo x y))),
    Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [STblk]
  ring

/-- **The conjugation `BAExp14bCutConj`** (`σc = - → +`): `G(-) = G(+)^*`, `E_a` and `C.S = 1` real, the cyclic rotation of the 3-loop. -/
theorem baExp14b_cut_conj (sz : Sizes d) (z : ℕ → ℂ) : BAExp14bCutConj sz z := by
  intro n t σo ac ao ω
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have hS : ∀ a₁ a₂ : Zd d (sz.L n), (baFMz sz z).S n a₁ a₂ = if a₁ = a₂ then 1 else 0 := fun a₁ a₂ => by
    change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a₁ a₂ = _
    rw [Matrix.one_apply]
  have c1 : ∀ a₁ : Zd d (sz.L n), star ((baFMz sz z).L n t ![true] ![a₁] ω) = (baFMz sz z).L n t ![false] ![a₁] ω :=
    fun a₁ => BAExp14b_loop1_conj hH _ true a₁
  have c3 : ∀ a₂ : Zd d (sz.L n), star ((baFMz sz z).L n t ![true, true, !σo] ![a₂, ao, ac] ω) =
      (baFMz sz z).L n t ![false, false, σo] ![a₂, ac, ao] ω := fun a₂ => by
    have := BAExp14b_loop3_conj hH (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) (!σo) a₂ ao ac
    rwa [Bool.not_not] at this
  have hW : star (((sz.W n : ℕ) : ℂ) ^ d) = ((sz.W n : ℕ) : ℂ) ^ d := by
    rw [star_pow]; simp
  symm
  unfold LWcutg
  simp only [star_mul', star_sum, star_sub, hW, c1, c3, hS, Bool.false_eq_true, ite_true, ite_false]
  refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_)
  by_cases h : a₁ = a₂ <;> simp [h]

end Cut

section Law

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- `f = X_{[α]} G(σ)_{yx}`. -/
private def BAExp14b_f (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y

/-- `∂_{h_{βγ}} f = (∂X) G(σ)_{yx} + X ∂G(σ)_{yx}`. -/
private def BAExp14b_df (σ : Bool) (x y α β γ : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14b_dX sz z n t ω α β γ * BAExp14a_tail sz z n t ω σ x y +
    BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14b_dtail sz z n t ω σ x y β γ

/-- The right side of `lanlw` for `Ǧ_{ab} f`: `Σ M S Ǧ G f - Σ M S G ∂f`. -/
private def BAExp14b_Rlan (σ : Bool) (x y α a b : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α', ∑ β, (baFMz sz z).M n a α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).GM n t ω β β *
      (baFMz sz z).G n t ω α' b * BAExp14b_f sz z n t ω σ x y α -
    ∑ α', ∑ β, (baFMz sz z).M n a α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β b *
      BAExp14b_df sz z n t ω σ x y α β α'

/-- The right side of `GGGamma` (`BAGGGammaR`, D402) for `Ǧ_{xα} Ǧ_{αy} f` at `(α, y, x)`. -/
private def BAExp14b_Rgg (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  (∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n β y * (baFMz sz z).M n x β * BAExp14b_f sz z n t ω σ x y α +
    ∑ β, BAExp14a_Wk sz z n t true α β * ((baFMz sz z).GM n t ω β y * (baFMz sz z).M n x β +
      (baFMz sz z).M n β y * (baFMz sz z).GM n t ω x β) * BAExp14b_f sz z n t ω σ x y α +
    ∑ w, ∑ γ, ∑ δ, BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) α w *
      (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
      ((baFMz sz z).GM n t ω δ δ * (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w * BAExp14b_f sz z n t ω σ x y α +
        (baFMz sz z).GM n t ω γ w * (baFMz sz z).G n t ω δ y * (baFMz sz z).G n t ω x δ * BAExp14b_f sz z n t ω σ x y α -
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_df sz z n t ω σ x y α δ γ))

variable {sz z} {κ ε 𝔠 𝔡 : ℝ}

/-- The polynomial `f` of the carrier, `Md v = M_{vv}`. -/
private abbrev BAExp14b_Pc (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    MvPolynomial (Bool × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ℂ :=
  BAExp14b_Pf (fun v => BAlwM d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v v)
    (STblk sz n α) σ x y

/-- **`lanlw` for `f = X_{[α]} G(σ)_{yx}` at the carrier**. -/
private theorem BAExp14b_law_lanlw (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (σ : Bool) (x y α a b : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (baFMz sz z).GM n t ω a b * BAExp14b_f sz z n t ω σ x y α ∂(BAExp14a_μ sz) =
      ∫ ω, BAExp14b_Rlan sz z n t ω σ x y α a b ∂(BAExp14a_μ sz) := by
  obtain ⟨ht1, hr, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hz : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im ≠ 0 := hzi.ne'
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have key := baLanlw_holds d (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hSelf ht0 ht1 (BAExp14b_Pc sz z n σ x y α) a b
  have cG : ∀ α β : Idx d (sz.L n) (sz.W n), Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
      BAlwG d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) ω' α β :=
    fun α β => BAExp14a_cont_lwG hz α β
  have cL : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14b_Pc sz z n σ x y α) a b ω' := by
    simp only [BAlanlwL, BAlwGc, BAExp14b_Pc, BAExp14b_f_eq]
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := cG
      fun_prop
    · simp only [↓reduceIte]
      have := cG
      fun_prop
  have cR : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14b_Pc sz z n σ x y α) a b ω' := by
    simp only [BAlanlwR, BAlwGc, BAExp14b_Pc, BAExp14b_f_eq, BAExp14b_df_eq _ _ _ _ hz]
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := cG
      fun_prop
    · simp only [↓reduceIte]
      have := cG
      fun_prop
  have eL : ∀ ω : sz.SeqΩ, (baFMz sz z).GM n t ω a b * BAExp14b_f sz z n t ω σ x y α =
      BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) a b (BAExp14a_slc sz n ω) := by
    intro ω
    unfold BAlanlwL
    rw [BAExp14b_Pc, BAExp14b_f_eq]
    cases σ <;> rfl
  have eR : ∀ ω : sz.SeqΩ, BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) a b (BAExp14a_slc sz n ω) = BAExp14b_Rlan sz z n t ω σ x y α a b := by
    intro ω
    unfold BAlanlwR BAExp14b_Rlan
    simp only [BAExp14b_Pc, BAExp14b_f_eq, BAExp14b_df_eq _ _ _ _ hz, BAExp14b_f, BAExp14b_df]
    cases σ <;> rfl
  calc _ = ∫ ω, BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) a b (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) := integral_congr_ae (Eventually.of_forall eL)
    _ = ∫ ω', BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) a b ω' ∂(PF d (sz.L n) (sz.W n) 0) := BAExp14a_int_slice n _ cL
    _ = ∫ ω', BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) a b ω' ∂(PF d (sz.L n) (sz.W n) 0) := key
    _ = ∫ ω, BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) a b (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) := (BAExp14a_int_slice n _ cR).symm
    _ = _ := integral_congr_ae (Eventually.of_forall eR)

/-- **`GGGamma` for `f = X_{[α]} G(σ)_{yx}` at the carrier**: `𝔼 Ǧ_{xα} Ǧ_{αy} f = 𝔼 [RHS]` (`BAGGGammaR` at `(α, y, x)`). -/
private theorem BAExp14b_law_GG (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (baFMz sz z).GM n t ω x α * (baFMz sz z).GM n t ω α y * BAExp14b_f sz z n t ω σ x y α ∂(BAExp14a_μ sz) =
      ∫ ω, BAExp14b_Rgg sz z n t ω σ x y α ∂(BAExp14a_μ sz) := by
  obtain ⟨ht1, hr, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hz : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im ≠ 0 := hzi.ne'
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have key := baGGGamma_holds d (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hSelf ht0 ht1 (BAExp14b_Pc sz z n σ x y α) α y x
  have cG : ∀ α β : Idx d (sz.L n) (sz.W n), Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
      BAlwG d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) ω' α β :=
    fun α β => BAExp14a_cont_lwG hz α β
  have cL : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAGGGammaL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14b_Pc sz z n σ x y α) α y x ω' := by
    simp only [BAGGGammaL, BAlwGc, BAExp14b_Pc, BAExp14b_f_eq]
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := cG
      fun_prop
    · simp only [↓reduceIte]
      have := cG
      fun_prop
  have cR : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAGGGammaR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14b_Pc sz z n σ x y α) α y x ω' := by
    simp only [BAGGGammaR, BAlwGc, BAExp14b_Pc, BAExp14b_f_eq, BAExp14b_df_eq _ _ _ _ hz]
    cases σ
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := cG
      fun_prop
    · simp only [↓reduceIte]
      have := cG
      fun_prop
  have eL : ∀ ω : sz.SeqΩ, (baFMz sz z).GM n t ω x α * (baFMz sz z).GM n t ω α y * BAExp14b_f sz z n t ω σ x y α =
      BAGGGammaL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) α y x (BAExp14a_slc sz n ω) := by
    intro ω
    unfold BAGGGammaL
    rw [BAExp14b_Pc, BAExp14b_f_eq]
    cases σ <;> rfl
  have eR : ∀ ω : sz.SeqΩ, BAGGGammaR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) α y x (BAExp14a_slc sz n ω) = BAExp14b_Rgg sz z n t ω σ x y α := by
    intro ω
    unfold BAGGGammaR BAExp14b_Rgg
    simp only [BAExp14b_Pc, BAExp14b_f_eq, BAExp14b_df_eq _ _ _ _ hz, BAExp14b_f, BAExp14b_df]
    cases σ <;> rfl
  calc _ = ∫ ω, BAGGGammaL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) α y x (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) := integral_congr_ae (Eventually.of_forall eL)
    _ = ∫ ω', BAGGGammaL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) α y x ω' ∂(PF d (sz.L n) (sz.W n) 0) := BAExp14a_int_slice n _ cL
    _ = ∫ ω', BAGGGammaR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) α y x ω' ∂(PF d (sz.L n) (sz.W n) 0) := key
    _ = ∫ ω, BAGGGammaR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
        (BAExp14b_Pc sz z n σ x y α) α y x (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) := (BAExp14a_int_slice n _ cR).symm
    _ = _ := integral_congr_ae (Eventually.of_forall eR)

end Law

section BM

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- A bounded continuous random variable on the common sample space. -/
private def BAExp14b_BM (f : sz.SeqΩ → ℂ) : Prop := Continuous f ∧ ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C

private theorem BAExp14b_BM.const (c : ℂ) : BAExp14b_BM (sz := sz) (fun _ => c) :=
  ⟨continuous_const, ‖c‖, fun _ => le_rfl⟩

private theorem BAExp14b_BM.add {f g : sz.SeqΩ → ℂ} (hf : BAExp14b_BM f) (hg : BAExp14b_BM g) :
    BAExp14b_BM (fun ω => f ω + g ω) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  obtain ⟨cg, Cg, hCg⟩ := hg
  exact ⟨cf.add cg, Cf + Cg, fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem BAExp14b_BM.neg {f : sz.SeqΩ → ℂ} (hf : BAExp14b_BM f) : BAExp14b_BM (fun ω => -f ω) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  exact ⟨cf.neg, Cf, fun ω => by rw [norm_neg]; exact hCf ω⟩

private theorem BAExp14b_BM.sub {f g : sz.SeqΩ → ℂ} (hf : BAExp14b_BM f) (hg : BAExp14b_BM g) :
    BAExp14b_BM (fun ω => f ω - g ω) := by
  simp only [sub_eq_add_neg]
  exact hf.add hg.neg

private theorem BAExp14b_BM.mul {f g : sz.SeqΩ → ℂ} (hf : BAExp14b_BM f) (hg : BAExp14b_BM g) :
    BAExp14b_BM (fun ω => f ω * g ω) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  obtain ⟨cg, Cg, hCg⟩ := hg
  refine ⟨cf.mul cg, Cf * Cg, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf ω) (hCg ω) (norm_nonneg _) ((norm_nonneg _).trans (hCf ω))

private theorem BAExp14b_BM.star {f : sz.SeqΩ → ℂ} (hf : BAExp14b_BM f) : BAExp14b_BM (fun ω => star (f ω)) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  exact ⟨cf.star, Cf, fun ω => by rw [norm_star]; exact hCf ω⟩

private theorem BAExp14b_BM.sum {ι : Type*} (s : Finset ι) {f : ι → sz.SeqΩ → ℂ} (h : ∀ i ∈ s, BAExp14b_BM (f i)) :
    BAExp14b_BM (fun ω => ∑ i ∈ s, f i ω) := by
  choose! C hC using fun i hi => (h i hi).2
  refine ⟨continuous_finsetSum _ fun i hi => (h i hi).1, ∑ i ∈ s, C i, fun ω => ?_⟩
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => hC i hi ω)

private theorem BAExp14b_BM.integrable {f : sz.SeqΩ → ℂ} (hf : BAExp14b_BM f) : Integrable f (BAExp14a_μ sz) := by
  obtain ⟨cf, Cf, hCf⟩ := hf
  exact BAExp14a_integrable cf hCf

private theorem BAExp14b_BM_G (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (x y : Idx d (sz.L n) (sz.W n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => (baFMz sz z).G n t ω x y) :=
  ⟨BAExp14a_cont_G hκ hflow n ht0 ht x y, _, fun ω => BAExp14a_G_le hκ hflow n ht0 ht ω x y⟩

section Atoms

variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
include hκ hflow ht0 ht

private theorem BAExp14b_BM_GM (a b : Idx d (sz.L n) (sz.W n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω a b) := by
  unfold FlowFM.GM
  exact (BAExp14b_BM_G hκ hflow n ht0 ht a b).sub (BAExp14b_BM.const _)

private theorem BAExp14b_BM_X (c : Zd d (sz.L n)) : BAExp14b_BM (fun ω : sz.SeqΩ => BAExp14a_X sz z n t ω c) := by
  unfold BAExp14a_X
  refine (BAExp14b_BM.const _).mul (BAExp14b_BM.sum _ fun v _ => BAExp14b_BM_GM hκ hflow n ht0 ht v v)

private theorem BAExp14b_BM_tail (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => BAExp14a_tail sz z n t ω σ x y) := by
  cases σ
  · simp only [BAExp14a_tail, Bool.false_eq_true, ↓reduceIte]
    exact (BAExp14b_BM_G hκ hflow n ht0 ht x y).star
  · simp only [BAExp14a_tail, ↓reduceIte]
    exact BAExp14b_BM_G hκ hflow n ht0 ht y x

private theorem BAExp14b_BM_dtail (σ : Bool) (x y δ γ : Idx d (sz.L n) (sz.W n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => BAExp14b_dtail sz z n t ω σ x y δ γ) := by
  cases σ
  · simp only [BAExp14b_dtail, Bool.false_eq_true, ↓reduceIte]
    exact ((BAExp14b_BM_G hκ hflow n ht0 ht x γ).mul (BAExp14b_BM_G hκ hflow n ht0 ht δ y)).star.neg
  · simp only [BAExp14b_dtail, ↓reduceIte]
    exact ((BAExp14b_BM_G hκ hflow n ht0 ht y δ).mul (BAExp14b_BM_G hκ hflow n ht0 ht γ x)).neg

private theorem BAExp14b_BM_dX (α δ γ : Idx d (sz.L n) (sz.W n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => BAExp14b_dX sz z n t ω α δ γ) := by
  unfold BAExp14b_dX
  refine ((BAExp14b_BM.const _).mul (BAExp14b_BM.sum _ fun v _ =>
    (BAExp14b_BM_G hκ hflow n ht0 ht v δ).mul (BAExp14b_BM_G hκ hflow n ht0 ht γ v))).neg

end Atoms

end BM

set_option hygiene false in
/-- Closure of `BAExp14b_BM` under the operations of the families, with the atoms of `Atoms` (the names `hκ hflow n ht0 ht` of the context). -/
local macro "bm_tac" : tactic =>
  `(tactic| repeat' first
    | exact BAExp14b_BM.const _
    | exact BAExp14b_BM_G hκ hflow n ht0 ht _ _
    | exact BAExp14b_BM_GM hκ hflow n ht0 ht _ _
    | exact BAExp14b_BM_X hκ hflow n ht0 ht _
    | exact BAExp14b_BM_tail hκ hflow n ht0 ht _ _ _
    | exact BAExp14b_BM_dtail hκ hflow n ht0 ht _ _ _ _ _
    | exact BAExp14b_BM_dX hκ hflow n ht0 ht _ _ _
    | apply BAExp14b_BM.mul
    | apply BAExp14b_BM.add
    | apply BAExp14b_BM.sub
    | apply BAExp14b_BM.neg
    | apply BAExp14b_BM.star
    | (apply BAExp14b_BM.sum; intros; skip))

section IntFam

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
include hκ hflow ht0 ht

private theorem BAExp14b_BM_S1 (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => BAExp14a_F sz z n t ω k σ a b) := by
  fin_cases k <;> simp only [BAExp14a_F, BAExp14a_FMM, BAExp14a_FT1, BAExp14a_FT3A, BAExp14a_FC1, BAExp14a_FC2, BAExp14a_outer,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> bm_tac

private theorem BAExp14b_BM_S2 (j : Fin 8) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => BAExp14b_FS2 sz z n t ω j σ a b) := by
  fin_cases j <;> simp only [BAExp14b_FS2, BAExp14b_FD1t, BAExp14b_FD2t, BAExp14b_FT2a, BAExp14b_FT2b, BAExp14b_FT3B, BAExp14b_FT3CG,
    BAExp14b_outerDt, BAExp14a_outer, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] <;> bm_tac

private theorem BAExp14b_BM_S3 (j : Fin 4) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_BM (fun ω : sz.SeqΩ => BAExp14b_FS3 sz z n t ω j σ a b) := by
  fin_cases j <;> simp only [BAExp14b_FS3, BAExp14b_FD1X, BAExp14b_FD2X, BAExp14b_FT3CX, BAExp14b_outerDX, Fin.zero_eta, Fin.mk_one,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] <;> bm_tac

end IntFam

/-! ## 6. The frames: every family is `W^{-2d} Σ_{x ∈ [a]} Σ_{y ∈ [b]} Σ_α ι(x, y, α)` -/

section Frames

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

private theorem BAExp14b_outer_eq_fr (σ : Bool) (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    BAExp14a_outer sz z n t ω σ a b T = BAExp14b_fr sz n a b (fun x y α =>
      BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) * T x y α)) := by
  unfold BAExp14a_outer BAExp14b_fr
  simp only [Finset.mul_sum]

private theorem BAExp14b_outerDt_eq_fr (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    BAExp14b_outerDt sz z n t ω a b T = BAExp14b_fr sz n a b (fun x y α =>
      BAExp14a_X sz z n t ω (STblk sz n α) * T x y α) := rfl

private theorem BAExp14b_outerDX_eq_fr (σ : Bool) (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    BAExp14b_outerDX sz z n t ω σ a b T = BAExp14b_fr sz n a b (fun x y α =>
      BAExp14a_tail sz z n t ω σ x y * T x y α) := by
  unfold BAExp14b_outerDX BAExp14b_fr
  simp only [Finset.mul_sum]

private theorem BAExp14b_fr_add (a b : Zd d (sz.L n))
    (J₁ J₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    BAExp14b_fr sz n a b (fun x y α => J₁ x y α + J₂ x y α) = BAExp14b_fr sz n a b J₁ + BAExp14b_fr sz n a b J₂ := by
  unfold BAExp14b_fr
  simp only [Finset.sum_add_distrib, mul_add]

private theorem BAExp14b_fr_sum {ι : Type*} [Fintype ι] (a b : Zd d (sz.L n))
    (J : ι → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    BAExp14b_fr sz n a b (fun x y α => ∑ i, J i x y α) = ∑ i, BAExp14b_fr sz n a b (J i) := by
  unfold BAExp14b_fr
  simp only [← Finset.mul_sum]
  congr 1
  calc ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, ∑ α, ∑ i, J i x y α
      = ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, ∑ i, ∑ α, J i x y α :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ i, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, ∑ α, J i x y α :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, ∑ α, J i x y α := Finset.sum_comm

/-! ### The 18 integrands (the `W^{-2d} Σ_{x,y,α}`-summands of the families, `tail = G(σ)_{yx}`, `X = X_{[α]}`) -/

private def BAExp14b_iMM (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ((baFMz sz z).M n x α * (baFMz sz z).M n α y))

private def BAExp14b_iT1 (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n x β * (baFMz sz z).M n β y)

private def BAExp14b_iT3A (k : Bool) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ∑ w, ∑ γ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n γ)) *
      (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w)

private def BAExp14b_iC1 (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ∑ α', (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n α α' *
      (baFMz sz z).G n t ω α' y)

private def BAExp14b_iC2 (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ∑ α', ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n x α' * (baFMz sz z).G n t ω α' α *
      (baFMz sz z).M n α y)

private def BAExp14b_iD1t (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_X sz z n t ω (STblk sz n α) * ∑ α', ∑ β,
    -((baFMz sz z).M n x α * (baFMz sz z).M n α α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β y *
      BAExp14b_dtail sz z n t ω σ x y β α')

private def BAExp14b_iD2t (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_X sz z n t ω (STblk sz n α) * ∑ α', ∑ β,
    -((baFMz sz z).M n x α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β α * (baFMz sz z).M n α y *
      BAExp14b_dtail sz z n t ω σ x y β α')

private def BAExp14b_iT2a (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).GM n t ω β y * (baFMz sz z).M n x β)

private def BAExp14b_iT2b (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n β y * (baFMz sz z).GM n t ω x β)

private def BAExp14b_iT3B (k : Bool) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
    ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
      (baFMz sz z).GM n t ω γ w * (baFMz sz z).G n t ω δ y * (baFMz sz z).G n t ω x δ)

private def BAExp14b_iT3CG (k : Bool) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_X sz z n t ω (STblk sz n α) * ∑ w, ∑ γ, ∑ δ,
    -(BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).G n t ω δ y *
      (baFMz sz z).GM n t ω x w * BAExp14b_dtail sz z n t ω σ x y δ γ)

private def BAExp14b_iD1X (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * ∑ α', ∑ β,
    -((baFMz sz z).M n x α * (baFMz sz z).M n α α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β y *
      BAExp14b_dX sz z n t ω α β α')

private def BAExp14b_iD2X (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * ∑ α', ∑ β,
    -((baFMz sz z).M n x α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β α * (baFMz sz z).M n α y *
      BAExp14b_dX sz z n t ω α β α')

private def BAExp14b_iT3CX (k : Bool) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAExp14a_tail sz z n t ω σ x y * ∑ w, ∑ γ, ∑ δ,
    -(BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).G n t ω δ y *
      (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ)

/-- The six S1 integrands, in the order of `BAExp14a_F`. -/
private def BAExp14b_iS1 (k : Fin 6) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ![BAExp14b_iMM sz z n t ω σ x y α, BAExp14b_iT1 sz z n t ω σ x y α, BAExp14b_iT3A sz z n t ω false σ x y α,
    BAExp14b_iT3A sz z n t ω true σ x y α, BAExp14b_iC1 sz z n t ω σ x y α, BAExp14b_iC2 sz z n t ω σ x y α] k

/-- The eight S2 integrands, in the order of `BAExp14b_FS2`. -/
private def BAExp14b_iS2 (j : Fin 8) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ![BAExp14b_iD1t sz z n t ω σ x y α, BAExp14b_iD2t sz z n t ω σ x y α, BAExp14b_iT2a sz z n t ω σ x y α,
    BAExp14b_iT2b sz z n t ω σ x y α, BAExp14b_iT3B sz z n t ω false σ x y α, BAExp14b_iT3B sz z n t ω true σ x y α,
    BAExp14b_iT3CG sz z n t ω false σ x y α, BAExp14b_iT3CG sz z n t ω true σ x y α] j

/-- The four S3 integrands, in the order of `BAExp14b_FS3`. -/
private def BAExp14b_iS3 (j : Fin 4) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ![BAExp14b_iD1X sz z n t ω σ x y α, BAExp14b_iD2X sz z n t ω σ x y α, BAExp14b_iT3CX sz z n t ω false σ x y α,
    BAExp14b_iT3CX sz z n t ω true σ x y α] j

private theorem BAExp14b_F_eq_fr (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14a_F sz z n t ω k σ a b = BAExp14b_fr sz n a b (fun x y α => BAExp14b_iS1 sz z n t ω k σ x y α) := by
  fin_cases k <;> simp only [BAExp14a_F, BAExp14a_FMM, BAExp14a_FT1, BAExp14a_FT3A, BAExp14a_FC1, BAExp14a_FC2,
    BAExp14b_iS1, BAExp14b_iMM, BAExp14b_iT1, BAExp14b_iT3A, BAExp14b_iC1, BAExp14b_iC2, BAExp14b_outer_eq_fr,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> rfl

private theorem BAExp14b_FS2_eq_fr (j : Fin 8) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FS2 sz z n t ω j σ a b = BAExp14b_fr sz n a b (fun x y α => BAExp14b_iS2 sz z n t ω j σ x y α) := by
  fin_cases j <;> simp only [BAExp14b_FS2, BAExp14b_FD1t, BAExp14b_FD2t, BAExp14b_FT2a, BAExp14b_FT2b, BAExp14b_FT3B,
    BAExp14b_FT3CG, BAExp14b_iS2, BAExp14b_iD1t, BAExp14b_iD2t, BAExp14b_iT2a, BAExp14b_iT2b, BAExp14b_iT3B,
    BAExp14b_iT3CG, BAExp14b_outer_eq_fr, BAExp14b_outerDt_eq_fr, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> rfl

private theorem BAExp14b_FS3_eq_fr (j : Fin 4) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FS3 sz z n t ω j σ a b = BAExp14b_fr sz n a b (fun x y α => BAExp14b_iS3 sz z n t ω j σ x y α) := by
  fin_cases j <;> simp only [BAExp14b_FS3, BAExp14b_FD1X, BAExp14b_FD2X, BAExp14b_FT3CX, BAExp14b_iS3, BAExp14b_iD1X,
    BAExp14b_iD2X, BAExp14b_iT3CX, BAExp14b_outerDX_eq_fr, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> rfl

/-- **The 18 families are the frame of the sum of the 18 integrands.** -/
private theorem BAExp14b_families_eq_fr (σ : Bool) (a b : Zd d (sz.L n)) :
    (∑ k : Fin 6, BAExp14a_F sz z n t ω k σ a b) + (∑ j : Fin 8, BAExp14b_FS2 sz z n t ω j σ a b) +
        (∑ j : Fin 4, BAExp14b_FS3 sz z n t ω j σ a b) =
      BAExp14b_fr sz n a b (fun x y α => (∑ k : Fin 6, BAExp14b_iS1 sz z n t ω k σ x y α) +
        (∑ j : Fin 8, BAExp14b_iS2 sz z n t ω j σ x y α) + (∑ j : Fin 4, BAExp14b_iS3 sz z n t ω j σ x y α)) := by
  have e1 : ∑ k : Fin 6, BAExp14a_F sz z n t ω k σ a b = ∑ k : Fin 6, BAExp14b_fr sz n a b (BAExp14b_iS1 sz z n t ω k σ) :=
    Finset.sum_congr rfl fun k _ => BAExp14b_F_eq_fr sz z n t ω k σ a b
  have e2 : ∑ j : Fin 8, BAExp14b_FS2 sz z n t ω j σ a b = ∑ j : Fin 8, BAExp14b_fr sz n a b (BAExp14b_iS2 sz z n t ω j σ) :=
    Finset.sum_congr rfl fun j _ => BAExp14b_FS2_eq_fr sz z n t ω j σ a b
  have e3 : ∑ j : Fin 4, BAExp14b_FS3 sz z n t ω j σ a b = ∑ j : Fin 4, BAExp14b_fr sz n a b (BAExp14b_iS3 sz z n t ω j σ) :=
    Finset.sum_congr rfl fun j _ => BAExp14b_FS3_eq_fr sz z n t ω j σ a b
  rw [e1, e2, e3, BAExp14b_fr_add, BAExp14b_fr_add, BAExp14b_fr_sum, BAExp14b_fr_sum, BAExp14b_fr_sum]

end Frames

/-! ## 7. The pathwise algebra: `Ǧ = G - M`, the right sides of `lanlw`, `GGGamma` and the 18 integrands -/

section Alg

/-- The linear algebra of the `lanlw` children: `m (Σ_i p_i - Σ_{i,k} B_{ik}) = T X Σ c_i + X Σ (-e_{ik}) + T Σ (-f_{ik})`
when `m p_i = T X c_i` and `m B_{ik} = X e_{ik} + T f_{ik}`. -/
private theorem BAExp14b_lin_lan {ι κ : Type*} [Fintype ι] [Fintype κ] (m T X : ℂ) (p c : ι → ℂ) (B e f : ι → κ → ℂ)
    (hp : ∀ i, m * p i = T * (X * c i)) (hB : ∀ i k, m * B i k = X * e i k + T * f i k) :
    m * (∑ i, p i - ∑ i, ∑ k, B i k) =
      T * (X * ∑ i, c i) + X * ∑ i, ∑ k, -e i k + T * ∑ i, ∑ k, -f i k := by
  have h1 : m * ∑ i, p i = T * (X * ∑ i, c i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hp i
  have h2 : m * ∑ i, ∑ k, B i k = X * ∑ i, ∑ k, e i k + T * ∑ i, ∑ k, f i k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hB i k
  rw [mul_sub, h1, h2]
  simp only [Finset.sum_neg_distrib, mul_neg]
  ring

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

private theorem BAExp14b_alg_MM (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    (baFMz sz z).M n x α * (baFMz sz z).M n α y * BAExp14b_f sz z n t ω σ x y α = BAExp14b_iMM sz z n t ω σ x y α := by
  unfold BAExp14b_f BAExp14b_iMM
  ring

/-- `M_{xα} · (Rlan at (α, y)) = C1 + D1t + D1X`. -/
private theorem BAExp14b_alg_MG (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σ x y α α y =
      BAExp14b_iC1 sz z n t ω σ x y α + BAExp14b_iD1t sz z n t ω σ x y α + BAExp14b_iD1X sz z n t ω σ x y α := by
  unfold BAExp14b_Rlan BAExp14b_iC1 BAExp14b_iD1t BAExp14b_iD1X BAExp14b_f BAExp14b_df
  have hA : ∑ α', ∑ β, (baFMz sz z).M n α α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).GM n t ω β β *
        (baFMz sz z).G n t ω α' y * (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y) =
      ∑ α', (baFMz sz z).M n α α' * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).G n t ω α' y *
        (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y) := by
    refine Finset.sum_congr rfl fun α' _ => ?_
    have h := BAExp14a_sumS_GM (sz := sz) (z := z) n t ω α'
    calc ∑ β, (baFMz sz z).M n α α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).GM n t ω β β *
          (baFMz sz z).G n t ω α' y * (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y)
        = ((baFMz sz z).M n α α' * (baFMz sz z).G n t ω α' y *
            (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y)) *
          ∑ β, BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).GM n t ω β β := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring
      _ = _ := by rw [h]; ring
  rw [hA]
  exact BAExp14b_lin_lan _ _ _ _ _ _ _ _ (fun i => by ring) (fun i k => by ring)

/-- `Ǧ_{xα}`-side `lanlw` child: `(Rlan at (x, α)) · M_{αy} = C2 + D2t + D2X`. -/
private theorem BAExp14b_alg_GM (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    BAExp14b_Rlan sz z n t ω σ x y α x α * (baFMz sz z).M n α y =
      BAExp14b_iC2 sz z n t ω σ x y α + BAExp14b_iD2t sz z n t ω σ x y α + BAExp14b_iD2X sz z n t ω σ x y α := by
  unfold BAExp14b_Rlan BAExp14b_iC2 BAExp14b_iD2t BAExp14b_iD2X BAExp14b_f BAExp14b_df
  have hA : ∑ α', ∑ β, (baFMz sz z).M n x α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).GM n t ω β β *
        (baFMz sz z).G n t ω α' α * (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y) =
      ∑ α', (baFMz sz z).M n x α' * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).G n t ω α' α *
        (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y) := by
    refine Finset.sum_congr rfl fun α' _ => ?_
    have h := BAExp14a_sumS_GM (sz := sz) (z := z) n t ω α'
    calc ∑ β, (baFMz sz z).M n x α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).GM n t ω β β *
          (baFMz sz z).G n t ω α' α * (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y)
        = ((baFMz sz z).M n x α' * (baFMz sz z).G n t ω α' α *
            (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y)) *
          ∑ β, BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).GM n t ω β β := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring
      _ = _ := by rw [h]; ring
  rw [hA, mul_comm _ ((baFMz sz z).M n α y)]
  exact BAExp14b_lin_lan _ _ _ _ _ _ _ _ (fun i => by ring) (fun i k => by ring)

private theorem BAExp14b_Wsplit (α w : Idx d (sz.L n) (sz.W n)) :
    BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) α w =
      BAExp14a_Wk sz z n t false α w + BAExp14a_Wk sz z n t true α w := by
  simp only [BAExp14a_Wk, Bool.false_eq_true, ↓reduceIte, ite_true, Matrix.sub_apply]
  ring

private theorem BAExp14b_lin_3 {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] (U a b c : ι₁ → ι₂ → ι₃ → ℂ) :
    ∑ w, ∑ γ, ∑ δ, U w γ δ * (a w γ δ + b w γ δ - c w γ δ) =
      ∑ w, ∑ γ, ∑ δ, U w γ δ * a w γ δ + ∑ w, ∑ γ, ∑ δ, U w γ δ * b w γ δ - ∑ w, ∑ γ, ∑ δ, U w γ δ * c w γ δ := by
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The `W^{(k)}`-part of the third sum of `GGGamma`: `T3A + T3B + T3C-Ḡ + T3C-tr`. -/
private theorem BAExp14b_alg_S3k (k : Bool) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
      ((baFMz sz z).GM n t ω δ δ * (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w * BAExp14b_f sz z n t ω σ x y α +
        (baFMz sz z).GM n t ω γ w * (baFMz sz z).G n t ω δ y * (baFMz sz z).G n t ω x δ * BAExp14b_f sz z n t ω σ x y α -
        (baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w * BAExp14b_df sz z n t ω σ x y α δ γ) =
      BAExp14b_iT3A sz z n t ω k σ x y α + BAExp14b_iT3B sz z n t ω k σ x y α + BAExp14b_iT3CG sz z n t ω k σ x y α +
        BAExp14b_iT3CX sz z n t ω k σ x y α := by
  rw [BAExp14b_lin_3]
  unfold BAExp14b_iT3A BAExp14b_iT3B BAExp14b_iT3CG BAExp14b_iT3CX BAExp14b_f BAExp14b_df
  have hA : ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        ((baFMz sz z).GM n t ω δ δ * (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w *
          (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y)) =
      BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
        ∑ w, ∑ γ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n γ)) *
          (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun γ _ => ?_
    have h := BAExp14a_sumS_GM (sz := sz) (z := z) n t ω γ
    calc ∑ δ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
          ((baFMz sz z).GM n t ω δ δ * (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w *
            (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y))
        = (BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w *
            (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y)) *
          ∑ δ, BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).GM n t ω δ δ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun δ _ => by ring
      _ = _ := by rw [h]; ring
  have hB : ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        ((baFMz sz z).GM n t ω γ w * (baFMz sz z).G n t ω δ y * (baFMz sz z).G n t ω x δ *
          (BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14a_tail sz z n t ω σ x y)) =
      BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
        ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
          (baFMz sz z).GM n t ω γ w * (baFMz sz z).G n t ω δ y * (baFMz sz z).G n t ω x δ) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by ring
  have hC : ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ *
        ((baFMz sz z).G n t ω δ y * (baFMz sz z).GM n t ω x w *
          (BAExp14b_dX sz z n t ω α δ γ * BAExp14a_tail sz z n t ω σ x y +
            BAExp14a_X sz z n t ω (STblk sz n α) * BAExp14b_dtail sz z n t ω σ x y δ γ)) =
      -(BAExp14a_X sz z n t ω (STblk sz n α) * ∑ w, ∑ γ, ∑ δ,
        -(BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).G n t ω δ y *
          (baFMz sz z).GM n t ω x w * BAExp14b_dtail sz z n t ω σ x y δ γ)) -
      BAExp14a_tail sz z n t ω σ x y * ∑ w, ∑ γ, ∑ δ,
        -(BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).G n t ω δ y *
          (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ) := by
    simp only [Finset.mul_sum, Finset.sum_neg_distrib, mul_neg, neg_neg]
    rw [sub_neg_eq_add]
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by ring
  rw [hA, hB, hC]
  ring

private theorem BAExp14b_W3 (α : Idx d (sz.L n) (sz.W n)) (M S : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (Z : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ w, ∑ γ, ∑ δ, BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) α w *
        M w γ * S γ δ * Z w γ δ =
      ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t false α w * M w γ * S γ δ * Z w γ δ +
        ∑ w, ∑ γ, ∑ δ, BAExp14a_Wk sz z n t true α w * M w γ * S γ δ * Z w γ δ := by
  simp only [BAExp14b_Wsplit, add_mul, Finset.sum_add_distrib]

/-- **The `GGGamma` children**: `Rgg = T1 + T2a + T2b + Σ_k (T3A + T3B + T3C-Ḡ + T3C-tr)`. -/
private theorem BAExp14b_alg_GG (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    BAExp14b_Rgg sz z n t ω σ x y α =
      BAExp14b_iT1 sz z n t ω σ x y α + BAExp14b_iT2a sz z n t ω σ x y α + BAExp14b_iT2b sz z n t ω σ x y α +
        (BAExp14b_iT3A sz z n t ω false σ x y α + BAExp14b_iT3B sz z n t ω false σ x y α +
          BAExp14b_iT3CG sz z n t ω false σ x y α + BAExp14b_iT3CX sz z n t ω false σ x y α) +
        (BAExp14b_iT3A sz z n t ω true σ x y α + BAExp14b_iT3B sz z n t ω true σ x y α +
          BAExp14b_iT3CG sz z n t ω true σ x y α + BAExp14b_iT3CX sz z n t ω true σ x y α) := by
  have h1 : ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n β y * (baFMz sz z).M n x β *
      BAExp14b_f sz z n t ω σ x y α = BAExp14b_iT1 sz z n t ω σ x y α := by
    unfold BAExp14b_iT1 BAExp14b_f
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have h2 : ∑ β, BAExp14a_Wk sz z n t true α β * ((baFMz sz z).GM n t ω β y * (baFMz sz z).M n x β +
      (baFMz sz z).M n β y * (baFMz sz z).GM n t ω x β) * BAExp14b_f sz z n t ω σ x y α =
      BAExp14b_iT2a sz z n t ω σ x y α + BAExp14b_iT2b sz z n t ω σ x y α := by
    unfold BAExp14b_iT2a BAExp14b_iT2b BAExp14b_f
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun β _ => by ring
  unfold BAExp14b_Rgg
  rw [BAExp14b_W3 sz z n t α ((baFMz sz z).M n) (BAlwS d (sz.L n) (sz.W n) t), BAExp14b_alg_S3k sz z n t ω false σ x y α,
    BAExp14b_alg_S3k sz z n t ω true σ x y α, h1, h2]
  ring

/-- **The cell identity, pathwise**: the right sides of `lanlw` (twice) and `GGGamma` assemble to the 18 integrands. -/
private theorem BAExp14b_alg (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    (baFMz sz z).M n x α * (baFMz sz z).M n α y * BAExp14b_f sz z n t ω σ x y α +
        (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σ x y α α y +
        BAExp14b_Rlan sz z n t ω σ x y α x α * (baFMz sz z).M n α y + BAExp14b_Rgg sz z n t ω σ x y α =
      (∑ k : Fin 6, BAExp14b_iS1 sz z n t ω k σ x y α) + (∑ j : Fin 8, BAExp14b_iS2 sz z n t ω j σ x y α) +
        (∑ j : Fin 4, BAExp14b_iS3 sz z n t ω j σ x y α) := by
  rw [BAExp14b_alg_MM, BAExp14b_alg_MG, BAExp14b_alg_GM, BAExp14b_alg_GG]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, BAExp14b_iS1, BAExp14b_iS2, BAExp14b_iS3, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val, add_zero]
  ring

end Alg

/-! ## 8. The expansion identity -/

section Expand

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- Linearity of the integral for `c₁ f₁ + c₂ f₂ + c₃ f₃ + f₄`. -/
private theorem BAExp14b_int4 {f₁ f₂ f₃ f₄ : sz.SeqΩ → ℂ} (h₁ : Integrable f₁ (BAExp14a_μ sz)) (h₂ : Integrable f₂ (BAExp14a_μ sz))
    (h₃ : Integrable f₃ (BAExp14a_μ sz)) (h₄ : Integrable f₄ (BAExp14a_μ sz)) (c₁ c₂ c₃ : ℂ) :
    ∫ ω, (c₁ * f₁ ω + c₂ * f₂ ω + c₃ * f₃ ω + f₄ ω) ∂(BAExp14a_μ sz) =
      c₁ * ∫ ω, f₁ ω ∂(BAExp14a_μ sz) + c₂ * ∫ ω, f₂ ω ∂(BAExp14a_μ sz) + c₃ * ∫ ω, f₃ ω ∂(BAExp14a_μ sz) +
        ∫ ω, f₄ ω ∂(BAExp14a_μ sz) := by
  have i1 : Integrable (fun ω => c₁ * f₁ ω) (BAExp14a_μ sz) := h₁.const_mul c₁
  have i2 : Integrable (fun ω => c₂ * f₂ ω) (BAExp14a_μ sz) := h₂.const_mul c₂
  have i3 : Integrable (fun ω => c₃ * f₃ ω) (BAExp14a_μ sz) := h₃.const_mul c₃
  have i12 : Integrable (fun ω => c₁ * f₁ ω + c₂ * f₂ ω) (BAExp14a_μ sz) := i1.add i2
  have i123 : Integrable (fun ω => c₁ * f₁ ω + c₂ * f₂ ω + c₃ * f₃ ω) (BAExp14a_μ sz) := i12.add i3
  rw [integral_add i123 h₄, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- **The cell identity** `𝔼[G(σ)_{yx} X_{[α]} G_{xα} G_{αy}] = 𝔼[M M f + M R_lan + R_lan' M + R_gg]`: `G = Ǧ + M`, `lanlw` twice, `GGGamma`. -/
private theorem BAExp14b_cell (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (σ : Bool) (x y α : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
        ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)) ∂(BAExp14a_μ sz) =
      ∫ ω, ((baFMz sz z).M n x α * (baFMz sz z).M n α y * BAExp14b_f sz z n t ω σ x y α +
        (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σ x y α α y +
        BAExp14b_Rlan sz z n t ω σ x y α x α * (baFMz sz z).M n α y + BAExp14b_Rgg sz z n t ω σ x y α) ∂(BAExp14a_μ sz) := by
  have iF : Integrable (fun ω : sz.SeqΩ => BAExp14b_f sz z n t ω σ x y α) (BAExp14a_μ sz) := by
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_f
    bm_tac
  have iF2 : Integrable (fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω α y * BAExp14b_f sz z n t ω σ x y α) (BAExp14a_μ sz) := by
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_f
    bm_tac
  have iF3 : Integrable (fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω x α * BAExp14b_f sz z n t ω σ x y α) (BAExp14a_μ sz) := by
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_f
    bm_tac
  have iF4 : Integrable (fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω x α * (baFMz sz z).GM n t ω α y *
      BAExp14b_f sz z n t ω σ x y α) (BAExp14a_μ sz) := by
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_f
    bm_tac
  have iR1 : Integrable (fun ω : sz.SeqΩ => BAExp14b_Rlan sz z n t ω σ x y α α y) (BAExp14a_μ sz) := by
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_Rlan BAExp14b_f BAExp14b_df
    bm_tac
  have iR2 : Integrable (fun ω : sz.SeqΩ => BAExp14b_Rlan sz z n t ω σ x y α x α) (BAExp14a_μ sz) := by
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_Rlan BAExp14b_f BAExp14b_df
    bm_tac
  have iR3 : Integrable (fun ω : sz.SeqΩ => BAExp14b_Rgg sz z n t ω σ x y α) (BAExp14a_μ sz) := by
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_Rgg BAExp14b_f BAExp14b_df
    bm_tac
  have hL : ∀ ω : sz.SeqΩ, BAExp14a_tail sz z n t ω σ x y * (BAExp14a_X sz z n t ω (STblk sz n α) *
      ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y)) =
      ((baFMz sz z).M n x α * (baFMz sz z).M n α y) * BAExp14b_f sz z n t ω σ x y α +
        (baFMz sz z).M n x α * ((baFMz sz z).GM n t ω α y * BAExp14b_f sz z n t ω σ x y α) +
        (baFMz sz z).M n α y * ((baFMz sz z).GM n t ω x α * BAExp14b_f sz z n t ω σ x y α) +
        (baFMz sz z).GM n t ω x α * (baFMz sz z).GM n t ω α y * BAExp14b_f sz z n t ω σ x y α := by
    intro ω
    unfold BAExp14b_f FlowFM.GM
    ring
  have hR : ∀ ω : sz.SeqΩ, (baFMz sz z).M n x α * (baFMz sz z).M n α y * BAExp14b_f sz z n t ω σ x y α +
        (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σ x y α α y +
        BAExp14b_Rlan sz z n t ω σ x y α x α * (baFMz sz z).M n α y + BAExp14b_Rgg sz z n t ω σ x y α =
      ((baFMz sz z).M n x α * (baFMz sz z).M n α y) * BAExp14b_f sz z n t ω σ x y α +
        (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σ x y α α y +
        (baFMz sz z).M n α y * BAExp14b_Rlan sz z n t ω σ x y α x α + BAExp14b_Rgg sz z n t ω σ x y α := by
    intro ω; ring
  simp only [hL, hR]
  rw [BAExp14b_int4 iF iF2 iF3 iF4, BAExp14b_int4 iF iR1 iR2 iR3,
    BAExp14b_law_lanlw hκ hflow n ht0 ht σ x y α α y, BAExp14b_law_lanlw hκ hflow n ht0 ht σ x y α x α,
    BAExp14b_law_GG hκ hflow n ht0 ht σ x y α]

/-- The integral of a frame is the frame of the integrals (`W^{-2d} Σ_{x ∈ [a]} Σ_{y ∈ [b]} Σ_α`). -/
private theorem BAExp14b_integral_fr (n : ℕ) (a b : Zd d (sz.L n))
    (J : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ)
    (hJ : ∀ x y α, Integrable (J x y α) (BAExp14a_μ sz)) :
    ∫ ω, BAExp14b_fr sz n a b (fun x y α => J x y α ω) ∂(BAExp14a_μ sz) =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, ∑ α,
        ∫ ω, J x y α ω ∂(BAExp14a_μ sz) := by
  unfold BAExp14b_fr
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => integrable_finsetSum _ fun α _ => hJ x y α]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ fun y _ => integrable_finsetSum _ fun α _ => hJ x y α]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_finsetSum _ fun α _ => hJ x y α]

private theorem BAExp14b_fr_congr (n : ℕ) (a b : Zd d (sz.L n))
    {J₁ J₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ}
    (h : ∀ x y α, J₁ x y α = J₂ x y α) : BAExp14b_fr sz n a b J₁ = BAExp14b_fr sz n a b J₂ := by
  unfold BAExp14b_fr
  simp only [h]

/-- **The expansion identity at `σc = +`.** -/
private theorem BAExp14b_expand_true (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (σo : Bool) (ac ao : Zd d (sz.L n)) :
    ∫ ω, LWcutg (baFMz sz z) n t true σo ac ao ω ∂(BAExp14a_μ sz) =
      (∑ k : Fin 6, ∫ ω, BAExp14aS1Fam sz z n t ω k true σo ac ao ∂(BAExp14a_μ sz)) +
        (∑ j : Fin 8, ∫ ω, BAExp14bS2Fam sz z n t ω j true σo ac ao ∂(BAExp14a_μ sz)) +
        (∑ j : Fin 4, ∫ ω, BAExp14bS3Fam sz z n t ω j true σo ac ao ∂(BAExp14a_μ sz)) := by
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have iL : ∀ x y α : Idx d (sz.L n) (sz.W n), Integrable (fun ω : sz.SeqΩ => BAExp14a_tail sz z n t ω σo x y *
      (BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y))) (BAExp14a_μ sz) := by
    intro x y α
    refine BAExp14b_BM.integrable ?_
    bm_tac
  have iJ : ∀ x y α : Idx d (sz.L n) (sz.W n), Integrable (fun ω : sz.SeqΩ =>
      ((baFMz sz z).M n x α * (baFMz sz z).M n α y * BAExp14b_f sz z n t ω σo x y α +
        (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σo x y α α y +
        BAExp14b_Rlan sz z n t ω σo x y α x α * (baFMz sz z).M n α y + BAExp14b_Rgg sz z n t ω σo x y α)) (BAExp14a_μ sz) := by
    intro x y α
    refine BAExp14b_BM.integrable ?_
    unfold BAExp14b_Rlan BAExp14b_Rgg BAExp14b_f BAExp14b_df
    bm_tac
  have e1 : ∫ ω, LWcutg (baFMz sz z) n t true σo ac ao ω ∂(BAExp14a_μ sz) =
      ∫ ω, BAExp14b_fr sz n ao ac (fun x y α => BAExp14a_tail sz z n t ω σo x y *
        (BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y))) ∂(BAExp14a_μ sz) :=
    integral_congr_ae (Eventually.of_forall fun ω => BAExp14b_cut_true n t hSelf σo ac ao ω)
  have e2 : ∫ ω, BAExp14b_fr sz n ao ac (fun x y α => BAExp14a_tail sz z n t ω σo x y *
        (BAExp14a_X sz z n t ω (STblk sz n α) * ((baFMz sz z).G n t ω x α * (baFMz sz z).G n t ω α y))) ∂(BAExp14a_μ sz) =
      ∫ ω, BAExp14b_fr sz n ao ac (fun x y α =>
        ((baFMz sz z).M n x α * (baFMz sz z).M n α y * BAExp14b_f sz z n t ω σo x y α +
          (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σo x y α α y +
          BAExp14b_Rlan sz z n t ω σo x y α x α * (baFMz sz z).M n α y + BAExp14b_Rgg sz z n t ω σo x y α)) ∂(BAExp14a_μ sz) := by
    rw [BAExp14b_integral_fr n ao ac _ iL, BAExp14b_integral_fr n ao ac _ iJ]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun α _ => ?_
    exact BAExp14b_cell hκ hflow n ht0 ht σo x y α
  have e3 : ∀ ω : sz.SeqΩ, BAExp14b_fr sz n ao ac (fun x y α =>
        ((baFMz sz z).M n x α * (baFMz sz z).M n α y * BAExp14b_f sz z n t ω σo x y α +
          (baFMz sz z).M n x α * BAExp14b_Rlan sz z n t ω σo x y α α y +
          BAExp14b_Rlan sz z n t ω σo x y α x α * (baFMz sz z).M n α y + BAExp14b_Rgg sz z n t ω σo x y α)) =
      (∑ k : Fin 6, BAExp14a_F sz z n t ω k σo ao ac) + (∑ j : Fin 8, BAExp14b_FS2 sz z n t ω j σo ao ac) +
        (∑ j : Fin 4, BAExp14b_FS3 sz z n t ω j σo ao ac) := by
    intro ω
    rw [BAExp14b_families_eq_fr]
    exact BAExp14b_fr_congr n ao ac fun x y α => BAExp14b_alg sz z n t ω σo x y α
  have iS1 : ∀ k : Fin 6, Integrable (fun ω : sz.SeqΩ => BAExp14a_F sz z n t ω k σo ao ac) (BAExp14a_μ sz) :=
    fun k => (BAExp14b_BM_S1 hκ hflow n ht0 ht k σo ao ac).integrable
  have iS2 : ∀ j : Fin 8, Integrable (fun ω : sz.SeqΩ => BAExp14b_FS2 sz z n t ω j σo ao ac) (BAExp14a_μ sz) :=
    fun j => (BAExp14b_BM_S2 hκ hflow n ht0 ht j σo ao ac).integrable
  have iS3 : ∀ j : Fin 4, Integrable (fun ω : sz.SeqΩ => BAExp14b_FS3 sz z n t ω j σo ao ac) (BAExp14a_μ sz) :=
    fun j => (BAExp14b_BM_S3 hκ hflow n ht0 ht j σo ao ac).integrable
  have iA : Integrable (fun ω : sz.SeqΩ => ∑ k : Fin 6, BAExp14a_F sz z n t ω k σo ao ac) (BAExp14a_μ sz) :=
    integrable_finsetSum _ fun k _ => iS1 k
  have iB : Integrable (fun ω : sz.SeqΩ => ∑ j : Fin 8, BAExp14b_FS2 sz z n t ω j σo ao ac) (BAExp14a_μ sz) :=
    integrable_finsetSum _ fun j _ => iS2 j
  have iC : Integrable (fun ω : sz.SeqΩ => ∑ j : Fin 4, BAExp14b_FS3 sz z n t ω j σo ao ac) (BAExp14a_μ sz) :=
    integrable_finsetSum _ fun j _ => iS3 j
  have iAB : Integrable (fun ω : sz.SeqΩ => (∑ k : Fin 6, BAExp14a_F sz z n t ω k σo ao ac) +
      ∑ j : Fin 8, BAExp14b_FS2 sz z n t ω j σo ao ac) (BAExp14a_μ sz) := iA.add iB
  rw [e1, e2]
  simp only [e3]
  rw [integral_add iAB iC, integral_add iA iB, integral_finsetSum _ fun k _ => iS1 k,
    integral_finsetSum _ fun j _ => iS2 j, integral_finsetSum _ fun j _ => iS3 j]
  simp only [BAExp14aS1Fam, BAExp14bS2Fam, BAExp14bS3Fam, ite_true]

end Expand

/-- **The expansion identity** (target 2): `𝔼 LWcutg = Σ S1 + Σ S2 + Σ S3` at every size `n`, time `t ∈ [0, BAflowT0]` and
labelling `(σc, σo, ac, ao)`, both charges.  `σc = +`: `G = Ǧ + M` and `BAGGGammaR`, `BAlanlwR` (twice) at `f = X_{[α]} G(σo)_{yx}`,
`∂f = (∂X) G(σo)_{yx} + X ∂G(σo)_{yx}`, `W = W^{(0)} + W^{(1)}`; `σc = -`: the conjugation `baExp14b_cut_conj`. -/
theorem baExp14b_expand_holds (d : ℕ) : BAExp14bExpand d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow n t ht0 ht σc σo ac ao
  cases σc
  · have h : ∫ ω, LWcutg (baFMz sz z) n t true (!σo) ao ac ω ∂(Sizes.seqP (sz.withLam 0)) =
        (∑ k : Fin 6, ∫ ω, BAExp14aS1Fam sz z n t ω k true (!σo) ao ac ∂(Sizes.seqP (sz.withLam 0))) +
          (∑ j : Fin 8, ∫ ω, BAExp14bS2Fam sz z n t ω j true (!σo) ao ac ∂(Sizes.seqP (sz.withLam 0))) +
          (∑ j : Fin 4, ∫ ω, BAExp14bS3Fam sz z n t ω j true (!σo) ao ac ∂(Sizes.seqP (sz.withLam 0))) :=
      BAExp14b_expand_true hκ hflow n ht0 ht (!σo) ao ac
    have hconj : ∀ f : (sz.withLam 0).SeqΩ → ℂ, ∫ ω, star (f ω) ∂(Sizes.seqP (sz.withLam 0)) =
        star (∫ ω, f ω ∂(Sizes.seqP (sz.withLam 0))) := fun f => by
      simpa using integral_conj (f := f) (μ := Sizes.seqP (sz.withLam 0))
    have e : ∫ ω, LWcutg (baFMz sz z) n t false σo ac ao ω ∂(Sizes.seqP (sz.withLam 0)) =
        star (∫ ω, LWcutg (baFMz sz z) n t true (!σo) ao ac ω ∂(Sizes.seqP (sz.withLam 0))) := by
      calc ∫ ω, LWcutg (baFMz sz z) n t false σo ac ao ω ∂(Sizes.seqP (sz.withLam 0))
          = ∫ ω, star (LWcutg (baFMz sz z) n t true (!σo) ao ac ω) ∂(Sizes.seqP (sz.withLam 0)) :=
            integral_congr_ae (Eventually.of_forall fun ω => baExp14b_cut_conj sz z n t σo ac ao ω)
        _ = _ := hconj (fun ω => LWcutg (baFMz sz z) n t true (!σo) ao ac ω)
    rw [e, h]
    simp only [BAExp14aS1Fam, BAExp14bS2Fam, BAExp14bS3Fam, Bool.false_eq_true, ite_false, ite_true, star_add, star_sum, hconj]
  · exact BAExp14b_expand_true hκ hflow n ht0 ht σo ac ao

end RBM.BA

end
