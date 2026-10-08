/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KKernel

/-!
# The Fourier symbol of the propagator kernel `K = |M^{(B)}|²` (BA-P3)

Ticket T2324.  Deterministic layer of the block Anderson model, uniform in `L` and in `g ∈ (0, Λ]`
(paper-delta D614: for `g ≥ (2C)⁻¹` the paper has no lower bound `(Mbound_AO)`, `7_8:1891`).

Cut P3a: the variance lower bound `1 - |m|² ≥ 2dg²/R⁴` (averaged Ward identity and `tr Ψ = 0`,
`tr Ψ² = 2dN`), the coordinate-permutation invariance of `M^{(B)}`, the equal weights of the `2d`
neighbours of `0` and the per-direction bound `K_{0,±e_i} ≥ c g²`.
Cut P3b: the symbol `K̂(θ_k) = Σ_a K_{0a} cos(θ_k · a)`, its gap, laziness and the second moment.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

open Matrix

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The variance lower bound (target 1) -/

section Variance

variable (d L : ℕ) [NeZero L]

private theorem KSymbol_adj_symm (x y : Zd d L) : Adj d L x y ↔ Adj d L y x := by
  simp only [Adj]
  rw [show y - x = -(x - y) by ring, zdistD_neg]

omit [NeZero L] in
private theorem KSymbol_not_adj_self (x : Zd d L) : ¬ Adj d L x x := by
  simp [Adj]

/-- `tr Ψ^{(B)} = 0`: the sum of the eigenvalues. -/
private theorem KSymbol_sum_eig : ∑ i, (PsiB_isHermitian d L).eigenvalues i = 0 := by
  have h := (PsiB_isHermitian d L).trace_eq_sum_eigenvalues
  have h0 : (PsiB d L).trace = 0 := by
    simp only [Matrix.trace, Matrix.diag, PsiB, Matrix.of_apply, KSymbol_not_adj_self d L, ite_false,
      Finset.sum_const_zero]
  rw [h0] at h
  have h2 : ((∑ i, (PsiB_isHermitian d L).eigenvalues i : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]; exact h.symm
  exact_mod_cast h2

/-- `tr (Ψ^{(B)})² = 2dN`: the sum of the squared eigenvalues. -/
private theorem KSymbol_sum_eig_sq (hL : 3 ≤ L) :
    ∑ i, ((PsiB_isHermitian d L).eigenvalues i) ^ 2 = 2 * (d : ℝ) * ((L ^ d : ℕ) : ℝ) := by
  set hΨ := PsiB_isHermitian d L with hΨdef
  set U : Matrix (Zd d L) (Zd d L) ℂ := (hΨ.eigenvectorUnitary : Matrix (Zd d L) (Zd d L) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hspec : PsiB d L = U * diagonal (fun l => (hΨ.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hΨ.spectral_theorem]
    rfl
  have hsq : PsiB d L * PsiB d L = U * diagonal (fun l => ((hΨ.eigenvalues l ^ 2 : ℝ) : ℂ)) * star U := by
    calc PsiB d L * PsiB d L
        = (U * diagonal (fun l => (hΨ.eigenvalues l : ℂ)) * star U)
            * (U * diagonal (fun l => (hΨ.eigenvalues l : ℂ)) * star U) := by rw [← hspec]
      _ = U * (diagonal (fun l => (hΨ.eigenvalues l : ℂ)) * (star U * U)
            * diagonal (fun l => (hΨ.eigenvalues l : ℂ))) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun l => ((hΨ.eigenvalues l ^ 2 : ℝ) : ℂ)) * star U := by
          rw [hUU, Matrix.mul_one, diagonal_mul_diagonal]
          have hf : (fun l => (hΨ.eigenvalues l : ℂ) * (hΨ.eigenvalues l : ℂ))
              = fun l => ((hΨ.eigenvalues l ^ 2 : ℝ) : ℂ) := by
            funext l; push_cast; ring
          rw [hf]
  have htr1 : (PsiB d L * PsiB d L).trace = ∑ l, ((hΨ.eigenvalues l ^ 2 : ℝ) : ℂ) := by
    rw [hsq]
    set D := diagonal (fun l => ((hΨ.eigenvalues l ^ 2 : ℝ) : ℂ)) with hD
    calc (U * D * star U).trace = (U * (D * star U)).trace := by rw [Matrix.mul_assoc]
      _ = ((D * star U) * U).trace := by rw [Matrix.trace_mul_comm]
      _ = (D * (star U * U)).trace := by rw [Matrix.mul_assoc]
      _ = D.trace := by rw [hUU, Matrix.mul_one]
      _ = _ := by rw [hD, Matrix.trace_diagonal]
  have htr2 : (PsiB d L * PsiB d L).trace = ((2 * (d : ℝ) * ((L ^ d : ℕ) : ℝ) : ℝ) : ℂ) := by
    have h1 : ∀ a b : Zd d L, PsiB d L a b * PsiB d L b a = if Adj d L a b then 1 else 0 := by
      intro a b
      by_cases h : Adj d L a b
      · simp [PsiB, h, (KSymbol_adj_symm d L a b).mp h]
      · simp [PsiB, h, mt (KSymbol_adj_symm d L b a).mp h]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, h1]
    have h2 : ∀ a : Zd d L, (∑ b : Zd d L, if Adj d L a b then (1 : ℂ) else 0) = ((2 * d : ℕ) : ℂ) := by
      intro a
      rw [← Finset.sum_filter, Finset.sum_const, card_adj d L hL a]
      simp
    simp only [h2, Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul]
    push_cast
    ring
  rw [htr1] at htr2
  have : ((∑ l, hΨ.eigenvalues l ^ 2 : ℝ) : ℂ) = ((2 * (d : ℝ) * ((L ^ d : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← htr2]; push_cast; rfl
  exact_mod_cast this

/-- The eigenvalues of `Ψ^{(B)}` lie in `[-2d, 2d]` (maximal row sum; a re-proof of the private
`FlowPins_eig_le`, `FlowPins.lean:735`, with `card_adj`). -/
private theorem KSymbol_eig_le (hL : 3 ≤ L) (j : Zd d L) :
    |(PsiB_isHermitian d L).eigenvalues j| ≤ 2 * d := by
  classical
  have hH := PsiB_isHermitian d L
  set v : Zd d L → ℂ := ⇑(hH.eigenvectorBasis j) with hv
  have hvne : ∃ k, v k ≠ 0 := by
    have h0 := (hH.eigenvectorBasis.orthonormal).ne_zero j
    by_contra hno
    push Not at hno
    apply h0
    ext k
    exact hno k
  have heq : PsiB d L *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ) • v := hH.mulVec_eigenvectorBasis j
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => ‖v k‖)
  obtain ⟨k0, hk0⟩ := hvne
  have hvi : v i ≠ 0 := by
    intro h
    apply hk0
    have := hi k0
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hrow := congrFun heq i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  have hnorm : ‖((hH.eigenvalues j : ℝ) : ℂ)‖ * ‖v i‖ ≤ (2 * d : ℝ) * ‖v i‖ := by
    calc ‖((hH.eigenvalues j : ℝ) : ℂ)‖ * ‖v i‖ = ‖((hH.eigenvalues j : ℝ) : ℂ) * v i‖ := (norm_mul _ _).symm
      _ = ‖∑ b, PsiB d L i b * v b‖ := by rw [hrow]
      _ ≤ ∑ b, ‖PsiB d L i b * v b‖ := norm_sum_le _ _
      _ ≤ ∑ b, ‖PsiB d L i b‖ * ‖v i‖ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hi b) (norm_nonneg _)
      _ = ((Finset.univ.filter fun b : Zd d L => Adj d L i b).card : ℝ) * ‖v i‖ := by
          rw [← Finset.sum_mul]
          congr 1
          simp only [PsiB, Matrix.of_apply]
          rw [Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases h : Adj d L i b <;> simp [h]
      _ = (2 * d : ℝ) * ‖v i‖ := by rw [card_adj d L hL i]; push_cast; ring
  have hpos : 0 < ‖v i‖ := norm_pos_iff.mpr hvi
  have := le_of_mul_le_mul_right hnorm hpos
  simpa using this

/-- The real variance identity `Σ_{ij} (x_i - x_j)² = 2n Σ x_i² - 2 (Σ x_i)²`. -/
private theorem KSymbol_double_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∑ i, ∑ j, (x i - x j) ^ 2 = 2 * (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 - 2 * (∑ i, x i) ^ 2 := by
  have h : ∀ i j, (x i - x j) ^ 2 = x i ^ 2 + x j ^ 2 - 2 * (x i * x j) := fun i j => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The complex variance identity `Σ_{ij} |f_i - f_j|² = 2n Σ |f_i|² - 2 |Σ f_i|²`. -/
private theorem KSymbol_double_norm_sq {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ∑ i, ∑ j, ‖f i - f j‖ ^ 2
      = 2 * (Fintype.card ι : ℝ) * ∑ i, ‖f i‖ ^ 2 - 2 * ‖∑ i, f i‖ ^ 2 := by
  have h1 : ∀ i j, ‖f i - f j‖ ^ 2 = ((f i).re - (f j).re) ^ 2 + ((f i).im - (f j).im) ^ 2 := by
    intro i j
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have h2 : ∀ i, ‖f i‖ ^ 2 = (f i).re ^ 2 + (f i).im ^ 2 := by
    intro i
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h3 : ‖∑ i, f i‖ ^ 2 = (∑ i, (f i).re) ^ 2 + (∑ i, (f i).im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    ring
  simp only [h1, h2, h3, Finset.sum_add_distrib]
  rw [KSymbol_double_sq (fun i => (f i).re), KSymbol_double_sq (fun i => (f i).im)]
  ring

/-- **Target 1** (P3a), the variance lower bound (supervisor 0344 Q2; paper-delta D614):
`1 - |m|² = Var(f) = ½ N⁻² Σ_{ij} |f_i - f_j|² ≥ R⁻⁴ Var(v) = 2dg²/R⁴`,
`f_i = (v_i - E - m)⁻¹`, `v = BAspec d L g`, `R = 2dg + |E + m|`. -/
theorem BAvar_lower : ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ → BAReal d L g κ E m →
    2 * (d : ℝ) * g ^ 2 / (2 * (d : ℝ) * g + ‖(E : ℂ) + m‖) ^ 4 ≤ 1 - ‖m‖ ^ 2 := by
  intro d L _ hL hd g κ E m hg hκ hr
  obtain ⟨hself, hκm⟩ := hr
  have hm0 : 0 < m.im := hself.1
  set N : ℝ := ((L ^ d : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    simpa [hN] using (by exact_mod_cast this : (0 : ℝ) < ((L ^ d : ℕ) : ℝ))
  have hcard : (Fintype.card (Zd d L) : ℝ) = N := by rw [card_Zd]
  set w : ℂ := (E : ℂ) + m with hw
  set v : Zd d L → ℝ := BAspec d L g with hv
  set f : Zd d L → ℂ := fun i => ((v i : ℂ) - w)⁻¹ with hf
  set R : ℝ := 2 * d * g + ‖w‖ with hR
  have hwim : w.im = m.im := by simp [hw]
  have hz : ∀ i, (v i : ℂ) - w ≠ 0 := by
    intro i h
    have := congrArg Complex.im h
    simp [hwim] at this
    exact hm0.ne' (by linarith)
  have hzim : ∀ i, ((v i : ℂ) - w).im = -m.im := by
    intro i; simp [hwim]
  -- the mean of `f` is `m`
  have hmean : m = ((N⁻¹ : ℝ) : ℂ) * ∑ i, f i := by
    have h2 := hself.2
    have hzm : ((E : ℂ) + m).im ≠ 0 := by
      have : ((E : ℂ) + m).im = m.im := by simp
      rw [this]; exact hm0.ne'
    rw [BAMB_trace_eq_sum d L g (E : ℂ) m hzm] at h2
    have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((N⁻¹ : ℝ) : ℂ) := by
      rw [hN, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [hc] at h2
    exact h2
  -- Ward: `Σ ‖f_i‖² = N`
  have hfim : ∀ i, (f i).im = m.im * ‖f i‖ ^ 2 := by
    intro i
    simp only [hf]
    rw [Complex.inv_im, hzim i, norm_inv, inv_pow, Complex.sq_norm]
    have := (Complex.normSq_pos.mpr (hz i))
    field_simp
  have hward : ∑ i, ‖f i‖ ^ 2 = N := by
    have h1 : m.im = N⁻¹ * (m.im * ∑ i, ‖f i‖ ^ 2) := by
      have h0 : m.im = N⁻¹ * ∑ i, (f i).im := by
        conv_lhs => rw [hmean]
        rw [Complex.im_ofReal_mul, Complex.im_sum]
      have h4 : ∑ i, (f i).im = m.im * ∑ i, ‖f i‖ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hfim i
      rw [← h4]; exact h0
    have h2 : m.im * (N * 1) = m.im * (∑ i, ‖f i‖ ^ 2) := by
      calc m.im * (N * 1) = N * m.im := by ring
        _ = N * (N⁻¹ * (m.im * ∑ i, ‖f i‖ ^ 2)) := by rw [← h1]
        _ = m.im * (∑ i, ‖f i‖ ^ 2) := by field_simp
    have h3 := mul_left_cancel₀ hm0.ne' h2
    linarith
  have hnormm : ‖∑ i, f i‖ ^ 2 = N ^ 2 * ‖m‖ ^ 2 := by
    have : ∑ i, f i = (N : ℂ) * m := by
      rw [hmean, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hNpos.ne']
      simp
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos, mul_pow]
  have hdouble : ∑ i, ∑ j, ‖f i - f j‖ ^ 2 = 2 * N ^ 2 * (1 - ‖m‖ ^ 2) := by
    rw [KSymbol_double_norm_sq, hcard, hward, hnormm]
    ring
  -- the pairwise lower bound
  have hvb : ∀ i, ‖(v i : ℂ) - w‖ ≤ R := by
    intro i
    have h1 : |v i| ≤ 2 * d * g := by
      have := KSymbol_eig_le d L hL i
      calc |v i| = |g| * |(PsiB_isHermitian d L).eigenvalues i| := by rw [hv, BAspec, abs_mul]
        _ ≤ g * (2 * d) := by rw [abs_of_pos hg]; exact mul_le_mul_of_nonneg_left this hg.le
        _ = 2 * d * g := by ring
    calc ‖(v i : ℂ) - w‖ ≤ ‖(v i : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ = |v i| + ‖w‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ R := by rw [hR]; linarith
  have hRpos : 0 < R := lt_of_lt_of_le (norm_pos_iff.mpr (hz 0)) (hvb 0)
  have hpair : ∀ i j, (v i - v j) ^ 2 / R ^ 4 ≤ ‖f i - f j‖ ^ 2 := by
    intro i j
    have hfd : f i - f j = (((v j - v i : ℝ) : ℂ)) / (((v i : ℂ) - w) * ((v j : ℂ) - w)) := by
      simp only [hf]
      rw [inv_sub_inv (hz i) (hz j)]
      congr 1
      push_cast
      ring
    have hn : ‖f i - f j‖ = |v j - v i| / (‖(v i : ℂ) - w‖ * ‖(v j : ℂ) - w‖) := by
      rw [hfd, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hpi : 0 < ‖(v i : ℂ) - w‖ := norm_pos_iff.mpr (hz i)
    have hpj : 0 < ‖(v j : ℂ) - w‖ := norm_pos_iff.mpr (hz j)
    have h1 : |v j - v i| / R ^ 2 ≤ ‖f i - f j‖ := by
      rw [hn]
      refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
      rw [sq]
      exact mul_le_mul (hvb i) (hvb j) hpj.le hRpos.le
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    refine le_trans (le_of_eq ?_) h2
    rw [div_pow, sq_abs, ← pow_mul, show (v i - v j) ^ 2 = (v j - v i) ^ 2 by ring]
  have hsumv : ∑ i, v i = 0 := by
    simp only [hv, BAspec, ← Finset.mul_sum, KSymbol_sum_eig, mul_zero]
  have hsumv2 : ∑ i, v i ^ 2 = g ^ 2 * (2 * (d : ℝ) * N) := by
    simp only [hv, BAspec, mul_pow, ← Finset.mul_sum, KSymbol_sum_eig_sq d L hL, hN]
  have hlow : 4 * (d : ℝ) * g ^ 2 * N ^ 2 / R ^ 4 ≤ ∑ i, ∑ j, ‖f i - f j‖ ^ 2 := by
    have h1 : ∑ i, ∑ j, (v i - v j) ^ 2 / R ^ 4 = 4 * (d : ℝ) * g ^ 2 * N ^ 2 / R ^ 4 := by
      simp only [← Finset.sum_div]
      rw [KSymbol_double_sq, hcard, hsumv, hsumv2]
      ring
    rw [← h1]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
  rw [hdouble] at hlow
  have hN2 : 0 < N ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)] at hlow ⊢
  nlinarith [hlow, hN2]

end Variance

/-! ## 2. Coordinate permutations (target 2) and the equal weights of the neighbours (target 3) -/

section Perm

variable (d L : ℕ) [NeZero L]

/-- The coordinate permutation `x ↦ x ∘ σ` of `Z_L^d` as an equivalence. -/
private def KSymbol_permEquiv (σ : Equiv.Perm (Fin d)) : Zd d L ≃ Zd d L where
  toFun x := fun j => x (σ j)
  invFun x := fun j => x (σ.symm j)
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

omit [NeZero L] in
private theorem KSymbol_adj_perm (σ : Equiv.Perm (Fin d)) (x y : Zd d L) :
    Adj d L (KSymbol_permEquiv d L σ x) (KSymbol_permEquiv d L σ y) ↔ Adj d L x y := by
  simp only [Adj, zdistD]
  have h : (KSymbol_permEquiv d L σ x - KSymbol_permEquiv d L σ y) = fun j => (x - y) (σ j) := rfl
  rw [h]
  have := Equiv.sum_comp σ (fun j => zdist L ((x - y) j))
  rw [this]

private theorem KSymbol_BAMB_eq (g : ℝ) (z m : ℂ) :
    BAMB d L g z m = ((g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ))⁻¹ := by
  unfold BAMB Mres
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- **Target 2** (P3a): `M^{(B)}` is invariant under coordinate permutations of `Z_L^d`
(a coordinate permutation is an automorphism of the torus adjacency). -/
theorem BAMB_perm : ∀ (d L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin d)) (g : ℝ) (z m : ℂ) (a b : Zd d L),
    BAMB d L g z m (fun j => a (σ j)) (fun j => b (σ j)) = BAMB d L g z m a b := by
  intro d L _ σ g z m a b
  set e := KSymbol_permEquiv d L σ with he
  have hA : ((g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ)).submatrix e e
      = (g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    ext x y
    have h1 : (e x = e y) ↔ (x = y) := e.injective.eq_iff
    have h2 : Adj d L (e x) (e y) ↔ Adj d L x y := KSymbol_adj_perm d L σ x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, PsiB,
      Matrix.of_apply, Matrix.one_apply, h1]
    simp only [h2]
  have h2 := Matrix.inv_submatrix_equiv
    ((g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ)) e e
  rw [hA] at h2
  rw [KSymbol_BAMB_eq]
  have h3 := congrFun (congrFun h2 a) b
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

theorem BAK_perm (σ : Equiv.Perm (Fin d)) (g E : ℝ) (m : ℂ) (a b : Zd d L) :
    BAK d L g E m (fun j => a (σ j)) (fun j => b (σ j)) = BAK d L g E m a b := by
  rw [BAK_apply, BAK_apply, BAMB_perm d L σ g (E : ℂ) m a b]

omit [NeZero L] in
private theorem KSymbol_unitVec_perm (σ : Equiv.Perm (Fin d)) (i : Fin d) (s : Bool) :
    (fun j => unitVec d L (i, s) (σ j)) = unitVec d L (σ.symm i, s) := by
  funext j
  simp only [unitVec, Pi.single_apply]
  by_cases h : j = σ.symm i
  · have : σ j = i := by rw [h]; simp
    simp [h, this]
  · have : ¬ σ j = i := fun h' => h (by rw [← h']; simp)
    simp [h, this]

private theorem KSymbol_dir_swap (g E : ℝ) (m : ℂ) (i j : Fin d) (s : Bool) :
    BAK d L g E m 0 (unitVec d L (i, s)) = BAK d L g E m 0 (unitVec d L (j, s)) := by
  have h := BAK_perm d L (Equiv.swap i j) g E m 0 (unitVec d L (i, s))
  rw [KSymbol_unitVec_perm, Equiv.symm_swap, Equiv.swap_apply_left] at h
  rw [← h]
  rfl

private theorem KSymbol_dir_sign (g E : ℝ) (m : ℂ) (i : Fin d) (s t : Bool) :
    BAK d L g E m 0 (unitVec d L (i, s)) = BAK d L g E m 0 (unitVec d L (i, t)) := by
  have hneg : unitVec d L (i, false) = -unitVec d L (i, true) := by
    simp [unitVec, Pi.single_neg]
  cases s <;> cases t
  · rfl
  · rw [hneg, BAK_zero_neg]
  · rw [hneg, BAK_zero_neg]
  · rfl

private theorem KSymbol_dir_all (g E : ℝ) (m : ℂ) (p q : Fin d × Bool) :
    BAK d L g E m 0 (unitVec d L p) = BAK d L g E m 0 (unitVec d L q) := by
  obtain ⟨i, s⟩ := p
  obtain ⟨j, t⟩ := q
  rw [KSymbol_dir_swap d L g E m i j s, KSymbol_dir_sign d L g E m j s t]

omit [NeZero L] in
private theorem KSymbol_filter_adj_zero (hL : 3 ≤ L) [NeZero L] :
    (Finset.univ.filter fun b : Zd d L => Adj d L 0 b) = Finset.univ.image (unitVec d L) := by
  rw [← filter_zdistD_eq_one hL]
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Adj, zero_sub, zdistD_neg]

/-- **Target 3** (P3a): every neighbour of `0` carries the same weight. -/
theorem BAK_dir_eq : ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g E : ℝ) (m : ℂ) (i : Fin d) (s : Bool),
    BAK d L g E m 0 (unitVec d L (i, s)) =
      (2 * (d : ℝ))⁻¹ * ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L 0 b), BAK d L g E m 0 b := by
  intro d L _ hL hd g E m i s
  rw [KSymbol_filter_adj_zero d L hL, Finset.sum_image (fun p _ q _ h => unitVec_injective hL h)]
  have h1 : ∀ p ∈ (Finset.univ : Finset (Fin d × Bool)),
      BAK d L g E m 0 (unitVec d L p) = BAK d L g E m 0 (unitVec d L (i, s)) :=
    fun p _ => KSymbol_dir_all d L g E m p (i, s)
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  push_cast
  field_simp

end Perm

/-! ## 3. The per-direction bound (target 4) -/

section Direction

/-- `R = 2dg + |E + m| ≤ 4dΛ + 3` for a real-axis solution, `0 < g ≤ Λ`
(`baSelf_none_of_gt`: `|E| ≤ 2 + 2dg`; `BAm_norm_le_one`: `|m| ≤ 1`). -/
private theorem KSymbol_R_le (d L : ℕ) [NeZero L] (Λ g E : ℝ) (m : ℂ) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (h : BASelf d L g (E : ℂ) m) :
    2 * (d : ℝ) * g + ‖(E : ℂ) + m‖ ≤ 4 * (d : ℝ) * Λ + 3 := by
  have hm1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) h
  have hE : |E| ≤ 2 + 2 * (d : ℝ) * g := by
    by_contra hc
    push Not at hc
    exact baSelf_none_of_gt d L g E (by rwa [abs_of_pos hg]) m h
  have h1 : ‖(E : ℂ) + m‖ ≤ |E| + ‖m‖ := by
    calc ‖(E : ℂ) + m‖ ≤ ‖(E : ℂ)‖ + ‖m‖ := norm_add_le _ _
      _ = |E| + ‖m‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left hgΛ hd0]

/-- The explicit constant of target 4: `c = κ²/(4(4dΛ + 3)⁸)`:
`K_{0,±e_i} ≥ c g²` (`BAK_adj_sum_ge`, target 1, target 3). -/
private theorem KSymbol_dir_ge_explicit (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ)
    (m : ℂ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (i : Fin d) (s : Bool) :
    κ ^ 2 / (4 * (4 * (d : ℝ) * Λ + 3) ^ 8) * g ^ 2 ≤ BAK d L g E m 0 (unitVec d L (i, s)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set R : ℝ := 2 * (d : ℝ) * g + ‖(E : ℂ) + m‖ with hR
  set R0 : ℝ := 4 * (d : ℝ) * Λ + 3 with hR0
  have hRpos : 0 < R := by positivity
  have hRR0 : R ≤ R0 := KSymbol_R_le d L Λ g E m hg hgΛ hr.1
  have hV := BAvar_lower d L hL hd g κ E m hg hκ hr
  have hVa : 0 ≤ 2 * (d : ℝ) * g ^ 2 / R ^ 4 := by positivity
  have hadj := BAK_adj_sum_ge d L hL hd g κ E m hg hκ hr 0
  have hsq : (κ * (2 * (d : ℝ) * g ^ 2 / R ^ 4)) ^ 2 ≤ (κ * (1 - ‖m‖ ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hV hκ.le) 2
  have h1 : κ ^ 2 * g ^ 2 / (4 * R ^ 8) ≤ BAK d L g E m 0 (unitVec d L (i, s)) := by
    rw [BAK_dir_eq d L hL hd g E m i s]
    have h2 : (2 * (d : ℝ))⁻¹ * ((κ * (2 * (d : ℝ) * g ^ 2 / R ^ 4)) ^ 2 / (8 * (d : ℝ) * g ^ 2))
        = κ ^ 2 * g ^ 2 / (4 * R ^ 8) := by
      field_simp
      ring
    rw [← h2]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hadj) (by positivity)
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have h3 : κ ^ 2 / (4 * R0 ^ 8) * g ^ 2 ≤ κ ^ 2 * g ^ 2 / (4 * R ^ 8) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by have := pow_le_pow_left₀ hRpos.le hRR0 8; linarith)
  exact h3.trans h1

/-- **Target 4** (P3a): the per-direction neighbour bound `K_{0,±e_i} ≥ c g²`, uniformly in `L` and
`g ∈ (0, Λ]` (paper-delta D614: no source in the paper for `g ≥ (2C)⁻¹`). -/
theorem BAK_dir_ge : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ (i : Fin d) (s : Bool), c * g ^ 2 ≤ BAK d L g E m 0 (unitVec d L (i, s)) := by
  intro d hd Λ κ hΛ hκ
  refine ⟨κ ^ 2 / (4 * (4 * (d : ℝ) * Λ + 3) ^ 8), by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr i s
  exact KSymbol_dir_ge_explicit d L hL hd Λ g κ E m hg hgΛ hκ hr i s

end Direction

/-! ## 4. The symbol of `K` on the dual torus (targets 5-7) -/

section Defs

variable (d L : ℕ) [NeZero L]

/-- The Fourier symbol of `K` on the dual torus, `K̂(θ_k) = Σ_a K_{0a} cos(θ_k · a)`, `θ_k = 2π k / L`
(real: `K_{0,-a} = K_{0a}`, `BAK_zero_neg`). -/
def BAKhat (g E : ℝ) (m : ℂ) (k : Zd d L) : ℝ :=
  ∑ a : Zd d L, BAK d L g E m 0 a *
    Real.cos (2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ))

/-- `|θ_k|²` with each coordinate taken in `(-π, π]`: `Σ_j (2π |k_j|_L / L)²`. -/
def BAthetaSq (k : Zd d L) : ℝ :=
  ∑ j, (2 * Real.pi * (zdist L (k j) : ℝ) / L) ^ 2

end Defs

section Symbol

variable (d L : ℕ) [NeZero L]

/-- The phase `θ_k · a = 2π/L Σ_j k_j a_j` (representatives in `[0, L)`). -/
private def KSymbol_phi (k a : Zd d L) : ℝ :=
  2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ)

private theorem KSymbol_Khat_eq (g E : ℝ) (m : ℂ) (k : Zd d L) :
    BAKhat d L g E m k = ∑ a, BAK d L g E m 0 a * Real.cos (KSymbol_phi d L k a) := rfl

private theorem KSymbol_phi_zero (k : Zd d L) : KSymbol_phi d L k 0 = 0 := by
  simp [KSymbol_phi]

/-- `θ_k · (-a) + θ_k · a ∈ 2π ℤ`: `(-a)_j.val = L - a_j.val` for `a_j ≠ 0`. -/
private theorem KSymbol_phi_neg (k a : Zd d L) :
    ∃ n : ℕ, KSymbol_phi d L k (-a) + KSymbol_phi d L k a = n * (2 * Real.pi) := by
  refine ⟨∑ j, (k j).val * (if a j = 0 then 0 else 1), ?_⟩
  have hj : ∀ j, ((k j).val : ℝ) * (((-a) j).val : ℝ) + ((k j).val : ℝ) * ((a j).val : ℝ)
      = (L : ℝ) * (((k j).val * (if a j = 0 then 0 else 1) : ℕ) : ℝ) := by
    intro j
    have hv : (a j).val < L := ZMod.val_lt _
    by_cases h : a j = 0
    · simp [h]
    · have h1 := ZMod.neg_val (a j)
      simp only [Pi.neg_apply, h1, h, ite_false]
      push_cast [Nat.cast_sub hv.le]
      ring
  unfold KSymbol_phi
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp_rw [hj]
  rw [← Finset.mul_sum]
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  push_cast
  field_simp

private theorem KSymbol_sin_neg (k a : Zd d L) :
    Real.sin (KSymbol_phi d L k (-a)) = -Real.sin (KSymbol_phi d L k a) := by
  obtain ⟨n, hn⟩ := KSymbol_phi_neg d L k a
  have : KSymbol_phi d L k (-a) = n * (2 * Real.pi) - KSymbol_phi d L k a := by linarith
  rw [this, Real.sin_nat_mul_two_pi_sub]

private theorem KSymbol_cos_neg (k a : Zd d L) :
    Real.cos (KSymbol_phi d L k (-a)) = Real.cos (KSymbol_phi d L k a) := by
  obtain ⟨n, hn⟩ := KSymbol_phi_neg d L k a
  have : KSymbol_phi d L k (-a) = n * (2 * Real.pi) - KSymbol_phi d L k a := by linarith
  rw [this, Real.cos_nat_mul_two_pi_sub]

private theorem KSymbol_sin_sum (g E : ℝ) (m : ℂ) (k : Zd d L) :
    ∑ a, BAK d L g E m 0 a * Real.sin (KSymbol_phi d L k a) = 0 := by
  have h := Equiv.sum_comp (Equiv.neg (Zd d L)) (fun a => BAK d L g E m 0 a * Real.sin (KSymbol_phi d L k a))
  simp only [Equiv.neg_apply, BAK_zero_neg, KSymbol_sin_neg, mul_neg, Finset.sum_neg_distrib] at h
  linarith

/-- **Target 5** (P3b): `BAKhat` is the Fourier transform of the row `K_{0,·}` (the sine part vanishes). -/
theorem BAKhat_eq : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (k : Zd d L),
    (∑ a : Zd d L, (BAK d L g E m 0 a : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ))) =
      (BAKhat d L g E m k : ℂ) := by
  intro d L _ g E m k
  have hterm : ∀ a : Zd d L, (BAK d L g E m 0 a : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ))
      = ((BAK d L g E m 0 a * Real.cos (KSymbol_phi d L k a) : ℝ) : ℂ)
        + ((BAK d L g E m 0 a * Real.sin (KSymbol_phi d L k a) : ℝ) : ℂ) * Complex.I := by
    intro a
    have he : 2 * (Real.pi : ℂ) * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ)
        = ((KSymbol_phi d L k a : ℝ) : ℂ) * Complex.I := by
      unfold KSymbol_phi
      push_cast
      ring
    rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum, KSymbol_sin_sum, KSymbol_Khat_eq]
  push_cast
  simp

/-- **Target 7** (P3b): laziness `1 + K̂(θ) ≥ 2κ²`. -/
theorem BAK_lazy : ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m →
    ∀ k : Zd d L, 2 * κ ^ 2 ≤ 1 + BAKhat d L g E m k := by
  intro d L _ g κ E m hκ hr k
  have hrow := BAK_row_sum d L g E m hr.1 0
  have h1 : 1 + BAKhat d L g E m k = ∑ a, BAK d L g E m 0 a * (1 + Real.cos (KSymbol_phi d L k a)) := by
    rw [KSymbol_Khat_eq]
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hrow]
  rw [h1]
  have h2 : BAK d L g E m 0 0 * (1 + Real.cos (KSymbol_phi d L k 0))
      ≤ ∑ a, BAK d L g E m 0 a * (1 + Real.cos (KSymbol_phi d L k a)) :=
    Finset.single_le_sum (f := fun a => BAK d L g E m 0 a * (1 + Real.cos (KSymbol_phi d L k a)))
      (fun a _ => mul_nonneg (BAK_nonneg d L g E m 0 a) (by linarith [Real.neg_one_le_cos (KSymbol_phi d L k a)]))
      (Finset.mem_univ 0)
  refine le_trans ?_ h2
  rw [KSymbol_phi_zero, Real.cos_zero]
  have := (BAK_diag_bounds d L g κ E m hκ hr 0).1
  linarith

end Symbol

/-! ## 5. The gap (target 6) -/

section Gap

/-- `1 - cos x ≥ 2x²/π²` on `[0, π]` (Jordan's inequality at `x/2`). -/
private theorem KSymbol_one_sub_cos_ge (x : ℝ) (h0 : 0 ≤ x) (hπ : x ≤ Real.pi) :
    2 * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hpi := Real.pi_pos
  have hs : 2 / Real.pi * (x / 2) ≤ Real.sin (x / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ (by positivity) hs 2
  have h2 := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h2
  have h3 : (2 / Real.pi * (x / 2)) ^ 2 = x ^ 2 / Real.pi ^ 2 := by
    field_simp
  have h4 : 2 * x ^ 2 / Real.pi ^ 2 = 2 * (x ^ 2 / Real.pi ^ 2) := by ring
  rw [h4]
  nlinarith [hsq, h2, h3]

private theorem KSymbol_zdist_two_le {L : ℕ} (u : ZMod L) [NeZero L] : 2 * zdist L u ≤ L := by
  simp only [zdist]
  omega

private theorem KSymbol_cos_zdist {L : ℕ} [NeZero L] (u : ZMod L) :
    Real.cos (2 * Real.pi * (u.val : ℝ) / L) = Real.cos (2 * Real.pi * (zdist L u : ℝ) / L) := by
  have hv : u.val < L := ZMod.val_lt u
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  by_cases h : u.val ≤ L - u.val
  · have : zdist L u = u.val := by simp only [zdist]; exact min_eq_left h
    rw [this]
  · have : zdist L u = L - u.val := by simp only [zdist]; exact min_eq_right (by omega)
    rw [this, Nat.cast_sub hv.le]
    have h2 : 2 * Real.pi * ((L : ℝ) - (u.val : ℝ)) / L = 2 * Real.pi - 2 * Real.pi * (u.val : ℝ) / L := by
      field_simp
    rw [h2, Real.cos_two_pi_sub]

private theorem KSymbol_cos_unitVec {L : ℕ} [NeZero L] (d : ℕ) (hL : 3 ≤ L) (k : Zd d L) (i : Fin d) (s : Bool) :
    Real.cos (KSymbol_phi d L k (unitVec d L (i, s))) = Real.cos (2 * Real.pi * ((k i).val : ℝ) / L) := by
  have hneg : unitVec d L (i, false) = -unitVec d L (i, true) := by
    simp [unitVec, Pi.single_neg]
  have htrue : KSymbol_phi d L k (unitVec d L (i, true)) = 2 * Real.pi * ((k i).val : ℝ) / L := by
    unfold KSymbol_phi
    rw [Finset.sum_eq_single i]
    · simp only [unitVec, Pi.single_eq_same, ite_true, val_one_of_three_le hL]
      push_cast
      ring
    · intro j _ hj
      simp [unitVec, Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  cases s
  · rw [hneg, KSymbol_cos_neg, htrue]
  · rw [htrue]

/-- **Target 6** (P3b): the spectral gap `1 - K̂(θ) ≥ c g² |θ|²`, uniformly in `L` and `g ∈ (0, Λ]`
(`c = 4κ²/(π² · 4(4dΛ + 3)⁸)`; paper-delta D614). -/
theorem BAK_gap : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ k : Zd d L, c * g ^ 2 * BAthetaSq d L k ≤ 1 - BAKhat d L g E m k := by
  intro d hd Λ κ hΛ hκ
  set c0 : ℝ := κ ^ 2 / (4 * (4 * (d : ℝ) * Λ + 3) ^ 8) with hc0
  have hc0pos : 0 < c0 := by positivity
  have hpi := Real.pi_pos
  refine ⟨4 * c0 / Real.pi ^ 2, by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr k
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hrow := BAK_row_sum d L g E m hr.1 0
  have h1 : 1 - BAKhat d L g E m k
      = ∑ a, BAK d L g E m 0 a * (1 - Real.cos (KSymbol_phi d L k a)) := by
    rw [KSymbol_Khat_eq]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hrow]
  rw [h1]
  have h2 : ∑ p : Fin d × Bool, BAK d L g E m 0 (unitVec d L p)
        * (1 - Real.cos (KSymbol_phi d L k (unitVec d L p)))
      ≤ ∑ a, BAK d L g E m 0 a * (1 - Real.cos (KSymbol_phi d L k a)) := by
    rw [← Finset.sum_image (f := fun a => BAK d L g E m 0 a * (1 - Real.cos (KSymbol_phi d L k a)))
      (s := Finset.univ) (g := unitVec d L) (fun p _ q _ h => unitVec_injective hL h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => mul_nonneg (BAK_nonneg d L g E m 0 a)
        (by linarith [Real.cos_le_one (KSymbol_phi d L k a)]))
  refine le_trans ?_ h2
  rw [Fintype.sum_prod_type, BAthetaSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_bool]
  set θ : ℝ := 2 * Real.pi * (zdist L (k i) : ℝ) / L with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθπ : θ ≤ Real.pi := by
    rw [hθ, div_le_iff₀ hL0]
    have : 2 * (zdist L (k i) : ℝ) ≤ L := by exact_mod_cast KSymbol_zdist_two_le (k i)
    nlinarith
  have hcos : ∀ s, Real.cos (KSymbol_phi d L k (unitVec d L (i, s))) = Real.cos θ := by
    intro s
    rw [KSymbol_cos_unitVec d hL k i s, hθ, KSymbol_cos_zdist]
  have hge := KSymbol_one_sub_cos_ge θ hθ0 hθπ
  have hK : ∀ s, c0 * g ^ 2 ≤ BAK d L g E m 0 (unitVec d L (i, s)) := fun s =>
    KSymbol_dir_ge_explicit d L hL hd Λ g κ E m hg hgΛ hκ hr i s
  have hterm : ∀ s, c0 * g ^ 2 * (2 * θ ^ 2 / Real.pi ^ 2)
      ≤ BAK d L g E m 0 (unitVec d L (i, s)) * (1 - Real.cos (KSymbol_phi d L k (unitVec d L (i, s)))) := by
    intro s
    rw [hcos s]
    exact mul_le_mul (hK s) hge (by positivity) (BAK_nonneg d L g E m 0 _)
  have := add_le_add (hterm true) (hterm false)
  calc 4 * c0 / Real.pi ^ 2 * g ^ 2 * θ ^ 2
      = c0 * g ^ 2 * (2 * θ ^ 2 / Real.pi ^ 2) + c0 * g ^ 2 * (2 * θ ^ 2 / Real.pi ^ 2) := by ring
    _ ≤ _ := this

end Gap

/-! ## 6. The second moment (target 8) -/

section SecondMoment

/-- **Target 8** (P3b): the second moment `Σ_a K_{0a} |a|² ≤ C g²`, uniformly in `L` and `g ∈ (0, Λ]`
(`r² ≤ (2/μ²) e^{μ r}` and `BAK_exp_moment_le`, the diagonal term cancelling). -/
theorem BAK_second_moment : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2 ≤ C * g ^ 2 := by
  intro d hd Λ κ hΛ hκ
  have hd0 : 0 < d := by omega
  set μ : ℝ := BAct_rate d Λ κ with hμ
  have hμpos : 0 < μ := BAct_rate_pos d Λ κ hd0 hΛ hκ
  set C0 : ℝ := 2 / μ ^ 2 * (BAp5s_A d Λ κ * BAp5s_S d Λ κ) with hC0
  refine ⟨max C0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro L _ hL g E m hg hgΛ hr
  have hmom := BAK_exp_moment_le d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr μ hμpos.le le_rfl 0
  have hsplit : ∀ f : Zd d L → ℝ, ∑ b, f b = f 0 + ∑ b ∈ Finset.univ.erase 0, f b := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have hdiag : BAK d L g E m 0 0 = ‖m‖ ^ 2 := BAK_diag d L g E m hr.1 0
  -- pointwise: `r² ≤ (2/μ²) e^{μ r}`
  have hpt : ∀ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2
      ≤ 2 / μ ^ 2 * (BAK d L g E m 0 a * Real.exp (μ * (zdistD d L (0 - a) : ℝ))) := by
    intro a
    rw [zero_sub, zdistD_neg]
    have hr0 : (0 : ℝ) ≤ (zdistD d L a : ℝ) := Nat.cast_nonneg _
    have he := Real.quadratic_le_exp_of_nonneg (mul_nonneg hμpos.le hr0)
    have h2 : (zdistD d L a : ℝ) ^ 2 ≤ 2 / μ ^ 2 * Real.exp (μ * (zdistD d L a : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [he, mul_nonneg hμpos.le hr0]
    calc BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2
        ≤ BAK d L g E m 0 a * (2 / μ ^ 2 * Real.exp (μ * (zdistD d L a : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (BAK_nonneg d L g E m 0 a)
      _ = _ := by ring
  have hsum : ∑ a ∈ Finset.univ.erase (0 : Zd d L), BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2
      ≤ 2 / μ ^ 2 * ∑ a ∈ Finset.univ.erase (0 : Zd d L),
          BAK d L g E m 0 a * Real.exp (μ * (zdistD d L (0 - a) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hpt a
  -- the `a = 0` term of the left side vanishes and that of the right side is `|m|²`
  have hL0 : BAK d L g E m 0 0 * (zdistD d L 0 : ℝ) ^ 2 = 0 := by simp
  have hR0 : BAK d L g E m 0 0 * Real.exp (μ * (zdistD d L (0 - 0) : ℝ)) = ‖m‖ ^ 2 := by
    rw [sub_self, zdistD_zero, hdiag]; simp
  have hmom' : ∑ b, BAK d L g E m 0 b * Real.exp (μ * (zdistD d L (0 - b) : ℝ))
      ≤ ‖m‖ ^ 2 + BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ := hmom
  rw [hsplit (fun a => BAK d L g E m 0 a * Real.exp (μ * (zdistD d L (0 - a) : ℝ))), hR0] at hmom'
  have hrest : ∑ b ∈ Finset.univ.erase (0 : Zd d L), BAK d L g E m 0 b * Real.exp (μ * (zdistD d L (0 - b) : ℝ))
      ≤ BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ := by linarith
  have h1 : ∑ a ∈ Finset.univ.erase (0 : Zd d L), BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2
      ≤ 2 / μ ^ 2 * (BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ) :=
    le_trans hsum (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  calc ∑ a, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2
      = BAK d L g E m 0 0 * (zdistD d L 0 : ℝ) ^ 2
        + ∑ a ∈ Finset.univ.erase (0 : Zd d L), BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2 :=
        hsplit (fun a => BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2)
    _ ≤ C0 * g ^ 2 := by
        rw [hL0, zero_add, hC0]
        calc _ ≤ 2 / μ ^ 2 * (BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ) := h1
          _ = _ := by ring
    _ ≤ max C0 1 * g ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end SecondMoment

/-! ## 7. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, data `P` of `KKernelInst`) -/

namespace KSymbolInst

open RBM.BA.MFixedPointInst

/-- Target 1 at `P`: `2dg²/R⁴ ≤ 1 - |m|²`. -/
theorem inst_var_lower :
    2 * (3 : ℝ) * P.g0 ^ 2 / (2 * (3 : ℝ) * P.g0 + ‖(P.E : ℂ) + P.m0‖) ^ 4 ≤ 1 - ‖P.m0‖ ^ 2 := by
  have h := BAvar_lower 3 4 (by norm_num) (by norm_num) P.g0 P.m0.im P.E P.m0 P.g0_pos P.real.1.1 P.real
  simpa using h

/-- Target 2 at the transposition `(0 1)` of the coordinates, entry `(e₁, e₂)`. -/
theorem inst_perm :
    BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (fun j => (![1, 0, 0] : Zd 3 4) (Equiv.swap (0 : Fin 3) 1 j))
        (fun j => (![0, 1, 0] : Zd 3 4) (Equiv.swap (0 : Fin 3) 1 j))
      = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 ![1, 0, 0] ![0, 1, 0] :=
  BAMB_perm 3 4 (Equiv.swap 0 1) P.g0 (P.E : ℂ) P.m0 ![1, 0, 0] ![0, 1, 0]

/-- Target 3 at `P`: the weight of `e₁` is the average over the six neighbours of `0`. -/
theorem inst_dir_eq :
    BAK 3 4 P.g0 P.E P.m0 0 (unitVec 3 4 (0, true)) =
      (2 * (3 : ℝ))⁻¹ * ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b), BAK 3 4 P.g0 P.E P.m0 0 b :=
  BAK_dir_eq 3 4 (by norm_num) (by norm_num) P.g0 P.E P.m0 0 true

/-- Target 4 at `P`, `Λ = 10`: a positive `c` with `c g² ≤ K_{0,-e₂}`. -/
theorem inst_dir_ge :
    ∃ c : ℝ, 0 < c ∧ c * P.g0 ^ 2 ≤ BAK 3 4 P.g0 P.E P.m0 0 (unitVec 3 4 (1, false)) := by
  obtain ⟨c, hc, h⟩ := BAK_dir_ge 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨c, hc, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 false⟩

/-- Target 5 at `P`, `k = (1, 0, 0)`. -/
theorem inst_Khat_eq :
    (∑ a : Zd 3 4, (BAK 3 4 P.g0 P.E P.m0 0 a : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ) * ∑ j, (((![1, 0, 0] : Zd 3 4) j).val : ℂ) * ((a j).val : ℂ))) =
      (BAKhat 3 4 P.g0 P.E P.m0 ![1, 0, 0] : ℂ) :=
  BAKhat_eq 3 4 P.g0 P.E P.m0 ![1, 0, 0]

/-- `|θ_k|² > 0` at `k = (1, 0, 0)` (nondegenerate momentum). -/
theorem inst_thetaSq_pos : 0 < BAthetaSq 3 4 ![1, 0, 0] := by
  unfold BAthetaSq
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨0, Finset.mem_univ _, ?_⟩
  have h1 : zdist 4 ((![1, 0, 0] : Zd 3 4) 0) = 1 := by decide
  rw [h1]
  positivity

/-- Target 6 at `P`, `Λ = 10`, `k = (1, 0, 0)`: the gap. -/
theorem inst_gap :
    ∃ c : ℝ, 0 < c ∧ c * P.g0 ^ 2 * BAthetaSq 3 4 ![1, 0, 0] ≤ 1 - BAKhat 3 4 P.g0 P.E P.m0 ![1, 0, 0] := by
  obtain ⟨c, hc, h⟩ := BAK_gap 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨c, hc, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real ![1, 0, 0]⟩

/-- Target 7 at `P`, `k = (1, 0, 0)`: laziness. -/
theorem inst_lazy :
    2 * P.m0.im ^ 2 ≤ 1 + BAKhat 3 4 P.g0 P.E P.m0 ![1, 0, 0] :=
  BAK_lazy 3 4 P.g0 P.m0.im P.E P.m0 P.real.1.1 P.real ![1, 0, 0]

/-- Target 8 at `P`, `Λ = 10`: the second moment. -/
theorem inst_second_moment :
    ∃ C : ℝ, 0 < C ∧ ∑ a : Zd 3 4, BAK 3 4 P.g0 P.E P.m0 0 a * (zdistD 3 4 a : ℝ) ^ 2 ≤ C * P.g0 ^ 2 := by
  obtain ⟨C, hC, h⟩ := BAK_second_moment 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, hC, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real⟩

/-- `K̂(0) = 1` at `P` (the row sum). -/
theorem inst_Khat_zero : BAKhat 3 4 P.g0 P.E P.m0 0 = 1 := by
  have h := BAK_row_sum 3 4 P.g0 P.E P.m0 P.real.1 0
  rw [KSymbol_Khat_eq]
  simpa [KSymbol_phi] using h

end KSymbolInst

end RBM.BA
