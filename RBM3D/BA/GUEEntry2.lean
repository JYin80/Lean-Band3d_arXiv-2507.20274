/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEEntry

/-!
# The block Anderson entry layer of the GUE phase, probabilistic part (T2515, row b)

BA twin of `Universality/GUEPhase/EntryTail.lean` and `EntryTailMain.lean`, on top of the
deterministic part in `BA/GUEEntry.lean`.

* `mixEntry_detBA`: the deterministic bound of `mix_detBA` stated on the fine lattice `Idx d
  L W` through `GUEEntry_llErr` and `GUEEntry_maxLoop` (the form of the tails).
* Target 11, `mixMatBA` (`= g Ψ + mixMat (sz.withLam 0) n a b ω`) with
  `GUEEntry_mixMatBA_eq_Xmat`, `GUEEntry_mixMatBA_isHermitian` and
  `GUEEntry_ouMatC_ba_eq_mixMatBA`; the Gaussian tails of the auxiliary carrier with the
  shift (`GUEEntry_quad_tail`, `GUEEntry_row_tail`, `GUEEntry_col_tail`), the failure set
  `GUEEntry_bad` with `GUEEntry_bad_tail`, and the union bound `GUEEntry_union`.
* Target 12, the pin `GUEEntryMixBA d` (free flow-point families `g n`, `E n`, `m n`) and
  its proof `gueEntryMixBA` (`3 ≤ d`).
* Target 13, compiled nonempty instances at `d = 3` (section `GUEEntryInst` at the end of
  the file).
-/

open private loopFine_pm_formula_vtx sum_vtx_ite from RBM3D.Green.Pins
open private EntryTail_Gres_true from RBM3D.Universality.GUEPhase.EntryTail
open private mixEntry_final_arith from RBM3D.Universality.GUEPhase.EntryTailMain

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section
namespace RBM.BA
open RBM RBM.Gauss RBM.Green RBM.Univ

section FinePart
open Finset Matrix

section Bridge
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The BA entry error `|G_{(a,x),(b,y)}(z_u) - M^{(B)}_{ab} δ_{xy}|` at the matrix `H`
(`z_u = E + (1 - u) m`, `M^{(B)} = (g Ψ^{(B)} - E - m)⁻¹`). -/
def GUEEntry_llErr (d L W : ℕ) [NeZero L] [NeZero W] (g E : ℝ) (m : ℂ) (u : ℝ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) : ℝ :=
  ‖Gres H (ztOf m E u) true i j -
    (if (split d L W i).2 = (split d L W j).2 then
      BAMB d L g (E : ℂ) m (split d L W i).1 (split d L W j).1 else 0)‖

/-- `max_{a,b} |𝓛_{u,(+,-),(a,b)}|` of the matrix `H` at `z_u = E + (1 - u) m`. -/
def GUEEntry_maxLoop (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d L), (0 : Zd d L)), Finset.mem_univ _⟩
    (fun p : Zd d L × Zd d L => ‖loopFine d L W H (ztOf m E u) ![true, false] ![p.1, p.2]‖)

theorem GUEEntry_norm_loop_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian) (z : ℂ) (a b : Zd d L) :
    ‖loopFine d L W H z ![true, false] ![a, b]‖ = GreenCore_loop (Gres (blockMat d L W H) z true) b a := by
  rw [loopFine_pm_formula_vtx H hH z a b, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity))]
  have h1 : ∀ v : Vtx d L W, (∑ w : Vtx d L W, if v.1 = b ∧ w.1 = a then
      ‖Gres (blockMat d L W H) z true v w‖ ^ 2 else 0) =
      if v.1 = b then ∑ w : Vtx d L W, (if w.1 = a then ‖Gres (blockMat d L W H) z true v w‖ ^ 2 else 0) else 0 :=
    fun v => by by_cases hv : v.1 = b <;> simp [hv]
  have hsum : (∑ v : Vtx d L W, ∑ w : Vtx d L W, if v.1 = b ∧ w.1 = a then
      ‖Gres (blockMat d L W H) z true v w‖ ^ 2 else 0) =
      ∑ β : Fin (W ^ d), ∑ α : Fin (W ^ d), ‖Gres (blockMat d L W H) z true (b, β) (a, α)‖ ^ 2 := by
    simp only [h1]
    rw [sum_vtx_ite (fun v => ∑ w : Vtx d L W, (if w.1 = a then ‖Gres (blockMat d L W H) z true v w‖ ^ 2 else 0)) b]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [sum_vtx_ite (fun w => ‖Gres (blockMat d L W H) z true (b, β) w‖ ^ 2) a]
  rw [hsum]
  unfold GreenCore_loop
  rfl

set_option maxHeartbeats 800000 in
-- the transport of the hypotheses from the fine lattice to `Vtx` and back, in one proof
/-- **The deterministic step on the fine lattice** (twin of `mixEntry_det`, `EntryTail.lean:859`): the four large-deviation
inputs for `X` against the minors of `G = (g Ψ + X - z)⁻¹`, `z = E + (1 - u) m`, `u = a + b`, stated on `Idx` (the
form of the tails), give `|(G - M)_{ij}|² ≤ C Φ² (max 𝓛 + W^{-d})` on the a priori event `‖G - M‖_max ≤ δ`. -/
theorem mixEntry_detBA {g Λ κ E a b δ Φ : ℝ} {m : ℂ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hr : BAReal d L g κ E m) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu1 : a + b < 1)
    {X : Matrix (Idx d L W) (Idx d L W) ℂ} (hX : X.IsHermitian)
    (hllErr : ∀ x y, GUEEntry_llErr d L W g E m (a + b) ((g : ℂ) • PsiI d L W + X) x y ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ GUEEntry_dlt d Λ κ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hΦ : 1 ≤ Φ)
    (hΦδ : GUEEntry_cs d Λ κ * Φ * δ ^ 2 ≤ 1)
    (hrow : ∀ i j, i ≠ j → ldeRowLHS X (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) i j ≤
      Φ * ldeRowRHS (Smix d L W 0 a b) (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) i j)
    (hcol : ∀ k j, k ≠ j → ldeColLHS X (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) k j ≤
      Φ * ldeColRHS (Smix d L W 0 a b) (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) k j)
    (hquad : ∀ i, ldeQuadLHS X (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) (Smix d L W 0 a b) 1 i ≤
      Φ * ldeQuadRHS (Smix d L W 0 a b) (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) i)
    (hdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * Smix d L W 0 a b i i) (i j : Idx d L W) :
    GUEEntry_llErr d L W g E m (a + b) ((g : ℂ) • PsiI d L W + X) i j ^ 2 ≤
      GUEEntry_C d Λ κ * Φ ^ 2 * (GUEEntry_maxLoop d L W m E (a + b) ((g : ℂ) • PsiI d L W + X) +
        ((W : ℝ) ^ d)⁻¹) := by
  set e := splitEquiv d L W with he
  set H : Matrix (Idx d L W) (Idx d L W) ℂ := (g : ℂ) • PsiI d L W + X with hHdef
  set z : ℂ := ztOf m E (a + b) with hzdef
  have hmpos : 0 < m.im := lt_of_lt_of_le hκ hr.2
  have hu0 : 0 < 1 - (a + b) := by linarith
  have hzim : 0 < z.im := by
    rw [hzdef, ztOf_im]; unfold etaOf; exact mul_pos hu0 hmpos
  have hPsi : ((g : ℂ) • PsiI d L W).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d L W).eq,
      show star (g : ℂ) = (g : ℂ) from Complex.conj_ofReal _]
  have hHerm : H.IsHermitian := hPsi.add hX
  have hGres : Gres H z true = green H z := EntryTail_Gres_true H z
  set s : ℂ := (E : ℂ) + m with hs
  have hsim : s.im ≠ 0 := by rw [hs]; simpa using hmpos.ne'
  have hHs : IsUnit (((g : ℂ) • PsiI d L W) - s • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) :=
    RBM.isUnit_sub_smul_of_isHermitian hPsi hsim
  set Mf : Matrix (Idx d L W) (Idx d L W) ℂ := Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m with hMf
  have hMfinv : Mf = Ring.inverse (((g : ℂ) • PsiI d L W) - s • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) := rfl
  have bm : ∀ A B : Matrix (Idx d L W) (Idx d L W) ℂ,
      blockMat d L W (A * B) = blockMat d L W A * blockMat d L W B :=
    fun A B => (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm
  have bm1 : blockMat d L W (1 : Matrix (Idx d L W) (Idx d L W) ℂ) = 1 := Matrix.submatrix_one_equiv e.symm
  have bD : ∀ c : ℂ, blockMat d L W (c • PsiI d L W) = c • PsiV d L W := by
    intro c; ext u v; simp [blockMat, PsiI]
  have hHb : blockMat d L W (H - z • 1) = (g : ℂ) • PsiV d L W + blockMat d L W X - z • 1 := by
    rw [hHdef, ← bD (g : ℂ)]
    ext u v
    simp [blockMat, Matrix.one_apply]
  have hMb : blockMat d L W (((g : ℂ) • PsiI d L W) - s • 1) = (g : ℂ) • PsiV d L W - s • 1 := by
    rw [← bD (g : ℂ)]
    ext u v
    simp [blockMat, Matrix.one_apply]
  have hGreenInv : green H z = Ring.inverse (H - z • 1) := by
    unfold green; exact Matrix.nonsing_inv_eq_ringInverse _
  have hUH : IsUnit (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) :=
    RBM.isUnit_sub_smul_of_isHermitian hHerm hzim.ne'
  have hGR : blockMat d L W (green H z) * ((g : ℂ) • PsiV d L W + blockMat d L W X - z • 1) = 1 := by
    rw [← hHb, ← bm, hGreenInv, Ring.inverse_mul_cancel _ hUH, bm1]
  have hRG : ((g : ℂ) • PsiV d L W + blockMat d L W X - z • 1) * blockMat d L W (green H z) = 1 := by
    rw [← hHb, ← bm, hGreenInv, Ring.mul_inverse_cancel _ hUH, bm1]
  have hMR : ((g : ℂ) • PsiV d L W - s • 1) * blockMat d L W Mf = 1 := by
    rw [← hMb, ← bm, hMfinv, Ring.mul_inverse_cancel _ hHs, bm1]
  have hMR' : blockMat d L W Mf * ((g : ℂ) • PsiV d L W - s • 1) = 1 := by
    rw [← hMb, ← bm, hMfinv, Ring.inverse_mul_cancel _ hHs, bm1]
  have hzs : z = s - ((a + b : ℝ) : ℂ) * m := by rw [hzdef, hs, ztOf]; push_cast; ring
  have hMv : ∀ u v : Vtx d L W, blockMat d L W Mf u v =
      if u.2 = v.2 then BAMB d L g (E : ℂ) m u.1 v.1 else 0 := by
    intro u v
    have h := BAMres_fine_apply d L W g (E : ℂ) m (by simpa using hmpos.ne') (e.symm u) (e.symm v)
    have hu' : split d L W (e.symm u) = u := e.apply_symm_apply u
    have hv' : split d L W (e.symm v) = v := e.apply_symm_apply v
    rw [hu', hv'] at h
    exact h
  have hDv : ∀ u l : Vtx d L W, ((g : ℂ) • PsiV d L W) u l =
      if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g : ℂ) else 0 := by
    intro u l
    simp only [PsiV, PsiB, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp_all
  have hHvh : (((g : ℂ) • PsiV d L W) + blockMat d L W X).IsHermitian := by
    have h1 : blockMat d L W H = ((g : ℂ) • PsiV d L W) + blockMat d L W X := by
      rw [hHdef, ← bD (g : ℂ)]; ext u v; simp [blockMat]
    rw [← h1]
    exact hHerm.submatrix _
  have hGg : Gres (blockMat d L W H) z true = (green H z).submatrix e.symm e.symm := by
    unfold Gres blockMat green
    simp only [ite_true]
    have e1 : H.submatrix e.symm e.symm - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
        (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix e.symm e.symm := by
      ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply]
    rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_submatrix_equiv]
  -- the inputs on `Vtx`
  have hSmv : GUEEntry_Smv d L W a b = fun p q => Smix d L W 0 a b (e.symm p) (e.symm q) := by
    funext p q; exact GUEEntry_Smv_eq a b p q
  have hLrow : LDERow (blockMat d L W X) (blockMat d L W (green H z)) (GUEEntry_Smv d L W a b) Φ := by
    intro x y hxy
    rw [hSmv]
    change ldeRowLHS (X.submatrix e.symm e.symm) ((green H z).submatrix e.symm e.symm) x y ≤
      Φ * ldeRowRHS (fun p q => Smix d L W 0 a b (e.symm p) (e.symm q)) ((green H z).submatrix e.symm e.symm) x y
    rw [mixEntry_relabel_ldeRowLHS, mixEntry_relabel_ldeRowRHS e.symm (Smix d L W 0 a b) (green H z) x y]
    exact hrow _ _ (fun h => hxy (e.symm.injective h))
  have hLcol : LDECol (blockMat d L W X) (blockMat d L W (green H z)) (GUEEntry_Smv d L W a b) Φ := by
    intro x y hxy
    rw [hSmv]
    change ldeColLHS (X.submatrix e.symm e.symm) ((green H z).submatrix e.symm e.symm) x y ≤
      Φ * ldeColRHS (fun p q => Smix d L W 0 a b (e.symm p) (e.symm q)) ((green H z).submatrix e.symm e.symm) x y
    rw [mixEntry_relabel_ldeColLHS, mixEntry_relabel_ldeColRHS e.symm (Smix d L W 0 a b) (green H z) x y]
    exact hcol _ _ (fun h => hxy (e.symm.injective h))
  have hLquad : LDEQuad (blockMat d L W X) (blockMat d L W (green H z)) (GUEEntry_Smv d L W a b) 1 Φ := by
    intro x
    rw [hSmv]
    change ldeQuadLHS (X.submatrix e.symm e.symm) ((green H z).submatrix e.symm e.symm)
      (fun p q => Smix d L W 0 a b (e.symm p) (e.symm q)) 1 x ≤
      Φ * ldeQuadRHS (fun p q => Smix d L W 0 a b (e.symm p) (e.symm q)) ((green H z).submatrix e.symm e.symm) x
    rw [mixEntry_relabel_ldeQuadLHS, mixEntry_relabel_ldeQuadRHS e.symm (Smix d L W 0 a b) (green H z) x]
    exact hquad _
  have hLdiag : ∀ x : Vtx d L W, ‖blockMat d L W X x x‖ ^ 2 ≤ Φ * GUEEntry_Smv d L W a b x x := fun x => by
    rw [GUEEntry_Smv_eq]; exact hdiag _
  have hΩ : ∀ u v : Vtx d L W, ‖blockMat d L W (green H z) u v - blockMat d L W Mf u v‖ ≤ δ := by
    intro u v
    have h := hllErr (e.symm u) (e.symm v)
    unfold GUEEntry_llErr at h
    rw [hGres] at h
    have hu' : split d L W (e.symm u) = u := e.apply_symm_apply u
    have hv' : split d L W (e.symm v) = v := e.apply_symm_apply v
    rw [hu', hv'] at h
    have h2 : blockMat d L W Mf u v = if u.2 = v.2 then BAMB d L g (E : ℂ) m u.1 v.1 else 0 := hMv u v
    rw [h2]
    exact h
  have hLm : ∀ a' b' : Zd d L, GreenCore_loop (blockMat d L W (green H z)) a' b' ≤
      GUEEntry_maxLoop d L W m E (a + b) H := by
    intro a' b'
    have h1 := GUEEntry_norm_loop_eq H hHerm z b' a'
    have h2 : blockMat d L W (green H z) = Gres (blockMat d L W H) z true := by rw [hGg]; rfl
    rw [h2, ← h1]
    exact Finset.le_sup' (fun p : Zd d L × Zd d L => ‖loopFine d L W H (ztOf m E (a + b)) ![true, false] ![p.1, p.2]‖)
      (Finset.mem_univ (b', a'))
  have key := mix_detBA hd hL hg hgΛ hκ hr ha hb hu1 hGR hRG hMR hMR' hzs
    (fun u v => by rw [← hMv u v]) (fun u l => by rw [hDv]) (by convert hHvh using 1) hzim hδ0 hδ hwd hΩ hΦ hΦδ hLrow hLcol hLquad hLdiag hLm
    (e i) (e j)
  have hent : GUEEntry_llErr d L W g E m (a + b) H i j =
      ‖blockMat d L W (green H z) (e i) (e j) - blockMat d L W Mf (e i) (e j)‖ := by
    unfold GUEEntry_llErr
    rw [hMv (e i) (e j), hGres]
    simp only [blockMat, Matrix.submatrix_apply, he, Equiv.symm_apply_apply]
    rfl
  rw [hent]
  exact key

end Bridge

end FinePart

section ProbPart
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

section Tails
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **Quadratic LDE (4.7) for `G = (A + X - z)⁻¹`** (twin of `mixEntry_quad_tail`, `EntryTail.lean:492`, with the
deterministic Hermitian shift `A`; `gaussLaw_quad_tail` is already shift-general). -/
theorem GUEEntry_quad_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ}
    (hv : TagFree d L W v) (hS : MixProfOK v S) {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gaussLaw d L W v {s | lam * ldeQuadRHS S (green (A + Xmat d L W s) z) i <
        ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z) S 1 i}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have h := gaussLaw_quad_tail hv hA hz i hlam q
  have hset : {s : Ω d L W | lam * ldeQuadRHS S (green (A + Xmat d L W s) z) i <
        ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z) S 1 i}
      = {s : Ω d L W | lam * quadVqS d L W v A z i s < ‖quadQS d L W v A z i s‖ ^ 2} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    have hH := hA.add (Xmat_isHermitian d L W s)
    have hVq : ldeQuadRHS S (green (A + Xmat d L W s) z) i = quadVqS d L W v A z i s := by
      unfold ldeQuadRHS quadVqS
      rw [RowChaos.sum_erase_eq (i := i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RowChaos.sum_erase_eq (i := i)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mixEntry_minor_eq hH hz i k l, ← hS.off i k.1 (Ne.symm k.2),
        hS.symm l.1 i, ← hS.off i l.1 (Ne.symm l.2)]
    have hQ : ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z) S 1 i =
        ‖quadQS d L W v A z i s‖ ^ 2 := by
      unfold ldeQuadLHS quadQS
      congr 2
      rw [RowChaos.sum_erase_eq (i := i)]
      · congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [RowChaos.sum_erase_eq (i := i)]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← mixEntry_minor_eq hH hz i k l]
        · rw [RowChaos.sum_erase_eq (i := i), Complex.ofReal_one, one_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← mixEntry_minor_eq hH hz i k k, ← hS.off i k.1 (Ne.symm k.2)]
    rw [hVq, hQ]
  rw [hset]
  exact h

/-- `s ↦ G^{(i)}_{kl}(A + X(s))` is continuous for `k, l ≠ i` (`continuous_green_minorS`). -/
theorem GUEEntry_cont_minor {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i k l : Idx d L W) (hk : k ≠ i) (hl : l ≠ i) :
    Continuous fun s : Ω d L W => greenMinor (green (A + Xmat d L W s) z) i k l := by
  have := continuous_green_minorS (d := d) (L := L) (W := W) hA hz i ⟨k, hk⟩ ⟨l, hl⟩
  convert this using 2 with s
  exact (mixEntry_minor_eq (hA.add (Xmat_isHermitian d L W s)) hz i ⟨k, hk⟩ ⟨l, hl⟩).symm

theorem GUEEntry_meas_row (S : Idx d L W → Idx d L W → ℝ) {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) {i j : Idx d L W} (hij : i ≠ j) (Λ : ℝ) :
    MeasurableSet {s : Ω d L W | Λ * ldeRowRHS S (green (A + Xmat d L W s) z) i j <
      ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) i j} := by
  refine measurableSet_lt (Continuous.measurable ?_) (Continuous.measurable ?_)
  · unfold ldeRowRHS
    exact continuous_const.mul (continuous_finsetSum _ fun k hk => continuous_const.mul
      ((GUEEntry_cont_minor hA hz i k j (Finset.ne_of_mem_erase hk) (Ne.symm hij)).norm.pow 2))
  · unfold ldeRowLHS
    exact (continuous_finsetSum _ fun k hk => (continuous_Xmat_apply i k).mul
      (GUEEntry_cont_minor hA hz i k j (Finset.ne_of_mem_erase hk) (Ne.symm hij))).norm.pow 2

theorem GUEEntry_meas_col (S : Idx d L W → Idx d L W → ℝ) {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) {k j : Idx d L W} (hkj : k ≠ j) (Λ : ℝ) :
    MeasurableSet {s : Ω d L W | Λ * ldeColRHS S (green (A + Xmat d L W s) z) k j <
      ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) k j} := by
  refine measurableSet_lt (Continuous.measurable ?_) (Continuous.measurable ?_)
  · unfold ldeColRHS
    exact continuous_const.mul (continuous_finsetSum _ fun l hl => ((GUEEntry_cont_minor hA hz j k l hkj
      (Finset.ne_of_mem_erase hl)).norm.pow 2).mul continuous_const)
  · unfold ldeColLHS
    exact (continuous_finsetSum _ fun l hl => (GUEEntry_cont_minor hA hz j k l hkj
      (Finset.ne_of_mem_erase hl)).mul (continuous_Xmat_apply l j)).norm.pow 2

/-- The minor resolvent of the shifted auxiliary matrix is `greenMinor` of the resolvent. -/
theorem GUEEntry_auxMinorRes_eq (v : CoordF d L W → ℝ≥0) {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d)) (k l : {a : Idx d L W // a ≠ i}) :
    auxMinorRes d L W v A z i ω k l = greenMinor (green (A + auxHG d L W v ω) z) i k.1 l.1 := by
  rw [← mixEntry_minor_eq (hA.add (auxHG_isHermitian d L W v ω)) hz i k l]
  rfl

/-- **Row LDE (4.8) for `G = (A + X - z)⁻¹`** (twin of `mixEntry_row_tail`, `EntryTail.lean:548`). -/
theorem GUEEntry_row_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ}
    (hv : TagFree d L W v) (hS : MixProfOK v S) {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) {i j : Idx d L W} (hij : i ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    gaussLaw d L W v {s | Λ * ldeRowRHS S (green (A + Xmat d L W s) z) i j <
        ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) i j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  obtain ⟨j', rfl⟩ : ∃ j' : {a : Idx d L W // a ≠ i}, j'.1 = j := ⟨⟨j, Ne.symm hij⟩, rfl⟩
  set c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ i} → ℂ :=
    fun ω k => auxMinorRes d L W v A z i ω k j' with hc_def
  have hc : ∀ k, Continuous fun ω => c ω k := fun k => continuous_auxMinorRes d L W v hA hz i k j'
  have hCb : ∀ ω k, ‖c ω k‖ ≤ |z.im|⁻¹ := fun ω k => norm_auxMinorRes_le d L W v hA hz i ω k j'
  have hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W i, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h
    funext k
    simp only [c]
    rw [auxMinorRes_congr d L W v A z i h]
  have hc0 : ∀ ω k, c ω k = greenMinor (green (A + auxHG d L W v ω) z) i k.1 j'.1 :=
    fun ω k => GUEEntry_auxMinorRes_eq v hA hz i ω k j'
  have hY : ∀ ω, ldeRowLHS (Xmat d L W (auxT d L W v ω)) (green (A + Xmat d L W (auxT d L W v ω)) z) i j'.1
      = ‖∑ k : {a : Idx d L W // a ≠ i}, auxHG d L W v ω i k.1 * c ω k‖ ^ 2 := by
    intro ω
    change ldeRowLHS (auxHG d L W v ω) (green (A + auxHG d L W v ω) z) i j'.1 = _
    unfold ldeRowLHS
    rw [RowChaos.sum_erase_eq (i := i)]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc0]
  have hR : ∀ ω, ldeRowRHS S (green (A + Xmat d L W (auxT d L W v ω)) z) i j'.1
      = ∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    change ldeRowRHS S (green (A + auxHG d L W v ω) z) i j'.1 = _
    unfold ldeRowRHS
    rw [RowChaos.sum_erase_eq (i := i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hS.off i k.1 (Ne.symm k.2), hc0]
  have hR0 : ∀ ω, 0 ≤ ∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by unfold sigRow; positivity) (sq_nonneg _)
  have h := aux_lin_tail (auxLinChaos d L W v i c hc _ hCb hcf)
    (fun ω => ‖∑ k : {a : Idx d L W // a ≠ i}, auxHG d L W v ω i k.1 * c ω k‖ ^ 2)
    (fun ω => ∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2) hR0
    (fun ω => auxLin_chaos hv i c hc _ hCb hcf ω)
    (fun ω => auxLin_Vq i c hc _ hCb hcf ω) hΛ q
  have hmap : gaussLaw d L W v = (Sizes.seqP (auxSizes d)).map (auxT d L W v) :=
    (auxT_law d L W v).symm
  have hAm := GUEEntry_meas_row S hA hz (Ne.symm j'.2) Λ
  rw [hmap, Measure.map_apply (auxT_measurable d L W v) hAm]
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hY ω, hR ω]

/-- **Column LDE (4.8) for `G = (A + X - z)⁻¹`** (twin of `mixEntry_col_tail`, `EntryTail.lean:608`). -/
theorem GUEEntry_col_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ}
    (hv : TagFree d L W v) (hS : MixProfOK v S) {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) {k j : Idx d L W} (hkj : k ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    gaussLaw d L W v {s | Λ * ldeColRHS S (green (A + Xmat d L W s) z) k j <
        ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) k j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k' : {a : Idx d L W // a ≠ j}, k'.1 = k := ⟨⟨k, hkj⟩, rfl⟩
  set c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ j} → ℂ :=
    fun ω l => (starRingEnd ℂ) (auxMinorRes d L W v A z j ω k' l) with hc_def
  have hc : ∀ l, Continuous fun ω => c ω l := fun l =>
    Complex.continuous_conj.comp (continuous_auxMinorRes d L W v hA hz j k' l)
  have hCb : ∀ ω l, ‖c ω l‖ ≤ |z.im|⁻¹ := fun ω l => by
    simp only [c, Complex.norm_conj]
    exact norm_auxMinorRes_le d L W v hA hz j ω k' l
  have hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W j, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h
    funext l
    simp only [c]
    rw [auxMinorRes_congr d L W v A z j h]
  have hc0 : ∀ ω l, c ω l = (starRingEnd ℂ) (greenMinor (green (A + auxHG d L W v ω) z) j k'.1 l.1) :=
    fun ω l => congrArg (starRingEnd ℂ) (GUEEntry_auxMinorRes_eq v hA hz j ω k' l)
  have hY : ∀ ω, ldeColLHS (Xmat d L W (auxT d L W v ω)) (green (A + Xmat d L W (auxT d L W v ω)) z) k'.1 j
      = ‖∑ l : {a : Idx d L W // a ≠ j}, auxHG d L W v ω j l.1 * c ω l‖ ^ 2 := by
    intro ω
    change ldeColLHS (auxHG d L W v ω) (green (A + auxHG d L W v ω) z) k'.1 j = _
    unfold ldeColLHS
    rw [RowChaos.sum_erase_eq (i := j)]
    have e : ∑ l : {a : Idx d L W // a ≠ j}, greenMinor (green (A + auxHG d L W v ω) z) j k'.1 l.1 *
          auxHG d L W v ω l.1 j
        = (starRingEnd ℂ) (∑ l : {a : Idx d L W // a ≠ j}, auxHG d L W v ω j l.1 * c ω l) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hH : (starRingEnd ℂ) (auxHG d L W v ω j l.1) = auxHG d L W v ω l.1 j :=
        (auxHG_isHermitian d L W v ω).apply l.1 j
      rw [hc0, map_mul, Complex.conj_conj, hH]
      ring
    rw [e, Complex.norm_conj]
  have hR : ∀ ω, ldeColRHS S (green (A + Xmat d L W (auxT d L W v ω)) z) k'.1 j
      = ∑ l : {a : Idx d L W // a ≠ j}, sigRow d L W v j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    change ldeColRHS S (green (A + auxHG d L W v ω) z) k'.1 j = _
    unfold ldeColRHS
    rw [RowChaos.sum_erase_eq (i := j)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hc' : ‖c ω l‖ = ‖greenMinor (green (A + auxHG d L W v ω) z) j k'.1 l.1‖ := by
      rw [hc0, Complex.norm_conj]
    rw [hc', hS.symm l.1 j, hS.off j l.1 (Ne.symm l.2)]
    ring
  have hR0 : ∀ ω, 0 ≤ ∑ l : {a : Idx d L W // a ≠ j}, sigRow d L W v j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    exact Finset.sum_nonneg fun l _ => mul_nonneg (by unfold sigRow; positivity) (sq_nonneg _)
  have h := aux_lin_tail (auxLinChaos d L W v j c hc _ hCb hcf)
    (fun ω => ‖∑ l : {a : Idx d L W // a ≠ j}, auxHG d L W v ω j l.1 * c ω l‖ ^ 2)
    (fun ω => ∑ l : {a : Idx d L W // a ≠ j}, sigRow d L W v j l.1 * ‖c ω l‖ ^ 2) hR0
    (fun ω => auxLin_chaos hv j c hc _ hCb hcf ω)
    (fun ω => auxLin_Vq j c hc _ hCb hcf ω) hΛ q
  have hAm := GUEEntry_meas_col S hA hz hkj Λ
  have hmap : gaussLaw d L W v = (Sizes.seqP (auxSizes d)).map (auxT d L W v) :=
    (auxT_law d L W v).symm
  rw [hmap, Measure.map_apply (auxT_measurable d L W v) hAm]
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hY ω, hR ω]

end Tails

section Mix2
variable {d : ℕ}

/-- **The BA mixture matrix** `g Ψ + √a X_block + √b X_GUE` on the carrier `ouP (UNModel.band (sz.withLam 0)) n`
(`= ouP (UNModelC.ba sz).toUNModel n`, `UNPins.lean:467`): the band mixture of `sz.withLam 0` plus the hopping. -/
def mixMatBA (sz : Sizes d) (n : ℕ) (g a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (g : ℂ) • PsiI d (sz.L n) (sz.W n) +
    @id (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (mixMat (sz.withLam 0) n a b ω)

theorem GUEEntry_mixMatBA_eq_Xmat (sz : Sizes d) (n : ℕ) (g a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    mixMatBA sz n g a b ω = (g : ℂ) • PsiI d (sz.L n) (sz.W n) +
      Xmat d (sz.L n) (sz.W n) (mixSample (sz.withLam 0) n a b ω) := by
  unfold mixMatBA
  exact congrArg (fun M => (g : ℂ) • PsiI d (sz.L n) (sz.W n) + M) (mixMat_eq_Xmat_mixSample (sz.withLam 0) n a b ω)

/-- The centred OU marginal of the block Anderson model is the BA mixture at `(a, b) = (e^{-t}, 1 - e^{-t})`,
`g = λ_n`. -/
theorem GUEEntry_ouMatC_ba_eq_mixMatBA (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC (UNModelC.ba sz) n t ω = mixMatBA sz n (sz.lam n) (Real.exp (-t)) (1 - Real.exp (-t)) ω := by
  have h := (ouMatC_ba_eq_band_add sz n t ω).trans (ouMat_eq_mixMat (sz.withLam 0) n t ω)
  unfold mixMatBA
  exact sub_eq_iff_eq_add'.1 h

end Mix2

section Bad
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **The union of the four large-deviation failure events** at the shift `A`, profile `S`, spectral parameter
`z` and factor `Λ` (twin of `mixBad`, `EntryTailMain.lean:120`, one union over the pairs). -/
def GUEEntry_bad (A : Matrix (Idx d L W) (Idx d L W) ℂ) (S : Idx d L W → Idx d L W → ℝ) (z : ℂ) (Λ : ℝ) :
    Set (Ω d L W) :=
  ⋃ p : Idx d L W × Idx d L W,
    {s | (p.1 ≠ p.2 ∧ Λ * ldeRowRHS S (green (A + Xmat d L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2) ∨
      (p.1 ≠ p.2 ∧ Λ * ldeColRHS S (green (A + Xmat d L W s) z) p.1 p.2 <
        ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2) ∨
      Λ * ldeQuadRHS S (green (A + Xmat d L W s) z) p.1 <
        ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z) S 1 p.1 ∨
      Λ * S p.1 p.1 < ‖Xmat d L W s p.1 p.1‖ ^ 2}

theorem GUEEntry_bad_tail (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {Λ : ℝ} (hΛ : 2 ≤ Λ) (q : ℕ) :
    gaussLaw d L W (mixVar d L W g a b) (GUEEntry_bad A (Smix d L W g a b) z Λ) ≤
      ENNReal.ofReal (4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * (mixCq q / Λ ^ (q + 1))) := by
  have hv := mixVar_tagFree d L W g a b
  have hS := mixProfOK (d := d) (L := L) (W := W) g ha hb
  have hΛ0 : 0 < Λ := by linarith
  have hΛ1 : 1 < Λ := by linarith
  set ε : ℝ := mixCq q / Λ ^ (q + 1) with hε
  have hε0 : 0 ≤ ε := by have := mixCq_pos q; positivity
  set Nn : ℕ := (W * L) ^ d with hNn
  have hcardI : Fintype.card (Idx d L W) = Nn := RBM.Gauss.card_Idx d L W
  have hcardP : Fintype.card (Idx d L W × Idx d L W) = Nn * Nn := by rw [Fintype.card_prod, hcardI]
  have hp : ∀ p : Idx d L W × Idx d L W, gaussLaw d L W (mixVar d L W g a b)
      {s : Ω d L W | (p.1 ≠ p.2 ∧ Λ * ldeRowRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2) ∨
      (p.1 ≠ p.2 ∧ Λ * ldeColRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
        ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2) ∨
      Λ * ldeQuadRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 <
        ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z) (Smix d L W g a b) 1 p.1 ∨
      Λ * Smix d L W g a b p.1 p.1 < ‖Xmat d L W s p.1 p.1‖ ^ 2} ≤ ENNReal.ofReal (4 * ε) := by
    intro p
    have hr : gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W | p.1 ≠ p.2 ∧
        Λ * ldeRowRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} ≤ ENNReal.ofReal ε := by
      by_cases hpp : p.1 = p.2
      · have : {s : Ω d L W | p.1 ≠ p.2 ∧ Λ * ldeRowRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} = ∅ := by ext s; simp [hpp]
        rw [this, measure_empty]; exact zero_le
      · have : {s : Ω d L W | p.1 ≠ p.2 ∧ Λ * ldeRowRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} =
          {s | Λ * ldeRowRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
            ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} := by ext s; simp [hpp]
        rw [this]
        exact (GUEEntry_row_tail hv hS hA hz hpp hΛ1 q).trans (ENNReal.ofReal_le_ofReal (mixEntry_tail_row_le hΛ q))
    have hc : gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W | p.1 ≠ p.2 ∧
        Λ * ldeColRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} ≤ ENNReal.ofReal ε := by
      by_cases hpp : p.1 = p.2
      · have : {s : Ω d L W | p.1 ≠ p.2 ∧ Λ * ldeColRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} = ∅ := by ext s; simp [hpp]
        rw [this, measure_empty]; exact zero_le
      · have : {s : Ω d L W | p.1 ≠ p.2 ∧ Λ * ldeColRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} =
          {s | Λ * ldeColRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
            ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} := by ext s; simp [hpp]
        rw [this]
        exact (GUEEntry_col_tail hv hS hA hz hpp hΛ1 q).trans (ENNReal.ofReal_le_ofReal (mixEntry_tail_row_le hΛ q))
    have hq : gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W | Λ * ldeQuadRHS (Smix d L W g a b)
        (green (A + Xmat d L W s) z) p.1 < ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z)
          (Smix d L W g a b) 1 p.1} ≤ ENNReal.ofReal ε :=
      (GUEEntry_quad_tail hv hS hA hz p.1 hΛ0 q).trans (ENNReal.ofReal_le_ofReal (mixEntry_tail_quad_le hΛ0 q))
    have hd' : gaussLaw d L W (mixVar d L W g a b) {s : Ω d L W | Λ * Smix d L W g a b p.1 p.1 <
        ‖Xmat d L W s p.1 p.1‖ ^ 2} ≤ ENNReal.ofReal ε :=
      (mixEntry_diag_tail hS p.1 (mixEntry_Smix_diag_pos d L W g ha hb hu p.1) hΛ0).trans
        (ENNReal.ofReal_le_ofReal (by have := mixEntry_tail_diag_le hΛ0 q; rw [hε]; exact this))
    have hsub : {s : Ω d L W | (p.1 ≠ p.2 ∧ Λ * ldeRowRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2) ∨
      (p.1 ≠ p.2 ∧ Λ * ldeColRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
        ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2) ∨
      Λ * ldeQuadRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 <
        ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z) (Smix d L W g a b) 1 p.1 ∨
      Λ * Smix d L W g a b p.1 p.1 < ‖Xmat d L W s p.1 p.1‖ ^ 2} ⊆
      ({s : Ω d L W | p.1 ≠ p.2 ∧ Λ * ldeRowRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeRowLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2} ∪
        {s : Ω d L W | p.1 ≠ p.2 ∧ Λ * ldeColRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 p.2 <
          ldeColLHS (Xmat d L W s) (green (A + Xmat d L W s) z) p.1 p.2}) ∪
      {s : Ω d L W | Λ * ldeQuadRHS (Smix d L W g a b) (green (A + Xmat d L W s) z) p.1 <
        ldeQuadLHS (Xmat d L W s) (green (A + Xmat d L W s) z) (Smix d L W g a b) 1 p.1} ∪
      {s : Ω d L W | Λ * Smix d L W g a b p.1 p.1 < ‖Xmat d L W s p.1 p.1‖ ^ 2} := by
      intro s hs
      rcases hs with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    have h3 := add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hr hc)) hq)) hd'
    refine h3.trans (le_of_eq ?_)
    have h4 : ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε = ENNReal.ofReal (4 * ε) := by
      rw [← ENNReal.ofReal_add hε0 hε0, ← ENNReal.ofReal_add (by positivity) hε0,
        ← ENNReal.ofReal_add (by positivity) hε0]
      congr 1; ring
    exact h4
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun p _ => hp p).trans ?_
  rw [Finset.sum_const, Finset.card_univ, hcardP, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  push_cast
  ring

end Bad

theorem GUEEntry_C_nonneg (d : ℕ) {Λ κ : ℝ} (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) : 0 ≤ GUEEntry_C d Λ κ := by
  have hc₀ := BAct_rate_pos d Λ κ hd hΛ hκ
  unfold GUEEntry_C GUEEntry_CAb GUEEntry_CXb GUEEntry_CRb GUEEntry_CA GUEEntry_CX GUEEntry_CR GUEEntry_Kbd
    GUEEntry_Kth GUEEntry_rho GUEEntry_Sc GUEEntry_XiC expC
  positivity

section Event
variable {d : ℕ}

theorem GUEEntry_maxLoop_nonneg (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) : 0 ≤ GUEEntry_maxLoop d L W m E u H :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : Zd d L × Zd d L =>
    ‖loopFine d L W H (ztOf m E u) ![true, false] ![p.1, p.2]‖) (Finset.mem_univ ((0 : Zd d L), (0 : Zd d L))))

/-- **The event of the pin (one mixture, one pair) is contained in the failure events** (twin of
`mixEntry_event_subset`, `EntryTailMain.lean:292`). -/
theorem GUEEntry_event_subset (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {Λ κ δ Φ T g E a b : ℝ} {m : ℂ}
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d (sz.L n) g κ E m) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu1 : a + b < 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ GUEEntry_dlt d Λ κ) (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hΦ : 1 ≤ Φ) (hΦδ : GUEEntry_cs d Λ κ * Φ * δ ^ 2 ≤ 1) (hT : GUEEntry_C d Λ κ * Φ ^ 2 ≤ T) :
    {ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) | ∃ i j : Idx d (sz.L n) (sz.W n),
      T * (GUEEntry_maxLoop d (sz.L n) (sz.W n) m E (a + b) (mixMatBA sz n g a b ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) g E m (a + b) (mixMatBA sz n g a b ω) x y ≤ δ
          then GUEEntry_llErr d (sz.L n) (sz.W n) g E m (a + b) (mixMatBA sz n g a b ω) i j ^ 2 else 0)}
      ⊆ mixSample (sz.withLam 0) n a b ⁻¹'
        GUEEntry_bad ((g : ℂ) • PsiI d (sz.L n) (sz.W n)) (Smix d (sz.L n) (sz.W n) 0 a b) (ztOf m E (a + b)) Φ := by
  rintro ω ⟨i, j, hij⟩
  by_contra hnot
  rw [GUEEntry_mixMatBA_eq_Xmat] at hij
  set s := mixSample (sz.withLam 0) n a b ω with hs
  have hnot' : s ∉ GUEEntry_bad ((g : ℂ) • PsiI d (sz.L n) (sz.W n)) (Smix d (sz.L n) (sz.W n) 0 a b)
      (ztOf m E (a + b)) Φ := hnot
  have hΛ : 0 < Λ := lt_of_lt_of_le hg hgΛ
  have hCn := GUEEntry_C_nonneg d (by omega) hΛ hκ
  have hT0 : 0 ≤ T := le_trans (mul_nonneg hCn (sq_nonneg Φ)) hT
  have hmL := GUEEntry_maxLoop_nonneg d (sz.L n) (sz.W n) m E (a + b)
    ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s)
  have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  by_cases hall : ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) g E m (a + b)
      ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) x y ≤ δ
  · simp only [hall, implies_true, ↓reduceIte] at hij
    have hrow : ∀ i j, i ≠ j → ldeRowLHS (Xmat d (sz.L n) (sz.W n) s)
        (green ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) (ztOf m E (a + b))) i j ≤
        Φ * ldeRowRHS (Smix d (sz.L n) (sz.W n) 0 a b)
          (green ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) (ztOf m E (a + b))) i j := by
      intro i j hij'
      by_contra h
      exact hnot' (Set.mem_iUnion.2 ⟨(i, j), Or.inl ⟨hij', not_le.1 h⟩⟩)
    have hcol : ∀ k j, k ≠ j → ldeColLHS (Xmat d (sz.L n) (sz.W n) s)
        (green ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) (ztOf m E (a + b))) k j ≤
        Φ * ldeColRHS (Smix d (sz.L n) (sz.W n) 0 a b)
          (green ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) (ztOf m E (a + b))) k j := by
      intro k j hkj
      by_contra h
      exact hnot' (Set.mem_iUnion.2 ⟨(k, j), Or.inr (Or.inl ⟨hkj, not_le.1 h⟩)⟩)
    have hquad : ∀ i, ldeQuadLHS (Xmat d (sz.L n) (sz.W n) s)
        (green ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) (ztOf m E (a + b)))
        (Smix d (sz.L n) (sz.W n) 0 a b) 1 i ≤
        Φ * ldeQuadRHS (Smix d (sz.L n) (sz.W n) 0 a b)
          (green ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) (ztOf m E (a + b))) i := by
      intro i
      by_contra h
      exact hnot' (Set.mem_iUnion.2 ⟨(i, i), Or.inr (Or.inr (Or.inl (not_le.1 h)))⟩)
    have hdiag : ∀ i, ‖Xmat d (sz.L n) (sz.W n) s i i‖ ^ 2 ≤ Φ * Smix d (sz.L n) (sz.W n) 0 a b i i := by
      intro i
      by_contra h
      exact hnot' (Set.mem_iUnion.2 ⟨(i, i), Or.inr (Or.inr (Or.inr (not_le.1 h)))⟩)
    have hdet := mixEntry_detBA hd (sz.three_le_L n) hg hgΛ hκ hr ha hb hu1 (Xmat_isHermitian d (sz.L n) (sz.W n) s)
      hall hδ0 hδ hwd hΦ hΦδ hrow hcol hquad hdiag i j
    have h1 : GUEEntry_C d Λ κ * Φ ^ 2 * (GUEEntry_maxLoop d (sz.L n) (sz.W n) m E (a + b)
        ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ≤
        T * (GUEEntry_maxLoop d (sz.L n) (sz.W n) m E (a + b)
        ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
      mul_le_mul_of_nonneg_right hT (add_nonneg hmL hW0)
    linarith
  · simp only [hall, ↓reduceIte] at hij
    have : 0 ≤ T * (GUEEntry_maxLoop d (sz.L n) (sz.W n) m E (a + b)
        ((g : ℂ) • PsiI d (sz.L n) (sz.W n) + Xmat d (sz.L n) (sz.W n) s) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
      mul_nonneg hT0 (add_nonneg hmL hW0)
    linarith

/-- **The union over the grid `k ≤ K` at one size** (twin of `mixEntry_union`, `EntryTailMain.lean:369`): the event of the
pin has `ouP`-probability at most `(K + 1) · 4 N² · C_q / Φ^{q+1}`, `N = size n = (W L)^d`. -/
private theorem GUEEntry_union (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {Λ κ δ Φ T g E : ℝ} {m : ℂ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hr : BAReal d (sz.L n) g κ E m) {K : ℕ} {a b : Fin (K + 1) → ℝ}
    (hab : ∀ k, 0 ≤ a k ∧ 0 ≤ b k ∧ 0 < a k + b k ∧ a k + b k < 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ GUEEntry_dlt d Λ κ)
    (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hΦ2 : 2 ≤ Φ) (hΦδ : GUEEntry_cs d Λ κ * Φ * δ ^ 2 ≤ 1)
    (hT : GUEEntry_C d Λ κ * Φ ^ 2 ≤ T) (q : ℕ) :
    ouP (UNModel.band (sz.withLam 0)) n {ω | ∃ (k : Fin (K + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      T * (GUEEntry_maxLoop d (sz.L n) (sz.W n) m E (a k + b k) (mixMatBA sz n g (a k) (b k) ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) g E m (a k + b k) (mixMatBA sz n g (a k) (b k) ω) x y ≤ δ
          then GUEEntry_llErr d (sz.L n) (sz.W n) g E m (a k + b k) (mixMatBA sz n g (a k) (b k) ω) i j ^ 2
          else 0)}
      ≤ ENNReal.ofReal (((K : ℝ) + 1) * (4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1)))) := by
  have hΦ1 : 1 ≤ Φ := by linarith
  have hmpos : 0 < m.im := lt_of_lt_of_le hκ hr.2
  have hPsi : ((g : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq, show star (g : ℂ) = (g : ℂ) from Complex.conj_ofReal _]
  have hsub : {ω | ∃ (k : Fin (K + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      T * (GUEEntry_maxLoop d (sz.L n) (sz.W n) m E (a k + b k) (mixMatBA sz n g (a k) (b k) ω) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) g E m (a k + b k) (mixMatBA sz n g (a k) (b k) ω) x y ≤ δ
          then GUEEntry_llErr d (sz.L n) (sz.W n) g E m (a k + b k) (mixMatBA sz n g (a k) (b k) ω) i j ^ 2
          else 0)}
      ⊆ ⋃ k : Fin (K + 1), mixSample (sz.withLam 0) n (a k) (b k) ⁻¹'
          GUEEntry_bad ((g : ℂ) • PsiI d (sz.L n) (sz.W n)) (Smix d (sz.L n) (sz.W n) 0 (a k) (b k))
            (ztOf m E (a k + b k)) Φ := by
    rintro ω ⟨k, i, j, hω⟩
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    obtain ⟨ha, hb, hu, hu1⟩ := hab k
    exact GUEEntry_event_subset hd sz n hg hgΛ hκ hr ha hb hu1 hδ0 hδ hwd hΦ1 hΦδ hT ⟨i, j, hω⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hk : ∀ k : Fin (K + 1), ouP (UNModel.band (sz.withLam 0)) n (mixSample (sz.withLam 0) n (a k) (b k) ⁻¹'
      GUEEntry_bad ((g : ℂ) • PsiI d (sz.L n) (sz.W n)) (Smix d (sz.L n) (sz.W n) 0 (a k) (b k))
        (ztOf m E (a k + b k)) Φ) ≤
      ENNReal.ofReal (4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1))) := by
    intro k
    obtain ⟨ha, hb, hu, hu1⟩ := hab k
    have hz : (ztOf m E (a k + b k)).im ≠ 0 := by
      rw [ztOf_im]; unfold etaOf; exact (mul_pos (by linarith) hmpos).ne'
    calc _ ≤ ((ouP (UNModel.band (sz.withLam 0)) n).map (mixSample (sz.withLam 0) n (a k) (b k)))
          (GUEEntry_bad ((g : ℂ) • PsiI d (sz.L n) (sz.W n)) (Smix d (sz.L n) (sz.W n) 0 (a k) (b k))
            (ztOf m E (a k + b k)) Φ) :=
          Measure.le_map_apply (measurable_mixSample (sz.withLam 0) n (a k) (b k)).aemeasurable _
      _ = gaussLaw d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) 0 (a k) (b k))
          (GUEEntry_bad ((g : ℂ) • PsiI d (sz.L n) (sz.W n)) (Smix d (sz.L n) (sz.W n) 0 (a k) (b k))
            (ztOf m E (a k + b k)) Φ) := by rw [mixSample_law (sz.withLam 0) n ha hb]; rfl
      _ ≤ _ := GUEEntry_bad_tail 0 ha hb hu hPsi hz hΦ2 q
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCq q / Φ ^ (q + 1)) := by
    have := mixCq_pos q
    have : 0 < Φ := by linarith
    positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  push_cast
  ring

end Event

/-- **Pin `GUEEntryMixBA d`** (BA twin of `GUEEntryMix d`, `EntryTail.lean:94`): Lemma 4.1 (4.2)+(4.3) of [YY_25] at the
block Anderson mixture `g_n Ψ + √a X_block + √b X_GUE` (profile `S_u = a S^{(B)}(0) + b N⁻¹`, `u = a + b < 1`, free
real-axis flow data `(g_n, E_n, m_n)` with `0 < g_n ≤ 𝔡⁻¹`, `BAReal`), in the one-time-law form on
`ouP (UNModel.band (sz.withLam 0)) n = ouP (UNModelC.ba sz).toUNModel n`: on the a priori event
`‖G - M‖_max ≤ δ_n`, `|G_ij - M_ij|² ≺ max_{a,b} |𝓛_{(+,-),(a,b)}| + W^{-d}`, `M = M^{(B)} ⊗ I`, at the spectral
parameter `z_u = E_n + (1 - u) m_n`.  No `∃ C`; the family premises are guarded by `BAReal` at `0 < κ`. -/
def GUEEntryMixBA (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ (g E : ℕ → ℝ) (m : ℕ → ℂ), (∀ n, 0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal d (sz.L n) (g n) κ (E n) (m n)) →
  ∀ n0 : ℕ, ∀ K : ℕ → ℕ, (∀ n, K n ≤ (sz.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ,
  (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) →
  ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) →
  (∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) →
  ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
    ouP (UNModel.band (sz.withLam 0)) n
      {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
        ((sz.size n : ℕ) : ℝ) ^ τ *
            (GUEEntry_maxLoop d (sz.L n) (sz.W n) (m n) (E n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
          (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) x y ≤ δ n
            then GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                  (mixMatBA sz n (g n) (a n k) (b n k) ω) i j ^ 2
            else 0)} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **Pin `GUEEntryMixBA' d`** (T2519 Amend 4 item 2): the text of `GUEEntryMixBA d` with the family premise split into
`BAReal` at every `n` and the coupling window `0 < g n ≤ 𝔡⁻¹` eventually (`StochDomAt` is eventual; the BA producers have
`g n = √t₀ λ_n` with `0 < g n` only eventually). -/
def GUEEntryMixBA' (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ (g E : ℕ → ℝ) (m : ℕ → ℂ), (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
  (∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹) →
  ∀ n0 : ℕ, ∀ K : ℕ → ℕ, (∀ n, K n ≤ (sz.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ,
  (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) →
  ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) →
  (∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) →
  ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
    ouP (UNModel.band (sz.withLam 0)) n
      {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
        ((sz.size n : ℕ) : ℝ) ^ τ *
            (GUEEntry_maxLoop d (sz.L n) (sz.W n) (m n) (E n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
          (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) x y ≤ δ n
            then GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                  (mixMatBA sz n (g n) (a n k) (b n k) ω) i j ^ 2
            else 0)} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

section Main
variable {d : ℕ} 

/-- `√(W^{-d}) ≤ N^{-𝔠 d / 2}` from the bandwidth `N^𝔠 ≤ W`. -/
theorem GUEEntry_sqrt_w0_le {N W 𝔠 : ℝ} {d : ℕ} (hN1 : 1 ≤ N) (hW : N ^ 𝔠 ≤ W) (h𝔠 : 0 < 𝔠) (hd : 0 < d) :
    Real.sqrt ((W ^ d)⁻¹) ≤ N ^ (-(𝔠 * d / 2)) := by
  have hN0 : 0 < N := by linarith
  have hb0 : 0 ≤ N ^ 𝔠 := Real.rpow_nonneg hN0.le _
  have hWd : N ^ (𝔠 * d) ≤ W ^ d := by
    rw [Real.rpow_mul hN0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ hb0 hW d
  rw [Real.sqrt_le_iff]
  refine ⟨Real.rpow_nonneg hN0.le _, ?_⟩
  have hsq : (N ^ (-(𝔠 * d / 2))) ^ 2 = (N ^ (𝔠 * d))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]
    congr 1; push_cast; ring
  rw [hsq]
  have hpos : 0 < N ^ (𝔠 * d) := Real.rpow_pos_of_pos hN0 _
  exact inv_anti₀ hpos hWd

set_option maxHeartbeats 800000 in
-- the `n`-wise engine of the pin: smallness, the union bound and the final arithmetic in one proof
/-- **`GUEEntryMixBA' d` is proved, `d ≥ 3`** (T2519 Amend 4 item 2): the proof of `gueEntryMixBA` (below, now a wrapper) with the
coupling window `0 < g n ≤ 𝔡⁻¹` taken eventually, as one more entry of the `filter_upwards`; `BAReal` is used at that `n`. -/
theorem gueEntryMixBA' (hd : 3 ≤ d) : GUEEntryMixBA' d := by
  intro 𝔠 𝔡 sz hAdm κ hκ g E m hrdata hwin n0 K hK a b hab c₀ δ hc₀ hδ0 hδ τ D hτ hD
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hAdm
  have hsz0 : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hd0 : 0 < d := by omega
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  set c₁ : ℝ := min c₀ (𝔠 * d / 2) with hc₁
  have hc₁0 : 0 < c₁ := lt_min hc₀ (by positivity)
  have hc₁c : c₁ ≤ c₀ := min_le_left _ _
  have hc₁d : c₁ ≤ 𝔠 * d / 2 := min_le_right _ _
  set τ' : ℝ := min (τ / 4) c₁ with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) hc₁0
  have hτ'c : τ' ≤ c₁ := min_le_right _ _
  have hτ'τ : τ' ≤ τ / 4 := min_le_left _ _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, D + n0 + 3 ≤ τ' * (q + 1) := by
    refine ⟨⌈(D + n0 + 3) / τ'⌉₊, ?_⟩
    have h1 := Nat.le_ceil ((D + n0 + 3) / τ')
    rw [div_le_iff₀ hτ'0] at h1
    nlinarith [hτ'0]
  have hc₀' : 0 < BAct_rate d 𝔡⁻¹ κ := BAct_rate_pos d 𝔡⁻¹ κ hd0 hΛ hκ
  have hKbd : 0 < GUEEntry_Kbd d 𝔡⁻¹ κ := by unfold GUEEntry_Kbd GUEEntry_rho GUEEntry_Kth expC; positivity
  have hdlt0 : 0 < GUEEntry_dlt d 𝔡⁻¹ κ := lt_min (by positivity) (by positivity)
  have hcs0 : 0 ≤ GUEEntry_cs d 𝔡⁻¹ κ := by
    unfold GUEEntry_cs GUEEntry_rho GUEEntry_Sc expC; positivity
  filter_upwards [hsz.eventually_ge_atTop 1, hδ, hbw,
    hsz0.eventually (eventually_le_rpow (GUEEntry_dlt d 𝔡⁻¹ κ)⁻¹ hc₁0),
    hsz0.eventually (eventually_le_rpow (GUEEntry_cs d 𝔡⁻¹ κ) hc₁0),
    hsz0.eventually (eventually_le_rpow 2 hτ'0),
    hsz0.eventually (eventually_le_rpow (GUEEntry_C d 𝔡⁻¹ κ) (half_pos hτ)),
    hsz.eventually_ge_atTop (8 * mixCq q), hwin] with n hN1 hδn hbwn hdltn hcsn hΦ2 hCn hCq hwn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  obtain ⟨hg, hgΛ⟩ := hwn
  have hr := hrdata n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set w₀ : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hw₀
  have hw0 : 0 ≤ w₀ := by positivity
  set δ' : ℝ := max (δ n) (Real.sqrt w₀) with hδ'
  have hδδ' : δ n ≤ δ' := le_max_left _ _
  have hδ'0 : 0 ≤ δ' := (hδ0 n).trans hδδ'
  have hwd : w₀ ≤ δ' ^ 2 := by
    have : (Real.sqrt w₀) ^ 2 = w₀ := Real.sq_sqrt hw0
    nlinarith [pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right (δ n) (Real.sqrt w₀)) 2]
  -- `δ' ≤ N^{-c₁}`
  have hNc : N ^ (-c₁) ≤ GUEEntry_dlt d 𝔡⁻¹ κ := by
    rw [Real.rpow_neg hN0.le]
    calc (N ^ c₁)⁻¹ ≤ ((GUEEntry_dlt d 𝔡⁻¹ κ)⁻¹)⁻¹ := inv_anti₀ (by positivity) hdltn
      _ = _ := inv_inv _
  have hδn1 : δ n ≤ N ^ (-c₁) :=
    hδn.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hsq1 : Real.sqrt w₀ ≤ N ^ (-c₁) :=
    (GUEEntry_sqrt_w0_le hN1 hbwn h𝔠 hd0).trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hδ'1 : δ' ≤ N ^ (-c₁) := max_le hδn1 hsq1
  have hδ'dlt : δ' ≤ GUEEntry_dlt d 𝔡⁻¹ κ := hδ'1.trans hNc
  have hΦ1 : 1 ≤ N ^ τ' := Real.one_le_rpow hN1 hτ'0.le
  have hΦδ : GUEEntry_cs d 𝔡⁻¹ κ * N ^ τ' * δ' ^ 2 ≤ 1 := by
    have h1 : δ' ^ 2 ≤ (N ^ (-c₁)) ^ 2 := pow_le_pow_left₀ hδ'0 hδ'1 2
    have h2 : N ^ τ' * (N ^ (-c₁)) ^ 2 ≤ N ^ (-c₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
    have h3 : GUEEntry_cs d 𝔡⁻¹ κ * N ^ (-c₁) ≤ 1 := by
      rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hN0 _)]
      exact hcsn
    calc GUEEntry_cs d 𝔡⁻¹ κ * N ^ τ' * δ' ^ 2 ≤ GUEEntry_cs d 𝔡⁻¹ κ * (N ^ τ' * (N ^ (-c₁)) ^ 2) := by
          have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hcs0 (Real.rpow_nonneg hN0.le τ'))
          linarith
      _ ≤ GUEEntry_cs d 𝔡⁻¹ κ * N ^ (-c₁) := mul_le_mul_of_nonneg_left h2 hcs0
      _ ≤ 1 := h3
  have hΦsq : (N ^ τ') ^ 2 ≤ N ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    push_cast; nlinarith
  have hT : GUEEntry_C d 𝔡⁻¹ κ * (N ^ τ') ^ 2 ≤ N ^ τ := by
    calc GUEEntry_C d 𝔡⁻¹ κ * (N ^ τ') ^ 2 ≤ N ^ (τ / 2) * N ^ (τ / 2) :=
          mul_le_mul hCn hΦsq (sq_nonneg _) (Real.rpow_nonneg hN0.le _)
      _ = N ^ τ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hmain := GUEEntry_union hd sz n hg hgΛ hκ hr (hab n) hδ'0 hδ'dlt hwd hΦ2 hΦδ hT q
  -- the pin event is inside the event at the enlarged `δ'`
  have hsub : {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      N ^ τ * (GUEEntry_maxLoop d (sz.L n) (sz.W n) (m n) (E n) (a n k + b n k) (mixMatBA sz n (g n) (a n k) (b n k) ω) + w₀) <
        (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
              (mixMatBA sz n (g n) (a n k) (b n k) ω) x y ≤ δ n
          then GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) i j ^ 2 else 0)} ⊆
      {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      N ^ τ * (GUEEntry_maxLoop d (sz.L n) (sz.W n) (m n) (E n) (a n k + b n k) (mixMatBA sz n (g n) (a n k) (b n k) ω) + w₀) <
        (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
              (mixMatBA sz n (g n) (a n k) (b n k) ω) x y ≤ δ'
          then GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) i j ^ 2 else 0)} := by
    rintro ω ⟨k, i, j, hω⟩
    refine ⟨k, i, j, lt_of_lt_of_le hω ?_⟩
    by_cases h1 : ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
        (mixMatBA sz n (g n) (a n k) (b n k) ω) x y ≤ δ n
    · have h2 : ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
          (mixMatBA sz n (g n) (a n k) (b n k) ω) x y ≤ δ' := fun x y => (h1 x y).trans hδδ'
      simp only [h1, h2, implies_true, ↓reduceIte, le_refl]
    · rw [ite_eq_right h1]
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
  refine (measure_mono hsub).trans (hmain.trans (ENNReal.ofReal_le_ofReal ?_))
  have hK' : (K n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ n0 := by exact_mod_cast hK n
  exact mixEntry_final_arith hN1 hK' hq (mixCq_pos q).le hCq

end Main

end ProbPart

/-! ## Compiled nonempty instances (T2515b, row b; CLAUDE.md §4 step 2), `d = 3`

* `stable_mixBA`: the flow point of `(L, g) = (4, 3/10)` (`UNPinsInst.fp`, `κ = Im m₀ > 0`), `(a, b) = (1/4, 1/4)`,
  `v ≡ 1`, `B = 33`; every hypothesis is discharged.
* `gueEntryMixBA` (the pin `GUEEntryMixBA 3`): the class sequence `S0` (`L = 4`, `W_n = (2 (n + 1))^5`, admissible at
  `(1/6, 1/10)`), constant flow data, `K ≡ 1`, two mixtures, `δ_n = N^{-1}`, `τ = D = 1`; every hypothesis is discharged.
* `mixEntry_detBA` and `mix_detBA`: `sz0` at `n = 25` (`L = 104`, `W = 52^5 = 380204032`, `N = (W L)^3`), the flow point
  `(g₁, E₁, m₁)` of `flow_sz0` with `κ = 1/2`, `Λ = 1/64`, `δ = 10⁻¹²`, `Φ = 1`; the numerical facts
  (`BAct_rate 3 (1/64) (1/2) = 1/4`, `10⁻¹² ≤ GUEEntry_dlt`, `GUEEntry_cs · δ² ≤ 1`, `W^{-3} ≤ δ²`) are proved.
  At `(a, b) = (1/4, 1/4)` the Hermitian matrix `X` (for `mix_detBA`: the carrier of `GreenCore_carrier`, any sample), the
  a priori event and the four large deviation inputs stay hypotheses (the events of `GUEEntry_bad`, discharged on the
  probability side by `gueEntryMixBA`), as in the band instance `inst_mixEntry_det`; at `(a, b) = (0, 0)` (`X = 0`,
  `G = M`) every hypothesis is discharged.
* `mixMatBA` and its three identities at `sz0`; `GUEEntry_bad_tail` at `Idx 3 3 2`. -/

/-! ### The numerical facts at `(d, Λ, κ) = (3, 1/64, 1/2)` -/

/-! ### Obstruction: no fully discharged `X = 0` instance of `mixEntry_detBA` / `mix_detBA` at `0 < a + b`

At `X = 0` the Ward identity for the minor `G^{(i)}` and `|G^{(i)}_{kk}| ≥ 2κ/3` (a priori event) give, in the quadratic
large deviation input, `Im z² (2κ/3)² (1 - W^{-d}) ≤ 2 Φ W^{-d}`, i.e. `Φ ≳ W^d`; with `W^{-d} ≤ δ²` and
`GUEEntry_cs Φ δ² ≤ 1` (`GUEEntry_cs ≥ 832 κ⁻⁴`) this is impossible.  Shown for `0 ≤ a ≤ b`, `0 < b`, `a + b ≤ 1/2`. -/

set_option maxHeartbeats 1600000 in
-- one proof: the minor Ward identity, the two bounds on `ldeQuadRHS`/`ldeQuadLHS` and the count
/-! ### `mixMatBA` and the tails at `sz0`, `Idx 3 3 2` -/

end RBM.BA
