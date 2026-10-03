/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLTree

/-!
# The closed form of fully summed trees, and the sum-zero bound given `Q(1) = 0`, `d ≥ 3`

Ticket T2043 (KL7a).  Paper: `(eq:Sigma-empty-sum-zero)`, first estimate
(`paper/tex/A_deterministic_estimates.tex:731`; its dimension-independent proof is cited there
from [YY_25] Lemma 3.10 and [RBSO1D] Lemma 4.29; RBM2D's label for it is `(SZjadljsk)`), with the
molecule decomposition `(eq:molecule-Kpi)` (`:625`) and the definition `(eq:defKpi)` (`:611`) of
`K^{(π)}`.

Port of `../RBM2D/RBM2D/Loop/SumZero.lean` at `c9a24cf` (914 lines): `sum_out`, `treeZ`,
`treeZ_peel`, `treeZ_eq`, `sum_selfW`, `edgeR`, `Qlayer`, `Alayer`, `SumZero_sum_Theta_col`,
`sum_Theta_sub_one_col`, `sum_Theta_sub_one_row`, `SumZero_sum_Kpi_eq`, `sum_SigmaPi`,
`sum_Kpi_closed`, `SumZero_SigmaPi_add_const`, `SumZero_sum_slice`, `SumZero_sum_slice_alt`,
`SigmaPi_alt_sumZero_le_of_Qlayer_one`, and the bulk gap `gapK` with (F3) `gapK_le_norm`
(`gapK` is `RBM2D/Loop/Kcal.lean:311`).  Renaming (T2008, T2014, T2020, T2025, T2036):
`Z2 L ↦ Zd d L`, `L² ↦ L^d`, `Theta L ↦ Theta d L g`, `Kpi ↦ KLKpi`, `SigmaPi ↦ KLSigmaPi`,
`selfW ↦ KLselfW`, `TSPlong ↦ KLTSPlong`, `sigAlt ↦ KLsigAlt`, `mSig ↦ mSigma`,
`spectralM ↦ mE`, `etaT ↦ Gauss.etaT`; the laminar API of `KLTree.lean` replaces the private
`LaminarLite` of the source, and the merged `KLKpi_eq_sum_SigmaPi` replaces its private
`treeValW_eq_sum_selfW'`.

**What differs from RBM2D beyond renaming and exponents.**  The merged `KLKpi`, `KLSigmaPi`
(`KLTree.lean:351, 366`) carry the factor `∏_i m(σ_i)` of `Γ^{(n)}_M` (paper `(eq:defKpi)`,
`(M-graph-value-unsummed)`, `A_deterministic_estimates.tex:611, 357`), which RBM2D's `Kpi`,
`SigmaPi` do not (there the factor stands in front of `Kn`).  Hence

* `Alayer` is `(∏_i m(σ_i)) · ∏_v (1 - ξ_v)⁻¹ · Q(σ,π)`, so that `sum_Kpi_closed` reads as in
  RBM2D, `∑_a K^{(π)} = L^d · A(σ,π)` (`KLSumZero_neg_Kpi_closed_2Dform` compiles that RBM2D's
  `A`, without the factor, is false for the merged `KLKpi`: pure triangle, `-8i` against `8`);
* `sum_SigmaPi` and `SumZero_sum_slice` carry the explicit factor `∏_i m(σ_i)`;
* `SumZero_sum_slice_alt` and `SigmaPi_alt_sumZero_le_of_Qlayer_one` keep RBM2D's statement:
  for `σ^{(alt)}` and `n` even the factor is `(m m̄)^{n/2} = 1`.

`Qlayer`, `edgeR` are RBM2D's.  `d` and `g` are free: no `3 ≤ d` and no condition on `g` enters
(`norm_SB`, `SB_mulVec_one` hold for every real `g`).
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. A light laminar API (private) -/

section LaminarLite

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem isDiag_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {J : Fin n × Fin n} (hJ : J ∈ F) : IsDiag n J.1 J.2 :=
  (KLisTSP_of_mem_TSP hF).1 J hJ

omit [NeZero n] in
private theorem crossingFree_of_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    CrossingFree F :=
  (KLisTSP_of_mem_TSP hF).2

private theorem wholeP_not_mem_TSP {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    KLwholeP n ∉ F :=
  KLwholeP_not_mem (KLisTSP_of_mem_TSP hF)

/-- The parent of a diagonal of a tree is a strictly larger node (merged `KLnodePar_spec`). -/
private theorem nodePar_up {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {J : Fin n × Fin n} (hJ : J ∈ F) : KLArcLe J (KLnodePar F J) ∧ KLnodePar F J ≠ J := by
  have hF' := KLisTSP_of_mem_TSP hF
  have hn : 2 ≤ n := by
    have h1 := (hF'.1 J hJ).1
    have := J.2.isLt
    rw [Fin.lt_def] at h1
    omega
  obtain ⟨-, h1, h2, -⟩ := KLnodePar_spec hF' hn (KLmem_nodes_of_mem hJ) (KLne_wholeP hF' hJ)
  exact ⟨h1, h2⟩

omit [NeZero n] in
private theorem arcWidth_lt {J e : Fin n × Fin n} (hJe : KLArcLe J e) (hne : J ≠ e)
    (hJ : J.1 ≤ J.2) : KLarcWidth J < KLarcWidth e :=
  lt_of_le_of_ne (KLarcWidth_le_of_arcLe hJe) fun heq =>
    hne (KLeq_of_arcLe_of_width hJ hJe heq.ge)

end LaminarLite

/-! ## 2. Summing out one coordinate -/

section SumOut

/-- **Summing out one coordinate.**  If `f` does not depend on the coordinate `i`, and `G y b`
does not depend on it either and has `∑_y G y b = r`, then
`|Z| ∑_b f(b) G(b_i, b) = r ∑_b f(b)`.  (Port of RBM2D `SumZero.lean:92`, itself a port of RBM1D
`sum_out`; dimension-free.) -/
theorem sum_out {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z] (i : ι)
    (f : (ι → Z) → ℂ) (G : Z → (ι → Z) → ℂ) (r : ℂ)
    (hf : ∀ b x, f (Function.update b i x) = f b)
    (hG : ∀ b x y, G y (Function.update b i x) = G y b)
    (hr : ∀ b, ∑ x, G x b = r) :
    (Fintype.card Z : ℂ) * ∑ b, f b * G (b i) b = r * ∑ b, f b := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨x0⟩⟩
  · have : IsEmpty (ι → Z) := ⟨fun b => isEmptyElim (b i)⟩
    simp
  set e := Equiv.piSplitAt i (fun _ : ι => Z)
  have hs : ∀ x b', e.symm (x, b') = Function.update (e.symm (x0, b')) i x := by
    intro x b'
    funext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hj]
  have hsi : ∀ x b', e.symm (x, b') i = x := by
    intro x b'; rw [hs, Function.update_self]
  have h1 : ∀ x b', f (e.symm (x, b')) = f (e.symm (x0, b')) := by
    intro x b'; rw [hs, hf]
  have h2 : ∀ x y b', G y (e.symm (x, b')) = G y (e.symm (x0, b')) := by
    intro x y b'; rw [hs, hG]
  rw [← Equiv.sum_comp e.symm, ← Equiv.sum_comp e.symm (fun b => f b),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hl : ∀ x, ∑ b' : {j // j ≠ i} → Z, f (e.symm (x, b')) * G (e.symm (x, b') i) (e.symm (x, b'))
      = ∑ b' : {j // j ≠ i} → Z, f (e.symm (x0, b')) * G x (e.symm (x0, b')) := by
    intro x
    refine sum_congr rfl fun b' _ => ?_
    rw [h1, hsi, h2]
  have hr' : ∀ x, ∑ b' : {j // j ≠ i} → Z, f (e.symm (x, b'))
      = ∑ b' : {j // j ≠ i} → Z, f (e.symm (x0, b')) := fun x => sum_congr rfl fun b' _ => h1 x b'
  simp only [hl, hr']
  rw [sum_comm, sum_const, card_univ, nsmul_eq_mul]
  simp only [← mul_sum, hr]
  rw [← sum_mul]
  ring

end SumOut

/-! ## 3. Fully summed trees -/

section TreeSum

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem card_Zd_cast : (Fintype.card (Zd d L) : ℂ) = (L : ℂ) ^ d := by
  rw [card_Zd, Nat.cast_pow]

/-- A tree without boundary edges, all labels summed: `∑_b ∏_e E_e(b_e, b_{par e})`. -/
noncomputable def treeZ (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) : ℂ :=
  ∑ b : ↥(KLnodes F) → Zd d L,
    ∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)

/-- **Peeling.**  If every edge weight has constant column sums `r_e`, then for every set `G`
of edges, `(L^d)^{|G|} ∑_b ∏_{e ∈ G} E_e(b_e, b_{par e}) = ∏_{e ∈ G} r_e · ∑_b 1`.  An edge
of `G` of smallest arc is childless in `G`, so its lower label can be summed out
(`sum_out`). -/
theorem treeZ_peel {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (r : ↥F → ℂ) (hr : ∀ J y, ∑ x, E J x y = r J) :
    ∀ G : Finset ↥F, ((L : ℂ) ^ d) ^ G.card * ∑ b : ↥(KLnodes F) → Zd d L,
        ∏ J ∈ G, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩) =
      (∏ J ∈ G, r J) * ∑ _b : ↥(KLnodes F) → Zd d L, (1 : ℂ) := by
  intro G
  induction G using Finset.strongInduction with
  | H G ih =>
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨e, he, hmin⟩ := G.exists_min_image (fun J : ↥F => KLarcWidth J.1) hne
  set i : ↥(KLnodes F) := ⟨e.1, KLmem_nodes_of_mem e.2⟩
  have hpe := nodePar_up hF e.2
  -- the parents of the other edges of `G` are not `e`
  have hpar : ∀ J ∈ G.erase e, KLnodePar F J.1 ≠ e.1 := by
    intro J hJ heq
    obtain ⟨hJne, hJG⟩ := mem_erase.1 hJ
    obtain ⟨hJp, hpJ⟩ := nodePar_up hF J.2
    rw [heq] at hJp hpJ
    have hJJ : J.1.1 ≤ J.1.2 := le_of_lt (isDiag_of_mem_TSP hF J.2).1
    have := arcWidth_lt hJp (Ne.symm hpJ) hJJ
    exact absurd (hmin J hJG) (not_le.2 this)
  have hself : ∀ J ∈ G.erase e, (⟨J.1, KLmem_nodes_of_mem J.2⟩ : ↥(KLnodes F)) ≠ i := by
    intro J hJ h
    have h' : J.1 = e.1 := by simpa [i] using congrArg Subtype.val h
    exact (mem_erase.1 hJ).1 (Subtype.ext h')
  set f : (↥(KLnodes F) → Zd d L) → ℂ := fun b =>
    ∏ J ∈ G.erase e, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)
  set Gf : Zd d L → (↥(KLnodes F) → Zd d L) → ℂ := fun y b =>
    E e y (b ⟨KLnodePar F e, KLnodePar_mem F e⟩)
  have hsplit : ∀ b : ↥(KLnodes F) → Zd d L,
      ∏ J ∈ G, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)
        = f b * Gf (b i) b := by
    intro b
    rw [← mul_prod_erase G _ he, mul_comm]
  have hf : ∀ b x, f (Function.update b i x) = f b := by
    intro b x
    refine prod_congr rfl fun J hJ => ?_
    have h1 : (⟨KLnodePar F J, KLnodePar_mem F J⟩ : ↥(KLnodes F)) ≠ i := by
      intro h; exact hpar J hJ (congrArg Subtype.val h)
    rw [Function.update_of_ne (hself J hJ), Function.update_of_ne h1]
  have hG : ∀ b x y, Gf y (Function.update b i x) = Gf y b := by
    intro b x y
    have h1 : (⟨KLnodePar F e, KLnodePar_mem F e⟩ : ↥(KLnodes F)) ≠ i := by
      intro h; exact hpe.2 (congrArg Subtype.val h)
    simp only [Gf, Function.update_of_ne h1]
  have hsum := sum_out i f Gf (r e) hf hG (fun b => hr e _)
  rw [card_Zd_cast] at hsum
  have hcard : G.card = (G.erase e).card + 1 := (card_erase_add_one he).symm
  have hlt : G.erase e ⊂ G := erase_ssubset he
  have hih := ih _ hlt
  simp only [hsplit]
  rw [hcard, pow_succ, mul_assoc, hsum, ← mul_prod_erase G _ he]
  rw [mul_left_comm, hih]
  ring

/-- **The closed form of a fully summed tree**: `∑_b ∏_e E_e(b_e, b_{par e}) = L^d ∏_e r_e`. -/
theorem treeZ_eq {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (r : ↥F → ℂ) (hr : ∀ J y, ∑ x, E J x y = r J) :
    treeZ F E = (L : ℂ) ^ d * ∏ J, r J := by
  have h := treeZ_peel hF E r hr univ
  have hc : Fintype.card ↥(KLnodes F) = F.card + 1 := by
    rw [Fintype.card_coe, KLnodes, card_insert_of_notMem (wholeP_not_mem_TSP hF)]
  have hone : ∑ _b : ↥(KLnodes F) → Zd d L, (1 : ℂ) = ((L : ℂ) ^ d) ^ (F.card + 1) := by
    rw [sum_const, card_univ, Fintype.card_pi, prod_const, card_univ, hc, nsmul_eq_mul,
      mul_one]
    push_cast
    rw [← card_Zd_cast (d := d) (L := L)]
  rw [hone, card_univ, Fintype.card_coe] at h
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hpow : ((L : ℂ) ^ d) ^ F.card ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hL0)
  unfold treeZ
  apply mul_left_cancel₀ hpow
  rw [h]
  ring

/-- Summing the self-energy over `δ` removes the Kronecker deltas. -/
theorem sum_selfW (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) :
    ∑ δ : Fin n → Zd d L, KLselfW d L F E δ = treeZ F E := by
  unfold KLselfW treeZ
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_mul]
  have h := (prod_univ_sum (fun _ : Fin n => (univ : Finset (Zd d L)))
    (fun v x => if x = b ⟨KLleafPar F v, KLleafPar_mem F v⟩ then (1 : ℂ) else 0)).symm
  rw [Fintype.piFinset_univ] at h
  rw [h]
  simp

end TreeSum

/-! ## 4. The closed forms `Q(σ,π)` and `A(σ,π)` -/

section Closed

variable {n : ℕ} [NeZero n]

/-- The column sum of an internal edge `Θ_ξ - 1`, `ξ = t m(s) m(s')`: `(1 - ξ)^{-1} - 1`. -/
noncomputable def edgeR (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : ℂ :=
  (1 - (t : ℂ) * (m s * m s'))⁻¹ - 1

/-- `Q(σ,π) = ∑_{F ∈ T_SP(σ,π)} ∏_{e ∈ F} ((1 - ξ_e)^{-1} - 1)`; it depends neither on `L`, `d`,
`g` nor on `W`. -/
noncomputable def Qlayer (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  ∑ F ∈ KLTSPlong n σ π, ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2)

/-- `A(σ,π) = L^{-d} ∑_a K^(π)(t,σ,a) = (∏_i m(σ_i)) ∏_v (1 - ξ_v)^{-1} · Q(σ,π)`
(`sum_Kpi_closed`); it depends neither on `L`, `d`, `g` nor on `W`.  The factor `∏_i m(σ_i)` is
the one of the merged `KLKpi` (RBM2D's `Alayer` has none). -/
noncomputable def Alayer (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  (∏ i, m (σ i)) * ((∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) * Qlayer m t σ π)

/-- Column sums of `Θ_ξ` on `Z_L^d`: `∑_x (Θ_ξ)_{xy} = (1 - ξ)^{-1}`. -/
theorem SumZero_sum_Theta_col {d L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (y : Zd d L) :
    ∑ x : Zd d L, Theta d L g ξ x y = (1 - ξ)⁻¹ := by
  rw [← sum_Theta_row_of_three_le (g := g) hL hξ y]
  refine sum_congr rfl fun x _ => ?_
  exact congrFun (congrFun (Theta_transpose_of_three_le (g := g) hL hξ) y) x

/-- Column sums of an internal edge weight: `∑_x (Θ_ξ - 1)_{xy} = (1 - ξ)^{-1} - 1`. -/
theorem sum_Theta_sub_one_col {d L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (y : Zd d L) :
    ∑ x : Zd d L, (Theta d L g ξ - 1) x y = (1 - ξ)⁻¹ - 1 := by
  simp only [Matrix.sub_apply, sum_sub_distrib, SumZero_sum_Theta_col (g := g) hL hξ,
    Matrix.one_apply]
  simp

/-- Row sums of an internal edge weight: `∑_y (Θ_ξ - 1)_{xy} = (1 - ξ)^{-1} - 1`. -/
theorem sum_Theta_sub_one_row {d L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {ξ : ℂ}
    (hξ : ‖ξ‖ < 1) (x : Zd d L) :
    ∑ y : Zd d L, (Theta d L g ξ - 1) x y = (1 - ξ)⁻¹ - 1 := by
  simp only [Matrix.sub_apply, sum_sub_distrib, sum_Theta_row_of_three_le (g := g) hL hξ,
    Matrix.one_apply]
  simp

variable (d L : ℕ) [NeZero L] (g : ℝ) (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- The step (3.47)–(3.48) of RBM2D's numbering, on `Z_L^d` (first stage of `(eq:molecule-Kpi)`
summed over `a`): `∑_a K^(π)(t,σ,a) = ∏_i (1 - t m_i m_{i+1})^{-1} ∑_δ Σ^(π)(t,σ,δ)`. -/
theorem SumZero_sum_Kpi_eq (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → Zd d L, KLKpi d L g m t σ a π =
      (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) *
        ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ := by
  simp_rw [KLKpi_eq_sum_SigmaPi d L g m t σ _ π]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun δ _ => ?_
  rw [← mul_sum, mul_comm]
  congr 1
  have h := (prod_univ_sum (fun _ : Fin n => (univ : Finset (Zd d L)))
    (fun v x => thetaEdge d L g m t (σ v) (σ (v + 1)) x (δ v))).symm
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine prod_congr rfl fun v _ => ?_
  exact SumZero_sum_Theta_col hL (hm _ _) (δ v)

/-- `∑_δ Σ^(π)(t,σ,δ) = L^d · (∏_i m(σ_i)) · Q(σ,π)` on `Z_L^d`. -/
theorem sum_SigmaPi (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ =
      (L : ℂ) ^ d * ((∏ i, m (σ i)) * Qlayer m t σ π) := by
  have h1 : ∀ F ∈ KLTSPlong n σ π,
      ∑ δ : Fin n → Zd d L,
          KLselfW d L F (fun J => thetaEdge d L g m t (σ J.1.1) (σ J.1.2) - 1) δ =
        (L : ℂ) ^ d * ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2) := by
    intro F hF
    have hT : F ∈ TSP n := (mem_filter.1 hF).1
    rw [sum_selfW, treeZ_eq hT (fun e => thetaEdge d L g m t (σ e.1.1) (σ e.1.2) - 1)
      (fun e => edgeR m t (σ e.1.1) (σ e.1.2))
      (fun e y => sum_Theta_sub_one_col hL (hm _ _) y)]
    rw [prod_coe_sort F (fun e => edgeR m t (σ e.1) (σ e.2))]
  unfold KLSigmaPi Qlayer
  rw [← mul_sum, sum_comm, sum_congr rfl h1, ← mul_sum]
  ring

/-- **The closed form of (3.48)** (RBM2D's numbering) on `Z_L^d`:
`∑_a K^(π)(t,σ,a) = L^d · A(σ,π)`. -/
theorem sum_Kpi_closed (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → Zd d L, KLKpi d L g m t σ a π = (L : ℂ) ^ d * Alayer m t σ π := by
  rw [SumZero_sum_Kpi_eq d L g m hm hL, sum_SigmaPi d L g m hm hL, Alayer]
  ring

end Closed

/-! ## 5. Translation invariance and the slice form -/

section SliceHelpers

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- If every edge weight is translation invariant, so is the self-energy of a tree. -/
private theorem selfW_add_const (F : Finset (Fin n × Fin n))
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ)
    (hE : ∀ e x y c, E e (x + c) (y + c) = E e x y) (δ : Fin n → Zd d L) (c : Zd d L) :
    KLselfW d L F E (fun v => δ v + c) = KLselfW d L F E δ := by
  unfold KLselfW
  rw [← Equiv.sum_comp (Equiv.addRight (fun _ : ↥(KLnodes F) => c))]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, Pi.add_apply, add_left_inj, hE]

private theorem Theta_sub_one_add_const {g : ℝ} (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (x y c : Zd d L) : (Theta d L g ξ - 1) (x + c) (y + c) = (Theta d L g ξ - 1) x y := by
  simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj,
    Theta_apply_add_right_of_three_le hL hξ]

end SliceHelpers

section Slice

variable {n : ℕ} [NeZero n] (d L : ℕ) [NeZero L] (g : ℝ) (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- **Translation invariance** of `Σ^(π)` on `Z_L^d` (RBM2D: Lemma 3.10 (1) of [YY_25]), for every
`σ` and `π`: `Σ^(π)(t,σ,δ + c) = Σ^(π)(t,σ,δ)`. -/
theorem SumZero_SigmaPi_add_const (hL : 3 ≤ L) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) (c : Zd d L) :
    KLSigmaPi d L g m t σ π (fun v => δ v + c) = KLSigmaPi d L g m t σ π δ := by
  unfold KLSigmaPi
  congr 1
  refine sum_congr rfl fun F _ => selfW_add_const F _ (fun e x y c => ?_) δ c
  exact Theta_sub_one_add_const hL (hm _ _) x y c

/-- **The slice form** (`d₁`-pinned form): with the label `δ_i = x` fixed,
`∑_{δ : δ_i = x} Σ^(π)(t,σ,δ) = (∏_j m(σ_j)) · Q(σ,π)`, for every `σ`, `π`, `i` and `x`; the
value depends neither on `L` nor on `x`. -/
theorem SumZero_sum_slice (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (i : Fin n) (x : Zd d L) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ i = x), KLSigmaPi d L g m t σ π δ =
      (∏ j, m (σ j)) * Qlayer m t σ π := by
  set S : Zd d L → ℂ := fun x =>
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ i = x), KLSigmaPi d L g m t σ π δ with hSdef
  have hS : ∀ x c : Zd d L, S (x + c) = S x := by
    intro x c
    simp only [hSdef, sum_filter]
    rw [← Equiv.sum_comp (Equiv.addRight (fun _ : Fin n => c))]
    refine sum_congr rfl fun δ _ => ?_
    simp only [Equiv.coe_addRight, Pi.add_apply, add_left_inj]
    split_ifs
    · exact SumZero_SigmaPi_add_const d L g m hm hL σ π δ c
    · rfl
  have hS0 : ∀ x : Zd d L, S x = S 0 := fun x => by
    have := hS 0 x
    rwa [zero_add] at this
  have htot : ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ = (L : ℂ) ^ d * S 0 := by
    rw [← sum_fiberwise univ (fun δ : Fin n → Zd d L => δ i) (KLSigmaPi d L g m t σ π)]
    change ∑ y : Zd d L, S y = _
    simp only [hS0, sum_const, card_univ, nsmul_eq_mul]
    rw [card_Zd_cast]
  rw [sum_SigmaPi d L g m hm hL] at htot
  have hL0 : (L : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have h0 : S 0 = (∏ j, m (σ j)) * Qlayer m t σ π := (mul_left_cancel₀ hL0 htot).symm
  change S x = _
  rw [hS0, h0]

end Slice

/-! ## 6. The bulk gap and the estimates for the Lipschitz step -/

section Estimates

/-- The bulk gap `c_κ`: `c_κ ≤ |1 - t m^{(E)2}|` for `t ∈ [0,1]`, `|E| ≤ 2 - κ`
(`gapK_le_norm`, (F3)).  Port of `RBM2D/Loop/Kcal.lean:311`; `d`-free and `g`-free. -/
noncomputable def gapK (κ : ℝ) : ℝ := min 1 (Real.sqrt (κ * (4 - κ) / 2))

private theorem gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ := by
  unfold gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

private theorem gapK_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    gapK κ ^ 2 ≤ κ * (4 - κ) / 2 := by
  have h0 : 0 ≤ gapK κ := (gapK_pos hκ hκ2).le
  have h1 : gapK κ ≤ Real.sqrt (κ * (4 - κ) / 2) := min_le_right _ _
  have h2 : Real.sqrt (κ * (4 - κ) / 2) ^ 2 = κ * (4 - κ) / 2 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith

/-- `|1 - t m²|² = (1 - t)² + t (4 - E²)`. -/
private theorem norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    ‖1 - (t : ℂ) * (mE E * mE E)‖ ^ 2 = (1 - t) ^ 2 + t * (4 - E ^ 2) := by
  have hre : (mE E).re = -E / 2 := mE_re E
  have him := mE_im E
  have hs := sq_sqrt_four_sub hE
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  linear_combination
    ((1 - t * E ^ 2 / 4) * t / 2 + t ^ 2 * (Real.sqrt (4 - E ^ 2) ^ 2 + 4 - E ^ 2) / 16
      + t ^ 2 * E ^ 2 / 4) * hs

/-- **(F3)**: the bulk gap `c_κ ≤ |1 - t m(s)²|` for `t ≥ 0` (in particular `t ∈ [0,1]`)
and `|E| ≤ 2 - κ`. -/
theorem gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t)
    (s : Bool) :
    gapK κ ≤ ‖1 - (t : ℂ) * (mSigma E s * mSigma E s)‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hsq : gapK κ ^ 2 ≤ ‖1 - (t : ℂ) * (mE E * mE E)‖ ^ 2 := by
    rw [norm_one_sub_sq hE2]
    have hg1 : gapK κ ^ 2 ≤ 1 := by
      have := gapK_le_one κ
      have := (gapK_pos hκ hκ2).le
      nlinarith
    have hg2 := gapK_sq_le hκ hκ2
    by_cases h2 : 2 ≤ 4 - E ^ 2
    · nlinarith
    · nlinarith [sq_nonneg (1 - t - (4 - E ^ 2) / 2)]
  have hle : gapK κ ≤ ‖1 - (t : ℂ) * (mE E * mE E)‖ := by
    have := (gapK_pos hκ hκ2).le
    have := norm_nonneg (1 - (t : ℂ) * (mE E * mE E))
    nlinarith
  cases s
  · have hc : (1 : ℂ) - (t : ℂ) * (mSigma E false * mSigma E false) =
        (starRingEnd ℂ) (1 - (t : ℂ) * (mE E * mE E)) := by
      simp [mSigma, map_sub, map_mul, Complex.conj_ofReal]
    rw [hc, Complex.norm_conj]
    exact hle
  · simpa [mSigma] using hle

/-- The factor `f(t) = (1 - tμ)⁻¹ - 1` is bounded by `c⁻¹`. -/
private theorem norm_edge_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) :
    ‖(1 - (t : ℂ) * μ)⁻¹ - 1‖ ≤ c⁻¹ := by
  have hne : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hct; linarith
  have h : (1 - (t : ℂ) * μ)⁻¹ - 1 = ((t : ℂ) * μ) * (1 - (t : ℂ) * μ)⁻¹ := by
    field_simp
    ring
  rw [h, norm_mul, norm_mul, hμ, Complex.norm_real, Real.norm_of_nonneg ht0, norm_inv, mul_one]
  have hinv : ‖1 - (t : ℂ) * μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hct
  have hc1 : 0 ≤ ‖1 - (t : ℂ) * μ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  nlinarith [ht1]

/-- The Lipschitz bound `|f(t) - f(1)| ≤ (1 - t) c⁻²`. -/
private theorem norm_edge_sub_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht1 : t ≤ 1)
    (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) (hc1 : c ≤ ‖1 - μ‖) :
    ‖((1 - (t : ℂ) * μ)⁻¹ - 1) - ((1 - μ)⁻¹ - 1)‖ ≤ (1 - t) * c⁻¹ ^ 2 := by
  have hne : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hct; linarith
  have hne1 : (1 : ℂ) - μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc1; linarith
  have h : ((1 - (t : ℂ) * μ)⁻¹ - 1) - ((1 - μ)⁻¹ - 1) =
      (((t - 1 : ℝ) : ℂ) * μ) * ((1 - (t : ℂ) * μ)⁻¹ * (1 - μ)⁻¹) := by
    field_simp
    push_cast
    ring
  rw [h, norm_mul, norm_mul, norm_mul, hμ, Complex.norm_real, norm_inv, norm_inv, mul_one,
    Real.norm_of_nonpos (by linarith), neg_sub]
  have hinv : ‖1 - (t : ℂ) * μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hct
  have hinv1 : ‖1 - μ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc hc1
  have h01 : 0 ≤ ‖1 - μ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hprod : ‖1 - (t : ℂ) * μ‖⁻¹ * ‖1 - μ‖⁻¹ ≤ c⁻¹ ^ 2 := by
    rw [sq]; exact mul_le_mul hinv hinv1 h01 (inv_nonneg.2 hc.le)
  exact mul_le_mul_of_nonneg_left hprod (by linarith)

/-- Telescoping bound for finite products:
`‖∏ a - ∏ b‖ ≤ |s| M^{|s|} δ` if `‖a_i‖, ‖b_i‖ ≤ M`, `‖a_i - b_i‖ ≤ δ`, `M ≥ 1`. -/
private theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℂ) {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ M) (hb : ∀ i ∈ s, ‖b i‖ ≤ M) (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ δ) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ s.card * M ^ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ M := fun i hi => ha i (mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ M := fun i hi => hb i (mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, ‖a i - b i‖ ≤ δ := fun i hi => hab i (mem_insert_of_mem hi)
    have hI := ih ha' hb' hab'
    have hax := ha x (mem_insert_self x s)
    have habx := hab x (mem_insert_self x s)
    have hQ : ‖∏ i ∈ s, b i‖ ≤ M ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖b i‖ ≤ ∏ _i ∈ s, M :=
            prod_le_prod₀ (fun i _ => norm_nonneg _) hb'
        _ = M ^ s.card := prod_const M
    rw [prod_insert hx, prod_insert hx, card_insert_of_notMem hx]
    have hsplit : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by ring
    rw [hsplit]
    have hMk : M ^ s.card ≤ M ^ s.card * M := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hM (Nat.le_succ _)
    have hM0 : 0 ≤ M := by linarith
    have hMk0 : 0 ≤ M ^ s.card := pow_nonneg hM0 _
    have hk0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    calc ‖a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i‖
        ≤ ‖a x‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ + ‖a x - b x‖ * ‖∏ i ∈ s, b i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ M * (s.card * M ^ s.card * δ) + δ * M ^ s.card := by
          gcongr
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * M ^ (s.card + 1) * δ := by
          push_cast
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left hMk hδ]

/-- A vertex `v` strictly inside the arc of `J` and not strictly inside the arc of any other
diagonal of `F` below `J`. -/
private def goodPt {n : ℕ} (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) (v : Fin n) :
    Prop :=
  J.1 < v ∧ v < J.2 ∧ ∀ e ∈ F, e ≠ J → KLArcLe e J → ¬(e.1 < v ∧ v < e.2)

private theorem exists_goodPt {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {J : Fin n × Fin n} (hJ : J ∈ F) : ∃ v, goodPt F J v := by
  have hJD := isDiag_of_mem_TSP hF hJ
  have hcf := crossingFree_of_mem_TSP hF
  obtain ⟨hJ12, hJadj, -⟩ := hJD
  rw [Fin.lt_def] at hJ12
  set S := F.filter (fun e => e.1 = J.1 ∧ e.2 < J.2) with hSdef
  rcases S.eq_empty_or_nonempty with hS | hS
  · have hlt : J.1.val + 1 < n := by have := J.2.isLt; omega
    refine ⟨⟨J.1.val + 1, hlt⟩, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; simp
    · rw [Fin.lt_def]; simp only; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      simp only at h1 h2
      have he1 : e.1 = J.1 := Fin.ext (by omega)
      have he2 : e.2 < J.2 := by
        rw [Fin.lt_def]
        rcases Nat.lt_or_ge e.2.val J.2.val with h | h
        · exact h
        · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
      have : e ∈ S := mem_filter.2 ⟨he, he1, he2⟩
      rw [hS] at this
      exact absurd this (notMem_empty e)
  · obtain ⟨e₀, he₀, hmax⟩ := S.exists_max_image (fun e => e.2.val) hS
    obtain ⟨he₀F, he₀1, he₀2⟩ := mem_filter.1 he₀
    have he₀D := (isDiag_of_mem_TSP hF he₀F).1
    rw [Fin.lt_def] at he₀D he₀2
    have he₀1' : e₀.1.val = J.1.val := congrArg Fin.val he₀1
    refine ⟨e₀.2, ?_, ?_, ?_⟩
    · rw [Fin.lt_def]; omega
    · rw [Fin.lt_def]; omega
    · rintro e he hne ⟨hle1, hle2⟩ ⟨h1, h2⟩
      rw [Fin.lt_def] at h1 h2
      rw [Fin.le_def] at hle1 hle2
      rcases Nat.lt_or_ge J.1.val e.1.val with h | h
      · apply hcf e₀ he₀F e he
        left
        refine ⟨?_, ?_, ?_⟩ <;> rw [Fin.lt_def] <;> omega
      · have he1 : e.1 = J.1 := Fin.ext (by omega)
        have he2 : e.2 < J.2 := by
          rw [Fin.lt_def]
          rcases Nat.lt_or_ge e.2.val J.2.val with h' | h'
          · exact h'
          · exact absurd (Prod.ext he1 (Fin.ext (by omega))) hne
        have : e.2.val ≤ e₀.2.val := hmax e (mem_filter.2 ⟨he, he1, he2⟩)
        omega

private theorem goodPt_inj {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n)
    {J J' : Fin n × Fin n} (hJ : J ∈ F) (hJ' : J' ∈ F) {v : Fin n}
    (hv : goodPt F J v) (hv' : goodPt F J' v) : J = J' := by
  by_contra hne
  have hcf := crossingFree_of_mem_TSP hF
  obtain ⟨a1, a2, a3⟩ := hv
  obtain ⟨b1, b2, b3⟩ := hv'
  by_cases h1 : KLArcLe J' J
  · exact a3 J' hJ' (Ne.symm hne) h1 ⟨b1, b2⟩
  by_cases h2 : KLArcLe J J'
  · exact b3 J hJ hne h2 ⟨a1, a2⟩
  simp only [KLArcLe, Fin.le_def, not_and_or, not_le] at h1 h2
  rw [Fin.lt_def] at a1 a2 b1 b2
  have hc1 := hcf J hJ J' hJ'
  have hc2 := hcf J' hJ' J hJ
  simp only [Crossing, Fin.lt_def, not_or, not_and_or, not_lt] at hc1 hc2
  omega

/-- A crossing-free set of diagonals of the `n`-gon has at most `n - 2` elements. -/
private theorem card_le_of_mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)} (hF : F ∈ TSP n) :
    F.card ≤ n - 2 := by
  classical
  let g : Fin n × Fin n → Fin n := fun J =>
    if h : ∃ v, goodPt F J v then Classical.choose h else J.1
  have hg : ∀ J ∈ F, goodPt F J (g J) := by
    intro J hJ
    have h := exists_goodPt hF hJ
    simp only [g, h, ↓reduceDIte]
    exact Classical.choose_spec h
  have hcard : (Finset.Ioo 0 (n - 1)).card = n - 2 := by
    rw [Nat.card_Ioo]; omega
  rw [← hcard]
  refine card_le_card_of_injOn (fun J => (g J).val) (fun J hJ => ?_) (fun J hJ J' hJ' h => ?_)
  · obtain ⟨h1, h2, -⟩ := hg J hJ
    rw [Fin.lt_def] at h1 h2
    have := J.2.isLt
    simp only [coe_Ioo, Set.mem_Ioo]
    omega
  · have hv : g J = g J' := Fin.ext h
    have g' := hg J' hJ'
    rw [← hv] at g'
    exact goodPt_inj hF hJ hJ' (hg J hJ) g'

/-- The number of trees: `#T_SP(σ,π) ≤ #T_SP(n) ≤ 2^{n²}`. -/
private theorem card_TSPlong_le (n : ℕ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    (KLTSPlong n σ π).card ≤ 2 ^ (n ^ 2) := by
  calc (KLTSPlong n σ π).card ≤ (TSP n).card := card_filter_le _ _
    _ ≤ (diagonals n).powerset.card := card_filter_le _ _
    _ = 2 ^ (diagonals n).card := card_powerset _
    _ ≤ 2 ^ (n ^ 2) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_univ _
          _ = n ^ 2 := by simp [sq]

end Estimates

/-! ## 7. The slice form for `σ^{(alt)}` and the sum-zero bound given `Q(1) = 0` -/

section SumZero

/-- `m(+) m(-) = |m|² = 1` in the bulk. -/
private theorem KLSumZero_mSigma_mul_not {E : ℝ} (hE : |E| ≤ 2) :
    mSigma E true * mSigma E false = 1 := by
  have h := norm_mE hE
  have h1 : mE E * (starRingEnd ℂ) (mE E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  simpa [mSigma] using h1

/-- For `n` even, `∏_i m(σ^{(alt)}_i) = (m(+) m(-))^{n/2} = 1`. -/
private theorem KLSumZero_prod_mSigma_alt {E : ℝ} (hE : |E| ≤ 2) {n : ℕ} (hev : Even n) :
    ∏ i : Fin n, mSigma E (KLsigAlt n i) = 1 := by
  have key : ∀ j : ℕ, ∏ k ∈ range (j + j), mSigma E (decide (k % 2 = 0)) = 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show j + 1 + (j + 1) = (j + j) + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
        one_mul]
      have h0 : (j + j) % 2 = 0 := by omega
      have h1 : ¬ (j + j + 1) % 2 = 0 := by omega
      simp only [h0, h1, decide_true, decide_false]
      exact KLSumZero_mSigma_mul_not hE
  obtain ⟨j, rfl⟩ := hev
  rw [← key j]
  exact Fin.prod_univ_eq_prod_range (fun k => mSigma E (decide (k % 2 = 0))) (j + j)

variable (d : ℕ) (g : ℝ)

/-- **The `d₁`-pinned form** under the hypotheses of the pin `SigmaPi_alt_sumZero_le`:
`∑_{δ : δ₀ = d₁} Σ^{(∅)}(t, σ^{(alt)}, δ) = Q(σ^{(alt)}, ∅)`, independent of `L` and `d₁`. -/
theorem SumZero_sum_slice_alt :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Zd d L,
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ ⟨0, by omega⟩ = d₁),
          KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ = Qlayer (mSigma E) t (KLsigAlt n) ∅ := by
  intro κ hκ L _ hL E hE t ht n _ hn hev d₁
  have hE2 : |E| ≤ 2 := by linarith
  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := fun s s' =>
    norm_mul_mSigma_lt_one hE2 ht.1 ht.2 s s'
  rw [SumZero_sum_slice d L g (mSigma E) hm hL (KLsigAlt n) ∅ ⟨0, by omega⟩ d₁,
    KLSumZero_prod_mSigma_alt hE2 hev, one_mul]

/-- The `L`-free Lipschitz bound: `‖Q(σ^{(alt)}, ∅)(t)‖ ≤ 2^{n²} n c_κ^{-n} (1 - t)` when
`Q(σ^{(alt)}, ∅)(1) = 0`. -/
private theorem norm_Qlayer_le {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 2 ≤ n) (σ : Fin n → Bool)
    (hQ1 : Qlayer (mSigma E) 1 σ ∅ = 0) :
    ‖Qlayer (mSigma E) t σ ∅‖ ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (1 - t) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hc := gapK_pos hκ hκ2
  set c := gapK κ with hcdef
  have hc1 : 1 ≤ c⁻¹ := one_le_inv₀ hc |>.2 (gapK_le_one κ)
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hμ : ∀ s : Bool, ‖mSigma E s * mSigma E s‖ = 1 := fun s => by
    rw [norm_mul, norm_mSigma hE2]; norm_num
  -- one tree
  have hF : ∀ F ∈ KLTSPlong n σ ∅,
      ‖∏ e ∈ F, edgeR (mSigma E) t (σ e.1) (σ e.2) - ∏ e ∈ F, edgeR (mSigma E) 1 (σ e.1) (σ e.2)‖
        ≤ n * c⁻¹ ^ n * (1 - t) := by
    intro F hFm
    obtain ⟨hFT, hFl⟩ := mem_filter.1 hFm
    have hsame : ∀ e ∈ F, σ e.2 = σ e.1 := by
      intro e he
      by_contra h
      have : e ∈ KLFlong F σ := mem_filter.2 ⟨he, Ne.symm h⟩
      rw [hFl] at this
      exact notMem_empty e this
    have hk := card_le_of_mem_TSP hFT
    have htel := norm_prod_sub_prod_le F (fun e => edgeR (mSigma E) t (σ e.1) (σ e.2))
      (fun e => edgeR (mSigma E) 1 (σ e.1) (σ e.2)) hc1 (by positivity : 0 ≤ (1 - t) * c⁻¹ ^ 2)
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact norm_edge_le (hμ _) ht.1 ht.2.le hc (gapK_le_norm hκ hE ht.1 _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact norm_edge_le (hμ _) zero_le_one le_rfl hc (gapK_le_norm hκ hE zero_le_one _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        have h1 := gapK_le_norm hκ hE zero_le_one (σ e.1)
        rw [Complex.ofReal_one, one_mul] at h1 ⊢
        exact norm_edge_sub_le (hμ _) ht.2.le hc (gapK_le_norm hκ hE ht.1 _) h1)
    refine htel.trans ?_
    have hkn : (F.card : ℝ) ≤ n := by
      have : F.card ≤ n := by omega
      exact_mod_cast this
    have hpow : c⁻¹ ^ F.card * c⁻¹ ^ 2 ≤ c⁻¹ ^ n := by
      rw [← pow_add]; exact pow_le_pow_right₀ hc1 (by omega)
    have hp0 : 0 ≤ c⁻¹ ^ F.card * c⁻¹ ^ 2 := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc (F.card : ℝ) * c⁻¹ ^ F.card * ((1 - t) * c⁻¹ ^ 2)
        = (F.card : ℝ) * (c⁻¹ ^ F.card * c⁻¹ ^ 2) * (1 - t) := by ring
      _ ≤ n * c⁻¹ ^ n * (1 - t) := by gcongr
  have hdiff : Qlayer (mSigma E) t σ ∅ = ∑ F ∈ KLTSPlong n σ ∅,
      (∏ e ∈ F, edgeR (mSigma E) t (σ e.1) (σ e.2) - ∏ e ∈ F, edgeR (mSigma E) 1 (σ e.1) (σ e.2)) := by
    rw [sum_sub_distrib]
    have : Qlayer (mSigma E) 1 σ ∅ = ∑ F ∈ KLTSPlong n σ ∅,
        ∏ e ∈ F, edgeR (mSigma E) 1 (σ e.1) (σ e.2) := rfl
    rw [← this, hQ1, sub_zero]
    rfl
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum hF).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard : ((KLTSPlong n σ ∅).card : ℝ) ≤ 2 ^ (n ^ 2) := by
    exact_mod_cast card_TSPlong_le n σ ∅
  have h0 : 0 ≤ (n : ℝ) * c⁻¹ ^ n * (1 - t) := by positivity
  calc ((KLTSPlong n σ ∅).card : ℝ) * (n * c⁻¹ ^ n * (1 - t))
      ≤ 2 ^ (n ^ 2) * (n * c⁻¹ ^ n * (1 - t)) := mul_le_mul_of_nonneg_right hcard h0
    _ = 2 ^ (n ^ 2) * n * c⁻¹ ^ n * (1 - t) := by ring

/-- `1 - t = η_t / Im m ≤ (2 / √(κ(4-κ))) η_t` in the bulk `|E| ≤ 2 - κ`. -/
private theorem one_sub_le_etaT {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht1 : t ≤ 1) :
    1 - t ≤ (2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have hq : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have hq0 : 0 < κ * (4 - κ) := by nlinarith
  have hsq0 : 0 < Real.sqrt (κ * (4 - κ)) := Real.sqrt_pos.2 hq0
  have hsq : Real.sqrt (κ * (4 - κ)) ≤ Real.sqrt (4 - E ^ 2) := Real.sqrt_le_sqrt hq
  rw [Gauss.etaT, mE_im]
  have h : 2 / Real.sqrt (κ * (4 - κ)) * ((1 - t) * (Real.sqrt (4 - E ^ 2) / 2)) =
      (1 - t) * (Real.sqrt (4 - E ^ 2) / Real.sqrt (κ * (4 - κ))) := by
    field_simp
  rw [h]
  have h1 : 1 ≤ Real.sqrt (4 - E ^ 2) / Real.sqrt (κ * (4 - κ)) := (one_le_div hsq0).2 hsq
  nlinarith

/-- **The sum-zero bound given `Q(1) = 0`** (conditional adapter for the signed sum-zero estimate
`(eq:Sigma-empty-sum-zero)`, first part; its extra hypothesis `Q(σ^{(alt)}, ∅)|_{t=1} = 0` is the
subject of the `SumZeroWard` port, ticket KL7c): the body of the pin with the hypothesis
`Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0` after `Even n`.  The constant is explicit and the bulk
`|E| ≤ 2 - κ` is assumed, as in RBM2D (paper-delta T2004a-11 of RBM2D, quoted in its
`docs/reports/T2028-prove.md:199`). -/
theorem SigmaPi_alt_sumZero_le_of_Qlayer_one :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n →
      Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0 → ∀ d₁ : Zd d L,
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ ⟨0, by omega⟩ = d₁),
          KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ‖
        ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t := by
  intro κ hκ L _ hL E hE t ht n _ hn hev hQ1 d₁
  rw [SumZero_sum_slice_alt d g κ hκ L hL E hE t ht n hn hev d₁]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hQ := norm_Qlayer_le hκ hE ht (by omega) (KLsigAlt n) hQ1
  have hη := one_sub_le_etaT hκ hE ht.2.le
  have hc := gapK_pos hκ hκ2
  have hA : 0 ≤ (2 : ℝ) ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n := by positivity
  calc ‖Qlayer (mSigma E) t (KLsigAlt n) ∅‖
      ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (1 - t) := hQ
    _ ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * ((2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t) :=
        mul_le_mul_of_nonneg_left hη hA
    _ = 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t := by
        ring

end SumZero

/-! ## 8. The instances: `d = 3`, `L = 3`, `n = 4`, `E = 0`, `t = 1/2`, `κ = 1`, `g = 1/2`

`L = 3` has `27` sites, `m(+) = i`, `m(-) = -i`, `σ = σ^{(alt)} = (+,-,+,-)`; RBM2D's Checks 1-2 in
`d = 3`, and one instance of every other public statement of the file.  At this data
`T_SP(σ^{(alt)}, ∅) = {∅, {(0,2)}, {(1,3)}}`, `Q(σ^{(alt)}, ∅)(t) = 1 + 2((1+t)⁻¹ - 1)`, which is
`1/3` at `t = 1/2` and `0` at `t = 1`. -/

section Instances

private theorem chk_mE_zero : mE 0 = Complex.I := by
  simp only [mE]
  have h : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]; push_cast; simp

private theorem chk_m_true : mSigma 0 true = Complex.I := by
  simp [mSigma, chk_mE_zero]

private theorem chk_m_false : mSigma 0 false = -Complex.I := by
  simp [mSigma, chk_mE_zero]

private theorem chk_mSigma_sq (s : Bool) : mSigma 0 s * mSigma 0 s = -1 := by
  cases s <;> simp [chk_m_true, chk_m_false]

/-- The hypothesis `‖t m m'‖ < 1` at `E = 0`, `t = 1/2`. -/
private theorem chk_hm (s s' : Bool) : ‖((1 / 2 : ℝ) : ℂ) * (mSigma 0 s * mSigma 0 s')‖ < 1 :=
  norm_mul_mSigma_lt_one (by norm_num) (by norm_num) (by norm_num) s s'

/-- `T_SP(σ^{(alt)}, ∅)` for `n = 4`: both diagonals join equal signs. -/
private theorem chk_TSPlong_four : KLTSPlong 4 (KLsigAlt 4) ∅ = {∅, {(0, 2)}, {(1, 3)}} := by
  decide

/-- `Q(σ^{(alt)}, ∅)(t) = 1 + 2((1 + t)⁻¹ - 1)` at `n = 4`, `E = 0`. -/
private theorem chk_Qlayer (t : ℝ) :
    Qlayer (mSigma 0) t (KLsigAlt 4) ∅ = 1 + 2 * ((1 + (t : ℂ))⁻¹ - 1) := by
  rw [Qlayer, chk_TSPlong_four, sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have h0 : KLsigAlt 4 0 = true := rfl
  have h1 : KLsigAlt 4 1 = false := rfl
  have h2 : KLsigAlt 4 2 = true := rfl
  have h3 : KLsigAlt 4 3 = false := rfl
  simp only [prod_empty, prod_singleton, edgeR, h0, h1, h2, h3, chk_mSigma_sq]
  ring

/-- `Q(σ^{(alt)}, ∅)(1) = 1 - 1/2 - 1/2 = 0` at `n = 4`, `E = 0`: the extra hypothesis of
`SigmaPi_alt_sumZero_le_of_Qlayer_one` holds at the instance, so the instance is not vacuous. -/
theorem KLSumZero_inst_Qlayer_one : Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅ = 0 := by
  rw [chk_Qlayer]
  norm_num

/-- `∏_i m(σ^{(alt)}_i) = 1` at `n = 4`, `E = 0`. -/
private theorem chk_prod_m : ∏ i : Fin 4, mSigma 0 (KLsigAlt 4 i) = 1 :=
  KLSumZero_prod_mSigma_alt (by norm_num) (by decide)

/-- **Instance of `SumZero_sum_slice_alt`** (RBM2D's Check 1 in `d = 3`): the `d₁`-pinned form at
`L = 3`, `n = 4`, `E = 0`, `t = 1/2` has the value `1/3` for every `d₁`. -/
theorem KLSumZero_inst_slice_alt (d₁ : Zd 3 3) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
      KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ = 1 / 3 := by
  rw [SumZero_sum_slice_alt 3 (1 / 2) 1 one_pos 3 le_rfl 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 le_rfl (by decide) d₁, chk_Qlayer]
  norm_num

/-- **Instance of `SigmaPi_alt_sumZero_le_of_Qlayer_one`** (RBM2D's Check 2 in `d = 3`), with its
extra hypothesis discharged by `KLSumZero_inst_Qlayer_one`. -/
theorem KLSumZero_inst_bound (d₁ : Zd 3 3) :
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
        KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ‖
      ≤ 2 ^ (4 ^ 2) * ((4 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 4 * (2 / Real.sqrt (1 * (4 - 1)))
          * Gauss.etaT 0 (1 / 2) :=
  SigmaPi_alt_sumZero_le_of_Qlayer_one 3 (1 / 2) 1 one_pos 3 le_rfl 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 le_rfl (by decide) KLSumZero_inst_Qlayer_one d₁

/-- **Instance of `SumZero_sum_slice`** at every slice `δ_i = x` of the same data: the value is
`(∏_j m(σ_j)) · Q(σ,π) = 1/3`. -/
theorem KLSumZero_inst_slice (i : Fin 4) (x : Zd 3 3) :
    ∑ δ ∈ univ.filter (fun δ : Fin 4 → Zd 3 3 => δ i = x),
      KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ = 1 / 3 := by
  rw [SumZero_sum_slice 3 3 (1 / 2) (mSigma 0) chk_hm le_rfl (KLsigAlt 4) ∅ i x, chk_prod_m,
    chk_Qlayer]
  norm_num

/-- **Instance of `sum_SigmaPi`**: `∑_δ Σ^{(∅)} = L^d (∏ m) Q = 27 · 1/3 = 9`. -/
theorem KLSumZero_inst_sum_SigmaPi :
    ∑ δ : Fin 4 → Zd 3 3, KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ = 9 := by
  rw [sum_SigmaPi 3 3 (1 / 2) (mSigma 0) chk_hm le_rfl (KLsigAlt 4) ∅, chk_prod_m, chk_Qlayer]
  norm_num

/-- **Instance of `SumZero_sum_Kpi_eq`**. -/
theorem KLSumZero_inst_Kpi_eq :
    ∑ a : Fin 4 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) a ∅ =
      (∏ v : Fin 4, (1 - ((1 / 2 : ℝ) : ℂ) *
          (mSigma 0 (KLsigAlt 4 v) * mSigma 0 (KLsigAlt 4 (v + 1))))⁻¹) *
        ∑ δ : Fin 4 → Zd 3 3, KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ :=
  SumZero_sum_Kpi_eq 3 3 (1 / 2) (mSigma 0) chk_hm le_rfl (KLsigAlt 4) ∅

/-- **Instance of `sum_Kpi_closed`**: `∑_a K^{(∅)}(1/2, σ^{(alt)}, a) = L^d A(σ^{(alt)}, ∅)`, with
`A(σ^{(alt)}, ∅)` unevaluated. -/
theorem KLSumZero_inst_Kpi_closed :
    ∑ a : Fin 4 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) a ∅ =
      (3 : ℂ) ^ 3 * Alayer (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ := by
  have h := sum_Kpi_closed 3 3 (1 / 2) (mSigma 0) chk_hm le_rfl (KLsigAlt 4) ∅
  rwa [Nat.cast_ofNat] at h

/-- `A(σ^{(alt)}, ∅) = 1 · 2⁴ · 1/3 = 16/3` at `E = 0`, `t = 1/2`. -/
private theorem chk_Alayer : Alayer (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ = 16 / 3 := by
  have h0 : KLsigAlt 4 0 = true := rfl
  have h1 : KLsigAlt 4 1 = false := rfl
  have h2 : KLsigAlt 4 2 = true := rfl
  have h3 : KLsigAlt 4 3 = false := rfl
  have e01 : ((0 : Fin 4) + 1) = 1 := rfl
  have e12 : ((1 : Fin 4) + 1) = 2 := rfl
  have e23 : ((2 : Fin 4) + 1) = 3 := rfl
  have e30 : ((3 : Fin 4) + 1) = 0 := rfl
  rw [Alayer, chk_prod_m, chk_Qlayer, Fin.prod_univ_four]
  simp only [e01, e12, e23, e30, h0, h1, h2, h3, chk_m_true, chk_m_false]
  norm_num [Complex.ext_iff]

/-- **Instance of `sum_Kpi_closed`, evaluated**: the sum of `K^{(∅)}(1/2, σ^{(alt)}, a)` over the
`27⁴` labels is `27 · 16/3 = 144`. -/
theorem KLSumZero_inst_Kpi_closed_val :
    ∑ a : Fin 4 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) a ∅ = 144 := by
  rw [KLSumZero_inst_Kpi_closed, chk_Alayer]
  norm_num

/-- `T_SP(+,+,+, ∅) = {∅}`: the triangle has no diagonal. -/
private theorem chk_TSPlong_three : KLTSPlong 3 (fun _ : Fin 3 => true) ∅ = {∅} := by
  decide

private theorem chk_Qlayer_pure : Qlayer (mSigma 0) (1 / 2) (fun _ : Fin 3 => true) ∅ = 1 := by
  rw [Qlayer, chk_TSPlong_three]
  simp

/-- **Instance of `sum_Kpi_closed` where `∏_i m(σ_i) ≠ 1`**: the pure triangle `σ = (+,+,+)`,
`∏_i m(σ_i) = i³ = -i`, `A(σ, ∅) = -i · (2/3)³ · 1`, so `∑_a K^{(∅)} = 27 · A = -8i`. -/
theorem KLSumZero_inst_Kpi_closed_pure :
    ∑ a : Fin 3 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (fun _ : Fin 3 => true) a ∅ =
      -8 * Complex.I := by
  rw [sum_Kpi_closed 3 3 (1 / 2) (mSigma 0) chk_hm le_rfl (fun _ : Fin 3 => true) ∅, Alayer,
    chk_Qlayer_pure, Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [chk_m_true, Nat.cast_ofNat]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h : (1 - ((1 / 2 : ℝ) : ℂ) * (Complex.I * Complex.I))⁻¹ = 2 / 3 := by
    rw [hI]; push_cast; norm_num
  rw [h]
  have h3 : Complex.I * Complex.I * Complex.I = -Complex.I := by rw [hI]; ring
  rw [h3]
  ring

/-- **The RBM2D form of the closed form is false for the merged `KLKpi`** (the reason for the factor
`∏_i m(σ_i)` in `Alayer`): at the pure triangle, `∑_a K^{(∅)} = -8i`, while
`L^d ∏_v (1 - ξ_v)⁻¹ Q = 8`. -/
theorem KLSumZero_neg_Kpi_closed_2Dform :
    ∑ a : Fin 3 → Zd 3 3, KLKpi 3 3 (1 / 2) (mSigma 0) (1 / 2) (fun _ : Fin 3 => true) a ∅ ≠
      (3 : ℂ) ^ 3 * ((∏ _v : Fin 3, (1 - ((1 / 2 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 true))⁻¹) *
        Qlayer (mSigma 0) (1 / 2) (fun _ : Fin 3 => true) ∅) := by
  rw [KLSumZero_inst_Kpi_closed_pure, chk_Qlayer_pure, Fin.prod_univ_three, chk_m_true]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h : (1 - ((1 / 2 : ℝ) : ℂ) * (Complex.I * Complex.I))⁻¹ = 2 / 3 := by
    rw [hI]; push_cast; norm_num
  rw [h]
  intro hne
  have := congrArg Complex.re hne
  norm_num at this

/-- **Instance of `SumZero_SigmaPi_add_const`** (translation invariance) at every `δ`, `c`. -/
theorem KLSumZero_inst_add_const (δ : Fin 4 → Zd 3 3) (c : Zd 3 3) :
    KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ (fun v => δ v + c) =
      KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ :=
  SumZero_SigmaPi_add_const 3 3 (1 / 2) (mSigma 0) chk_hm le_rfl (KLsigAlt 4) ∅ δ c

/-- The instance tree `F = {(0,2)}` of the quadrilateral (a member of `T_SP(4)`). -/
def KLSumZero_instF : Finset (Fin 4 × Fin 4) := {(0, 2)}

theorem KLSumZero_instF_mem : KLSumZero_instF ∈ TSP 4 := by decide

/-- The internal edge weights `Θ^{(σ_i,σ_j)}_t - 1` of the instance tree at the instance data. -/
noncomputable def KLSumZero_instE : ↥KLSumZero_instF → Matrix (Zd 3 3) (Zd 3 3) ℂ :=
  fun J => thetaEdge 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4 J.1.1) (KLsigAlt 4 J.1.2) - 1

/-- Their column sums `(1 - ξ_e)⁻¹ - 1`. -/
noncomputable def KLSumZero_instr : ↥KLSumZero_instF → ℂ :=
  fun J => edgeR (mSigma 0) (1 / 2) (KLsigAlt 4 J.1.1) (KLsigAlt 4 J.1.2)

/-- The column-sum hypothesis of `treeZ_peel`, `treeZ_eq` at the instance data (discharged by
`sum_Theta_sub_one_col`). -/
theorem KLSumZero_inst_col (J : ↥KLSumZero_instF) (y : Zd 3 3) :
    ∑ x, KLSumZero_instE J x y = KLSumZero_instr J :=
  sum_Theta_sub_one_col (by norm_num) (chk_hm _ _) y

/-- **Instance of `treeZ_peel`** at the instance tree, for every set `G` of its edges. -/
theorem KLSumZero_inst_treeZ_peel (G : Finset ↥KLSumZero_instF) :
    ((3 : ℂ) ^ 3) ^ G.card * ∑ b : ↥(KLnodes KLSumZero_instF) → Zd 3 3,
        ∏ J ∈ G, KLSumZero_instE J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩)
          (b ⟨KLnodePar KLSumZero_instF J, KLnodePar_mem KLSumZero_instF J⟩) =
      (∏ J ∈ G, KLSumZero_instr J) * ∑ _b : ↥(KLnodes KLSumZero_instF) → Zd 3 3, (1 : ℂ) := by
  have h := treeZ_peel (d := 3) (L := 3) KLSumZero_instF_mem KLSumZero_instE KLSumZero_instr
    KLSumZero_inst_col G
  rwa [Nat.cast_ofNat] at h

/-- **Instance of `treeZ_eq`** at the instance tree: `∑_b ∏_e (Θ - 1) = L^d ∏_e ((1 - ξ_e)⁻¹ - 1)`. -/
theorem KLSumZero_inst_treeZ_eq :
    treeZ KLSumZero_instF KLSumZero_instE = (3 : ℂ) ^ 3 * ∏ J, KLSumZero_instr J := by
  have h := treeZ_eq (d := 3) (L := 3) KLSumZero_instF_mem KLSumZero_instE KLSumZero_instr
    KLSumZero_inst_col
  rwa [Nat.cast_ofNat] at h

/-- **Instance of `sum_selfW`** at the instance tree. -/
theorem KLSumZero_inst_sum_selfW :
    ∑ δ : Fin 4 → Zd 3 3, KLselfW 3 3 KLSumZero_instF KLSumZero_instE δ =
      treeZ KLSumZero_instF KLSumZero_instE :=
  sum_selfW _ _

/-- **Instance of the column and row sums** of `Θ_ξ - 1` at `ξ = 1/2`: `(1 - ξ)⁻¹ - 1 = 1`. -/
theorem KLSumZero_inst_Theta_sums (x : Zd 3 3) :
    ∑ y : Zd 3 3, Theta 3 3 (1 / 2) ((1 / 2 : ℝ) : ℂ) y x = (1 - ((1 / 2 : ℝ) : ℂ))⁻¹ ∧
    ∑ y : Zd 3 3, (Theta 3 3 (1 / 2) ((1 / 2 : ℝ) : ℂ) - 1) y x =
      (1 - ((1 / 2 : ℝ) : ℂ))⁻¹ - 1 ∧
    ∑ y : Zd 3 3, (Theta 3 3 (1 / 2) ((1 / 2 : ℝ) : ℂ) - 1) x y =
      (1 - ((1 / 2 : ℝ) : ℂ))⁻¹ - 1 := by
  have hξ : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real]; norm_num
  exact ⟨SumZero_sum_Theta_col (by norm_num) hξ x, sum_Theta_sub_one_col (by norm_num) hξ x,
    sum_Theta_sub_one_row (by norm_num) hξ x⟩

/-- **Instance of `gapK_le_norm`** (F3): `c_κ = 1 ≤ |1 - t m(+)²| = 3/2` at `κ = 1`, `E = 0`,
`t = 1/2`. -/
theorem KLSumZero_inst_gap :
    gapK 1 ≤ ‖1 - (((1 / 2 : ℝ)) : ℂ) * (mSigma 0 true * mSigma 0 true)‖ :=
  gapK_le_norm one_pos (by norm_num) (by norm_num) true

/-- **Instance of `sum_out`**: `ι = Fin 2`, `Z = Fin 3`, `i = 0`, `f(b) = b₁`, `G(y, b) = 1(y = b₁)`
(independent of the coordinate `0`, with `∑_y G(y, b) = 1`): `3 ∑_b b₁ 1(b₀ = b₁) = ∑_b b₁`. -/
theorem KLSumZero_inst_sum_out :
    (Fintype.card (Fin 3) : ℂ) * ∑ b : Fin 2 → Fin 3,
        ((b 1 : Fin 3).val : ℂ) * (if b 0 = b 1 then 1 else 0) =
      1 * ∑ b : Fin 2 → Fin 3, ((b 1 : Fin 3).val : ℂ) := by
  exact sum_out (0 : Fin 2) (fun b : Fin 2 → Fin 3 => ((b 1 : Fin 3).val : ℂ))
    (fun y b => if y = b 1 then 1 else 0) 1
    (fun b x => by simp)
    (fun b x y => by simp)
    (fun b => by simp)

end Instances

end RBM.Loop
