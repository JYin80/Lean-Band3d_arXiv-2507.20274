/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KCactusCut
import RBM3D.BA.KTreeRep
import RBM3D.Loop.KLSumZeroWard
import RBM3D.Loop.KLIndStepB

/-!
# Stage K, row K06: the BA molecule layer `K^{(π)}`, `Σ^{(π)}`, `(eq_K-Kpi)`, the factorisation

Ticket T2376 (design BA-DK, `docs/reports/T2360-design.md` §4 row K06; supervisor
`docs/supervisor/2026-10-09-2051.md` K-a…K-e and `2026-10-10-0350.md` C2; Amend 1 of DECISIONS
§190: the cut machinery is in `BA/KCactusCut.lean`).  Paper: `(eq:defKpi)`, `(eq_K-Kpi)`,
`(eq:molecule-Kpi)` (`A_deterministic_estimates.tex:600-640`).  The BA twin of the band layer
`Loop/KLTree.lean` §4-§5 and of the factorisation at an innermost long edge
`Loop/KLSumZeroWard.lean` §1-§3, over the cactus `BAGamma` (K04) and the BA solution `BAKsol`
(K05b: `baTreeRep`).

1. `BAKpi`, `BASigmaTree`, `BASigmaPi`, `BASig`: `K^{(π)}` is the sum of the cactus values over the
   trees whose long chords are `π`; the self-energy `Σ^{(π)}` is the same sum with every leaf edge
   `Θ^{(σ_v,σ_{v+1})}(a_v, ·)` replaced by the indicator of `δ_v` at its slot.  Neither carries
   `∏ m(σ_i)` nor a power of `W` (as `BATreeRep`).
2. `baK_eq_sum_Kpi` (`(eq_K-Kpi)`) from `baTreeRep`; `baKpi_eq_sum_SigmaPi`, the first stage of
   `(eq:molecule-Kpi)`.
3. `baSigmaPi_shift`, `baSigmaPi_reflect`, `baSig_transl`: the first two conjuncts of
   `SigSumZeroAbs` (a reflection and a translation of `δ`) at the molecule weight `BASig`.
4. `baSigmaPi_cut`: the factorisation at an innermost long edge (`(eq:molecule-Kpi)` by induction
   on `π`): `Σ^{(π)}` is the outer self-energy glued through the chord `tΘ^{(σ_i,σ_j)}` to the inner
   self-energy `Σ^{(∅)}`; `Flong_eq_iff_cut`, `KLsum_cut` and `baCactus_cut`.  No `W`, no
   hypothesis on `M` or `t`; the chord is oriented `u` (inner end) to `w` (outer end), and the
   reversed inner leaf `Θ^{(σ_j,σ_i)} = (Θ^{(σ_i,σ_j)})ᵀ` is `1ᵀ = 1` at the self-energy level
   (C2: no symmetry of `M` is used).
5. Compiled instances at the flow point `P` of `(d, L) = (3, 4)`, `n = 4`.

Public: the definitions and theorems above; every other helper is `private` with the stem
`KMolecule_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. The definitions -/

/-- **`K^{(π)}`** (`(eq:defKpi)`): the sum of the cactus values over the trees whose long chords are
exactly `π`.  The BA `Γ` carries no `∏ m(σ_i)` (as `BATreeRep`). -/
noncomputable def BAKpi (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) (a : Fin n → Zd d L) (π : Finset (Fin n × Fin n)) : ℂ :=
  ∑ F ∈ KLTSPlong n σ π, BAGamma d L n M t F σ a

/-- **The self-energy of one tree**: the cactus value with every leaf edge removed, the leaf weight
`Θ^{(σ_v,σ_{v+1})}(a_v, ·)` replaced by the indicator of `δ_v` at the leaf's slot (the generic
value `KLgval` with the leaf weights `1`). -/
noncomputable def BASigmaTree (d L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (δ : Fin n → Zd d L) : ℂ :=
  KLgval d L (Nd := BAslot F) (Lf := Fin n) δ (fun _ => 1) (BAslotLeaf F)
    (BACactusValEdgeW M t F σ) (BACactusValSrc F) (BACactusValTgt F)

/-- **`Σ^{(π)}`**, the BA self-energy (first stage of `(eq:molecule-Kpi)`): `BASigmaTree` summed over the
trees whose long chords are exactly `π`. -/
noncomputable def BASigmaPi (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) : ℂ :=
  ∑ F ∈ KLTSPlong n σ π, BASigmaTree d L M t F σ δ

/-- **The molecule weight as an interface family**: `Σ^{(∅)}` at the BA data `M(σ) = BAMsigma (BAMB ..)`,
indexed by `i : ι` so that it has the type `Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ` of
`SigSumZeroAbs` (`Loop/KLIndStepA.lean:1036`) and `IndStepAbs` (`Loop/KLIndStepB.lean:77`). -/
noncomputable def BASig {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)]
    (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (i : ι) (σ : Fin n → Bool) (δ : Fin n → Zd d (L i)) : ℂ :=
  BASigmaPi d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ ∅ δ

/-! ## 2. The first stage and `(eq_K-Kpi)` -/

section FirstStage

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- Re-attaching the leaf edges to the self-energy gives back the tree value: the generic value with
leaf weights `Lw` is `Σ_δ (value with leaf weights 1 at δ) ∏_ℓ Lw_ℓ(a_ℓ, δ_ℓ)` (the twin of
`KLtreeValW_eq_sum_selfW`, `Loop/KLTree.lean:403`). -/
private theorem KMolecule_gval_eq_sum {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf]
    [DecidableEq Lf] [Fintype Ed] (a : Lf → Zd d L) (Lw : Lf → Matrix (Zd d L) (Zd d L) ℂ) (p : Lf → Nd)
    (E : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → Nd) :
    KLgval d L a Lw p E c q = ∑ δ : Lf → Zd d L, KLgval d L δ (fun _ => 1) p E c q * ∏ ℓ, Lw ℓ (a ℓ) (δ ℓ) := by
  simp only [KLgval, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : ∀ δ : Lf → Zd d L, (∏ ℓ, (1 : Matrix (Zd d L) (Zd d L) ℂ) (δ ℓ) (b (p ℓ))) *
      (∏ e, E e (b (c e)) (b (q e))) * ∏ ℓ, Lw ℓ (a ℓ) (δ ℓ) =
      (∏ e, E e (b (c e)) (b (q e))) * ∏ ℓ, ((1 : Matrix (Zd d L) (Zd d L) ℂ) (δ ℓ) (b (p ℓ)) * Lw ℓ (a ℓ) (δ ℓ)) := by
    intro δ
    rw [mul_comm (∏ ℓ, (1 : Matrix (Zd d L) (Zd d L) ℂ) (δ ℓ) (b (p ℓ))), mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [h, ← Finset.mul_sum]
  rw [mul_comm]
  congr 1
  have := (Finset.prod_univ_sum (fun _ : Lf => (Finset.univ : Finset (Zd d L)))
    (fun ℓ x => (1 : Matrix (Zd d L) (Zd d L) ℂ) x (b (p ℓ)) * Lw ℓ (a ℓ) x)).symm
  rw [Fintype.piFinset_univ] at this
  rw [this]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  simp [Matrix.one_apply]

/-- **The first stage of `(eq:molecule-Kpi)`**: `K^{(π)}(t,σ,a) = Σ_δ Σ^{(π)}(t,σ,δ) ∏_v Θ^{(σ_v,σ_{v+1})}(a_v, δ_v)`. -/
theorem baKpi_eq_sum_SigmaPi (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) (π : Finset (Fin n × Fin n)) :
    BAKpi d L n M t σ a π = ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ π δ *
      ∏ v, BAThetaOf M t (σ v) (σ (v + 1)) (a v) (δ v) := by
  simp only [BAKpi, BASigmaPi, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  exact KMolecule_gval_eq_sum a (BACactusValLeafW M t σ) (BAslotLeaf F) (BACactusValEdgeW M t F σ)
    (BACactusValSrc F) (BACactusValTgt F)

omit [NeZero n] in
/-- The layers `KLTSPlong n σ π`, `π ⊆ diagonals n`, partition `TSP n` (a copy of the private
`KLsum_TSPlong`, `Loop/KLTree.lean:381`). -/
private theorem KMolecule_sum_TSPlong {M : Type*} [AddCommMonoid M] (σ : Fin n → Bool)
    (f : Finset (Fin n × Fin n) → M) :
    ∑ π ∈ (diagonals n).powerset, ∑ F ∈ KLTSPlong n σ π, f F = ∑ F ∈ TSP n, f F := by
  refine Finset.sum_fiberwise_of_maps_to (fun F hF => ?_) f
  rw [Finset.mem_powerset]
  have hF' := (Finset.mem_filter.1 hF).1
  exact (Finset.filter_subset _ _).trans (Finset.mem_powerset.1 hF')

/-- **`(eq_K-Kpi)`**: `𝒦^{(n)}_{t,σ,a} = W^{-d(n-1)} Σ_{π ⊂ Z_n^{off}} K^{(π)}(t,σ,a)`, `n ≥ 3`, for the block
Anderson solution `BAKsol` (`baTreeRep` at `Λ = g`, and the fibres of `F ↦ F_long(F, σ)`). -/
theorem baK_eq_sum_Kpi (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ)
    {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) =
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
        ∑ π ∈ (diagonals n).powerset, BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π := by
  rw [baTreeRep d g κ hg hκ L hL W g hg le_rfl E m hr t ht n hn σ a]
  simp only [BAKpi]
  rw [KMolecule_sum_TSPlong σ (fun F => BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a)]

end FirstStage

/-! ## 3. The translation clauses -/

section Clauses

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- The generic value with the leaf weights `1` is invariant under a permutation `e` of the labels when `e`
fixes every edge weight (`Σ_b` is reindexed by `b ↦ e ∘ b`). -/
private theorem KMolecule_gval_perm {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf] [Fintype Ed]
    (e : Zd d L ≃ Zd d L) (a : Lf → Zd d L) (p : Lf → Nd) (E : Ed → Matrix (Zd d L) (Zd d L) ℂ)
    (c q : Ed → Nd) (hE : ∀ ε x y, E ε (e x) (e y) = E ε x y) :
    KLgval d L (fun ℓ => e (a ℓ)) (fun _ => 1) p E c q = KLgval d L a (fun _ => 1) p E c q := by
  unfold KLgval
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ : Nd => e) _ _ fun b => ?_).symm
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [Matrix.one_apply, e.injective.eq_iff]
  · exact Finset.prod_congr rfl fun ε _ => (hE ε _ _).symm

/-- `Θ^{(s,s')} = (1 - t M^{(s,s')})⁻¹` is invariant under a permutation `e` of the labels fixing every `M(σ)`
(the conjugation of `Ring.inverse` by a permutation matrix, `Matrix.inv_submatrix_equiv`; no invertibility). -/
private theorem KMolecule_theta_perm (e : Zd d L ≃ Zd d L) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ σ x y, M σ (e x) (e y) = M σ x y) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BAThetaOf M t s s' (e x) (e y) = BAThetaOf M t s s' x y := by
  have hQ : ∀ x y, BAMssOf M s s' (e x) (e y) = BAMssOf M s s' x y := fun x y => by
    simp only [BAMssOf, Matrix.of_apply, hM]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s').submatrix e e =
      1 - (t : ℂ) • BAMssOf M s s' := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQ]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s') e e
  rw [hA] at h2
  unfold BAThetaOf PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- Every edge weight of the cactus is invariant under a permutation `e` of the labels fixing every `M(σ)`. -/
private theorem KMolecule_edge_perm (e : Zd d L ≃ Zd d L) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ σ x y, M σ (e x) (e y) = M σ x y) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) :
    ∀ (ε : ↥F ⊕ BAslot F) (x y : Zd d L),
      BACactusValEdgeW M t F σ ε (e x) (e y) = BACactusValEdgeW M t F σ ε x y := by
  rintro (J | s) x y
  · change ((t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) (e x) (e y) =
      ((t : ℂ) • BAThetaOf M t (σ J.1.1) (σ J.1.2)) x y
    simp only [Matrix.smul_apply, KMolecule_theta_perm e M hM]
  · exact hM _ x y

/-- `Σ^{(π)}` is invariant under a permutation `e` of the labels fixing every `M(σ)`. -/
private theorem KMolecule_sigmaPi_perm (e : Zd d L ≃ Zd d L) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ σ x y, M σ (e x) (e y) = M σ x y) (t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (δ : Fin n → Zd d L) : BASigmaPi d L n M t σ π (fun j => e (δ j)) = BASigmaPi d L n M t σ π δ :=
  Finset.sum_congr rfl fun F _ =>
    KMolecule_gval_perm e δ (BAslotLeaf F) _ _ _ (KMolecule_edge_perm e M hM t F σ)

/-- **Translation invariance of `Σ^{(π)}`** (the second clause of `SigSumZeroAbs`): `Σ^{(π)}(δ + c) = Σ^{(π)}(δ)`
when every `M(σ)` is translation invariant. -/
theorem baSigmaPi_shift (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) (c : Zd d L) :
    BASigmaPi d L n M t σ π (fun j => δ j + c) = BASigmaPi d L n M t σ π δ :=
  KMolecule_sigmaPi_perm (Equiv.addRight c) M (fun σ x y => hshift σ x y c) t σ π δ

omit [NeZero L] in
/-- A translation invariant symmetric `M(σ)` is invariant under the point reflection `x ↦ c - x`: shift by
`x + y - c`, then symmetry. -/
private theorem KMolecule_reflect_inv (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y)
    (hsymm : ∀ (σ : Bool) (x y : Zd d L), M σ x y = M σ y x) (c : Zd d L) (σ : Bool) (x y : Zd d L) :
    M σ (c - x) (c - y) = M σ x y := by
  rw [hsymm σ (c - x) (c - y)]
  have := hshift σ (c - y) (c - x) (x + y - c)
  rw [show c - y + (x + y - c) = x by ring, show c - x + (x + y - c) = y by ring] at this
  exact this.symm

/-- **Reflection invariance of `Σ^{(π)}`** (the first clause of `SigSumZeroAbs`): `Σ^{(π)}(c - δ) = Σ^{(π)}(δ)` when
every `M(σ)` is translation invariant and symmetric (a reflection, not a translation of `δ`). -/
theorem baSigmaPi_reflect (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y)
    (hsymm : ∀ (σ : Bool) (x y : Zd d L), M σ x y = M σ y x) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) (c : Zd d L) :
    BASigmaPi d L n M t σ π (fun j => c - δ j) = BASigmaPi d L n M t σ π δ :=
  KMolecule_sigmaPi_perm (Equiv.subLeft c) M (fun σ x y => KMolecule_reflect_inv M hshift hsymm c σ x y) t σ π δ

end Clauses

/-- `M(σ)` of the block Anderson model is symmetric (`BAMB_symm`, `BA/Ward.lean:83`; `M(-) = M^*`). -/
private theorem KMolecule_BAMsigma_symm (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ x y = BAMsigma d L (BAMB d L g z m) σ y x := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, BAMB_symm d L g z m x y]
  · exact BAMB_symm d L g z m x y

/-- **The two translation clauses of `SigSumZeroAbs`** (the first two conjuncts, at alternating `σ`) for the molecule
weight `BASig`: the reflection `Σ(c - δ) = Σ(δ)` and the translation `Σ(δ + c) = Σ(δ)`.  `BAMsigma_shift`
(`BA/KSolve.lean:558`) and `BAMB_symm` (`BA/Ward.lean:83`) give the hypotheses of `baSigmaPi_shift`,
`baSigmaPi_reflect`, which hold for every `σ` and every `π` (the alternation is not used). -/
theorem baSig_transl {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ)
    (m : ι → ℂ) (t : ι → ℝ) :
    (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (c : Zd d (L i)) (δ : Fin n → Zd d (L i)),
        BASig d n L g E m t i σ (fun j => c - δ j) = BASig d n L g E m t i σ δ) ∧
    (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (δ : Fin n → Zd d (L i)) (c : Zd d (L i)),
        BASig d n L g E m t i σ (fun j => δ j + c) = BASig d n L g E m t i σ δ) :=
  ⟨fun i σ _ c δ => baSigmaPi_reflect _ (fun σ x y c => BAMsigma_shift d (L i) (g i) _ (m i) σ x y c)
      (KMolecule_BAMsigma_symm d (L i) (g i) _ (m i)) (t i) σ ∅ δ c,
    fun i σ _ δ c => baSigmaPi_shift _ (fun σ x y c => BAMsigma_shift d (L i) (g i) _ (m i) σ x y c) (t i) σ ∅ δ c⟩

/-! ## 4. The factorisation at an innermost long edge -/

section Cut

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **The cut of the self-energy of one tree at its chord `J`**: the generic cut `baCactus_cut` at the leaf weights
`1`, `P = Q = 1` (`1ᵀ = 1`: the reversed inner leaf of the cut carries no weight at the `Σ` level, C2) and the
chord weight `S = tΘ^{(σ_i,σ_j)}` (the chord `J` of the tree `F` already carries `S`), with the inner end `u` first. -/
private theorem KMolecule_tree_cut {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (δ : Fin n → Zd d L) :
    BASigmaTree d L M t F σ δ = ∑ u : Zd d L, ∑ w : Zd d L,
      BASigmaTree d L M t (KLFIn F J) (sigmaIn σ J) (BAdeltaIn J δ u) *
        ((t : ℂ) * BAThetaOf M t (σ J.1) (σ J.2) u w) *
      BASigmaTree d L M t (KLFOut F J) (sigmaOut σ J) (BAdeltaOut J δ w) := by
  have h := baCactus_cut hF hn hJ M t σ δ (fun _ => 1) 1 ((t : ℂ) • BAThetaOf M t (σ J.1) (σ J.2)) 1
  have hupd : Function.update (BACactusValEdgeW M t F σ) (Sum.inl ⟨J, hJ⟩)
      (1 * ((t : ℂ) • BAThetaOf M t (σ J.1) (σ J.2)) * 1) = BACactusValEdgeW M t F σ := by
    rw [one_mul, mul_one]
    exact Function.update_eq_self (Sum.inl ⟨J, hJ⟩) (BACactusValEdgeW M t F σ)
  have hin : BAdeltaIn J (fun _ : Fin n => (1 : Matrix (Zd d L) (Zd d L) ℂ)) (1 : Matrix (Zd d L) (Zd d L) ℂ)ᵀ =
      fun _ => 1 := by
    rw [Matrix.transpose_one]
    funext k
    simp only [BAdeltaIn, Function.update_apply]
    split_ifs <;> rfl
  have hout : BAdeltaOut J (fun _ : Fin n => (1 : Matrix (Zd d L) (Zd d L) ℂ)) 1 = fun _ => 1 := by
    funext k
    simp only [BAdeltaOut, Function.update_apply]
    split_ifs <;> rfl
  rw [hupd, hin, hout] at h
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  exact h

/-- The fourfold sum of the layer assembly: `Σ_G Σ_H Σ_{u,w} a(H,u) s(u,w) b(G,w) = Σ_{u,w} (Σ_H a(H,u)) s(u,w) (Σ_G b(G,w))`. -/
private theorem KMolecule_sum4 {α β : Type*} [Fintype α] [Fintype β] {γ : Type*} {γ' : Type*} (sG : Finset γ) (sH : Finset γ')
    (a : γ' → α → ℂ) (s : α → β → ℂ) (b : γ → β → ℂ) :
    ∑ G ∈ sG, ∑ H ∈ sH, ∑ u, ∑ w, a H u * s u w * b G w =
      ∑ u, ∑ w, (∑ H ∈ sH, a H u) * s u w * ∑ G ∈ sG, b G w := by
  calc ∑ G ∈ sG, ∑ H ∈ sH, ∑ u, ∑ w, a H u * s u w * b G w
      = ∑ G ∈ sG, ∑ u, ∑ w, ∑ H ∈ sH, a H u * s u w * b G w := by
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ u, ∑ w, ∑ G ∈ sG, ∑ H ∈ sH, a H u * s u w * b G w := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ u, ∑ w, (∑ H ∈ sH, a H u) * s u w * ∑ G ∈ sG, b G w := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul_sum, Finset.sum_comm]

/-- **The factorisation of the self-energy at an innermost long edge** (`(eq:molecule-Kpi)` by induction on `π`; the BA
twin of the molecule factorisation `Qlayer_cut`, `Loop/KLSumZeroWard.lean:293`).  Let `π = F_long(F₀, σ)` and let
`J = (i, j) ∈ π` be innermost.  Then `Σ^{(π)}(σ)` is the outer self-energy `Σ^{(π∖J)'}(σ_out)` on the outside polygon,
glued through the long edge `tΘ^{(σ_i,σ_j)}` (inner end `u`, outer end `w`) to the inner self-energy `Σ^{(∅)}(σ_in)` on the
inside polygon.  No `W`, no hypothesis on `M` or `t`.  The layer bijection is `Flong_eq_iff_cut` and `KLsum_cut`, the
gluing of one tree is `baCactus_cut`. -/
theorem baSigmaPi_cut (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π)
    (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (δ : Fin n → Zd d L) :
    BASigmaPi d L n M t σ π δ = ∑ u : Zd d L, ∑ w : Zd d L,
      BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ (BAdeltaIn J δ u) *
        ((t : ℂ) * BAThetaOf M t (σ J.1) (σ J.2) u w) *
      BASigmaPi d L (n - KLwIn J + 1) M t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J))
        (BAdeltaOut J δ w) := by
  have hF₀' := KLisTSP_of_mem_TSP hF₀
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJd : IsDiag n J.1 J.2 := hF₀'.1 J hJF₀
  set π' := (π.erase J).image (KLshiftOut J) with hπ'
  set A : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → Zd d L → ℂ := fun H u =>
    if KLFlong H (sigmaIn σ J) = ∅ then BASigmaTree d L M t H (sigmaIn σ J) (BAdeltaIn J δ u) else 0 with hA
  set B : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) → Zd d L → ℂ := fun G w =>
    if KLFlong G (sigmaOut σ J) = π' then BASigmaTree d L M t G (sigmaOut σ J) (BAdeltaOut J δ w) else 0 with hB
  set f : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) →
      Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ := fun G H =>
    ∑ u, ∑ w, A H u * ((t : ℂ) * BAThetaOf M t (σ J.1) (σ J.2) u w) * B G w with hf
  have hlayer : KLTSPlong n σ π = ((TSP n).filter fun F => J ∈ F).filter fun F => KLFlong F σ = π := by
    ext F
    simp only [KLTSPlong, Finset.mem_filter]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨⟨hF, Flong_subset F σ (h ▸ hJπ)⟩, h⟩
    · rintro ⟨⟨hF, -⟩, h⟩
      exact ⟨hF, h⟩
  have hpt : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if KLFlong F σ = π then BASigmaTree d L M t F σ δ else 0) = f (KLFOut F J) (KLFIn F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := Finset.mem_filter.1 hF
    have hF' := KLisTSP_of_mem_TSP hFT
    have hiff := Flong_eq_iff_cut hF' hn hJF σ hF₀' hπ hJπ hinner
    by_cases h : KLFlong F σ = π
    · obtain ⟨h1, h2⟩ := hiff.1 h
      have h1' : KLFlong (KLFOut F J) (sigmaOut σ J) = π' := h1
      simp only [h, ↓reduceIte, f, A, B, h1', h2]
      exact KMolecule_tree_cut hF' hn hJF M t σ δ
    · simp only [h, ↓reduceIte, f]
      by_cases h1 : KLFlong (KLFOut F J) (sigmaOut σ J) = π'
      · have h2 : ¬KLFlong (KLFIn F J) (sigmaIn σ J) = ∅ := fun h2 => h (hiff.2 ⟨h1, h2⟩)
        simp [A, B, h2]
      · simp [A, B, h1]
  have hA' : ∀ u, ∑ H ∈ KLTSPlong (KLwIn J + 1) (sigmaIn σ J) ∅,
      BASigmaTree d L M t H (sigmaIn σ J) (BAdeltaIn J δ u) = ∑ H ∈ TSP (KLwIn J + 1), A H u := fun u => by
    simp only [KLTSPlong, hA, Finset.sum_filter]
  have hB' : ∀ w, ∑ G ∈ KLTSPlong (n - KLwIn J + 1) (sigmaOut σ J) π',
      BASigmaTree d L M t G (sigmaOut σ J) (BAdeltaOut J δ w) = ∑ G ∈ TSP (n - KLwIn J + 1), B G w := fun w => by
    simp only [KLTSPlong, hB, Finset.sum_filter]
  unfold BASigmaPi
  rw [hlayer, Finset.sum_filter, Finset.sum_congr rfl hpt, KLsum_cut hJd hn f]
  simp only [hA', hB', hf]
  exact KMolecule_sum4 _ _ A (fun u w => (t : ℂ) * BAThetaOf M t (σ J.1) (σ J.2) u w) B

end Cut

/-! ## 5. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`,
`0 < P.g0`), `W = 2` (`W^d = 8`), `κ = Im m₀ > 0`, `t = 1/2`, `n = 4` (`TSP 4 = {∅, {(0,2)}, {(1,3)}}`), the charges
`σ = (+,+,-,+)` (`σ_0 ≠ σ_2`: the chord `(0,2)` is long), four distinct labels.  The cut is at `J = (0,2)` of the tree
`{(0,2)}`, `π = {(0,2)}`: an inner and an outer triangle, `π' = ∅`.  Every deterministic hypothesis is discharged; the only
hypothesis of an `example` is the bound clause of `SigSumZeroAbs`, which is K07/K08's pin. -/

namespace KMoleculeInst

open RBM.BA.MFixedPointInst

/-- `baK_eq_sum_Kpi` (`(eq_K-Kpi)`) at the flow point: `𝒦^{(4)} = W^{-3d} Σ_{π ⊆ {(0,2),(1,3)}} K^{(π)}`. -/
example :=
  baK_eq_sum_Kpi 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    (n := 4) (by norm_num) ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- `baKpi_eq_sum_SigmaPi` (the first stage) at the same data, the layer `π = {(0,2)}`. -/
example :=
  baKpi_eq_sum_SigmaPi (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2)
    ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] {((0 : Fin 4), (2 : Fin 4))}

/-- `baSigmaPi_cut` (the factorisation) at the cut `J = (0,2)` of the tree `{(0,2)} ∈ TSP 4`, the layer
`π = KLFlong {(0,2)} σ = {(0,2)}`: `J` is innermost, the outer and the inner polygon are triangles. -/
example :=
  baSigmaPi_cut (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num)
    (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
    (F₀ := {((0 : Fin 4), (2 : Fin 4))}) (by rw [TSP_four]; simp) (π := {((0 : Fin 4), (2 : Fin 4))})
    (by decide) (Finset.mem_singleton_self _) (fun e he _ => Finset.mem_singleton.1 he)
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- `baSigmaPi_shift`, `baSigmaPi_reflect` at the layer `π = {(0,2)}`. -/
example :=
  baSigmaPi_shift (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
    (fun σ x y c => BAMsigma_shift 3 4 P.g0 _ P.m0 σ x y c) (1 / 2) ![true, true, false, true]
    {((0 : Fin 4), (2 : Fin 4))} ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ![1, 0, 0]

example :=
  baSigmaPi_reflect (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
    (fun σ x y c => BAMsigma_shift 3 4 P.g0 _ P.m0 σ x y c) (KMolecule_BAMsigma_symm 3 4 P.g0 _ P.m0) (1 / 2)
    ![true, true, false, true] {((0 : Fin 4), (2 : Fin 4))} ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ![1, 0, 0]

/-- The molecule weight at the flow point, `ι = Unit`, as a family of the type of `Sig`. -/
private noncomputable abbrev Sig0 := BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
  (fun _ => (1 : ℝ) / 2)

/-- **`baSig_transl`** at the flow point, alternating `σ = (+,-,+,-)`: the reflection clause (`c = (1,0,0)`). -/
example :=
  (baSig_transl (ι := Unit) 3 4 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (1 : ℝ) / 2)).1 () ![true, false, true, false] (by decide) ![1, 0, 0]
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- The translation clause at the same data. -/
example :=
  (baSig_transl (ι := Unit) 3 4 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
    (fun _ => (1 : ℝ) / 2)).2 () ![true, false, true, false] (by decide)
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ![1, 0, 0]

/-- **The interface**: `BASig` has the type of the molecule weight of `SigSumZeroAbs`; the first two conjuncts are
`baSig_transl`, the bound clause (the third conjunct, K07/K08's pin) stays a hypothesis. -/
example (h3 : ∀ Q : ℕ, Q ≤ 2 * (3 - 1) → ∃ C : ℝ, 0 < C ∧
      ∀ (σ : Fin 4 → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin 4) (x : Zd 3 4),
        ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ r = x), Sig0 () σ δ‖ ≤ C * (1 - (1 : ℝ) / 2) ∧
        ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ r = x),
            ‖Sig0 () σ δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ Q ≤ C * (P.g0 ^ 2 + (1 - (1 : ℝ) / 2))) :
    SigSumZeroAbs 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => (1 : ℝ) / 2) Sig0 :=
  ⟨(baSig_transl (ι := Unit) 3 4 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
      (fun _ => (1 : ℝ) / 2)).1,
    (baSig_transl (ι := Unit) 3 4 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0)
      (fun _ => (1 : ℝ) / 2)).2,
    fun Q hQ => by
      obtain ⟨C, hC, h⟩ := h3 Q hQ
      exact ⟨C, hC, fun _ σ hσ r x => h σ hσ r x⟩⟩

/-- `BASig` also has the type `Sig` of `IndStepAbs` (`Loop/KLIndStepB.lean:77`), with the leaf edges `TH = Θ` of the BA data. -/
example (Bp : Unit → ℝ) : Prop :=
  IndStepAbs 3 4 (fun _ : Unit => 4) Bp Sig0 (fun _ s s' => BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) s s')

end KMoleculeInst

end RBM.BA
