/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLSumAll
import RBM3D.Loop.KLCut

/-!
# The sum-zero identity `R_n(1) = 0` and the signed sum-zero bound, `d ≥ 3`

Ticket T2056 (KL7c).  Paper: `(eq:Sigma-empty-sum-zero)`, first estimate
(`paper/tex/A_deterministic_estimates.tex:731`), established in [YY_25, Lemma 3.10]; the paper
notes (`:734`) that these proofs are dimension-independent and rely only on the pure loop
estimate, the short-edge bound, the `M`-edge bound and Ward's identity (WI_calK) for `𝒦`-loops.
RBM2D's label for it is `(SZjadljsk)`.  The second estimate is KL9.

* `Qlayer_alt_one_eq_zero`: `Q(σ^{(alt)}, ∅)|_{t=1} = 0` (`R_n(1) = 0`, [YY_25] Lemma 3.10 (2))
  for every even `n ≥ 4` and `|E| < 2`; `Q` and `A` do not depend on `d`, `g`, `L`, `W`.
* `KLSigmaPi_alt_sumZero_le`: the signed sum-zero bound, the statement of the conditional adapter
  `SigmaPi_alt_sumZero_le_of_Qlayer_one` (KL7a, `KLSumZero.lean:813`) without its hypothesis
  `Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0`.  Constant explicit, bulk `|E| ≤ 2 - κ` (RBM2D's
  paper-delta T2004a-11; cited, not re-proposed).

Port of `../RBM2D/RBM2D/Loop/SumZeroWard.lean` at `c9a24cf` (2085 lines), sections 4-12; its
section 13 (checks over `Z2`) is replaced by the instances at the end of this file.
Sections 1-3 there (the laminar API, the cut families, the cut bijection) are private copies of
what is public in the merged `KLTree.lean`/`KLCut.lean`, and are used from there (`KLsum_cut`,
`KLFIn`, `KLFOut`, `KLshiftIn`, `KLshiftOut`, `KLunCol`, `KLoutEnds_of`, `KLdiag_width`, ...).
Written here, `private`: the inside/outside charges `sigmaIn`, `sigmaOut` and `exists_innermost`,
`Flong_subset_diagonals` (public in RBM2D's `KBoundCut.lean:45, 59, 1876, 1893`, absent from
RBM3D), the layer facts `Flong_FOut`, `Flong_FIn`, `Flong_eq_iff_cut`, the molecule factorization
`prod_cut`, `Qlayer_cut`, `prod_cyc`, `prod_leaves_cut`, `Alayer_cut`, the base bound (3.49), the
induction (3.50), and the copies `KLSumZeroWard_{gapK_pos, gapK_le_one, norm_edge_le,
norm_edge_sub_le, norm_prod_sub_prod_le}` of helpers that are private in `KLSumZero.lean`.
Renaming: `Z2 L ↦ Zd d L`, `Flong ↦ KLFlong`, `TSPlong ↦ KLTSPlong`, `sigAlt ↦ KLsigAlt`,
`mSig ↦ mSigma`, `Gauss.spectralM ↦ mE`, `etaT ↦ Gauss.etaT`, `Kcal ↦ KLK`, `Kpi ↦ KLKpi`,
`SigmaPi ↦ KLSigmaPi`, `Kcal_sumAll_le ↦ KLK_sumAll_le`, `Kcal_eq_sum_Kpi ↦ KLK_eq_sum_Kpi`,
`wIn, shiftIn, shiftOut, FIn, FOut, col, unCol, ArcLe, IsTSP, ... ↦ KL...` (merged `KLCut`).

**What differs from RBM2D beyond renaming and exponents** (DECISIONS §23: the merged `Alayer` is
`(∏_i m(σ_i)) ∏_v (1 - ξ_v)⁻¹ Q`, as the merged `KLKpi` carries `∏_i m(σ_i)`; RBM2D's does not):
* `Alayer_cut`: RBM2D's prefactor `ξ_J (1 - ξ_J)`, `ξ_J = t m(σ_i) m(σ_j)`, becomes `t (1 - ξ_J)`
  (equal to `ξ_J (1 - ξ_J) / (m(σ_i) m(σ_j))` when `m(σ_i) m(σ_j) ≠ 0`): the vertices `i`, `j` of
  `J` lie on both polygons, so `∏_in m · ∏_out m = (∏ m) m(σ_i) m(σ_j)` (`prod_leaves_cut` with
  `g s s' = m s`).  For a long edge `m(σ_i) m(σ_j) = 1`, `ξ_J = t`: both prefactors are `t (1 - t)`
  and the induction (3.50) is RBM2D's.
* the base bound (3.49): `|Z_3²| = 9` becomes `|Z_3^3| = 27` (the bound is `d`-free, proved at
  `d = 3`, `g = 1`), and `KLK_eq_sum_Kpi` at `W = 1` reads `∑_π KLKpi = KLK` (RBM2D: `(∏ m)⁻¹ 𝒦`),
  so the step `‖∏ m‖ = 1` is not needed.  `W^d` enters only through `KLK_sumAll_le` at `W = 1`.
* (3.51): `Q(t) = (1 - t)^n A(σ^{(alt)}, ∅)(t)` uses `∏_i m(σ^{(alt)}_i) = 1` (`n` even).
* the flip `Alayer_not`: the factor `∏ m` goes to its conjugate; the statement is RBM2D's.
No other change.  No hypothesis is added, no statement weakened; `d` and `g` are free (no `3 ≤ d`).
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. The charges of the inside and outside polygons of a cut -/

section Charges

variable {n : ℕ} [NeZero n]

/-- The charges of the inside polygon of the cut `J = (i, j)`: its vertex `k` is the vertex
`i + k`.  (RBM2D `Loop/KBoundCut.lean:45`; not in the merged `KLCut`.) -/
private def sigmaIn (σ : Fin n → Bool) (J : Fin n × Fin n) : Fin (KLwIn J + 1) → Bool :=
  fun k => σ ⟨min (J.1.val + k.val) (n - 1), by have := NeZero.pos n; omega⟩

/-- The charges of the outside polygon of the cut `J` (`n - KLwIn J + 1` vertices): the arc of
`J` is collapsed to its left end.  (RBM2D `Loop/KBoundCut.lean:59`.) -/
private def sigmaOut (σ : Fin n → Bool) (J : Fin n × Fin n) : Fin (n - KLwIn J + 1) → Bool :=
  fun k => σ ⟨min (KLunCol J k.val) (n - 1), by have := NeZero.pos n; omega⟩

end Charges

/-! ## 2. The layer condition across the cut -/

section LayerFacts

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

omit [NeZero n] in
private theorem mem_Flong {F : Finset (Fin n × Fin n)} {σ : Fin n → Bool} {d : Fin n × Fin n} :
    d ∈ KLFlong F σ ↔ d ∈ F ∧ σ d.1 ≠ σ d.2 := mem_filter

omit [NeZero n] in
private theorem Flong_subset (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) :
    KLFlong F σ ⊆ F :=
  filter_subset _ _

omit [NeZero n] in
private theorem arcLe_le {d : Fin n × Fin n} (h : KLArcLe d J) (h12 : d.1 ≤ d.2) :
    J.1.val ≤ d.1.val ∧ d.2.val ≤ J.2.val ∧ d.1.val ≤ d.2.val := by
  simp only [KLArcLe, Fin.le_def] at h h12
  exact ⟨h.1, h.2, h12⟩

private theorem sigmaIn_shiftIn (σ : Fin n → Bool) {d : Fin n × Fin n} (hd : KLArcLe d J)
    (h12 : d.1 ≤ d.2) :
    sigmaIn σ J (KLshiftIn J d).1 = σ d.1 ∧ sigmaIn σ J (KLshiftIn J d).2 = σ d.2 := by
  obtain ⟨h1, h2⟩ := KLshiftIn_val hd h12
  obtain ⟨a1, a2, a3⟩ := arcLe_le hd h12
  have hd1 := d.1.isLt
  have hd2 := d.2.isLt
  constructor <;> (unfold sigmaIn; congr 1; ext; simp only [h1, h2]; omega)

private theorem sigmaOut_shiftOut (σ : Fin n → Bool) {d : Fin n × Fin n} (hd : KLOutEnds J d)
    (hJ : J.1.val + 2 ≤ J.2.val) :
    sigmaOut σ J (KLshiftOut J d).1 = σ d.1 ∧ sigmaOut σ J (KLshiftOut J d).2 = σ d.2 := by
  obtain ⟨h1, h2⟩ := KLshiftOut_val d (by omega : J.1.val < J.2.val)
  have hd1 := d.1.isLt
  have hd2 := d.2.isLt
  have e1 := KLunCol_col hd.1 hJ
  have e2 := KLunCol_col hd.2.1 hJ
  constructor <;> (unfold sigmaOut; congr 1; ext; simp only [h1, h2, e1, e2]; omega)

variable {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
include hF hn hJ

/-- The long edges of the outside family are the outside long edges of `F`. -/
private theorem Flong_FOut (σ : Fin n → Bool) :
    KLFlong (KLFOut F J) (sigmaOut σ J) =
      ((KLFlong F σ).filter fun d => ¬KLArcLe d J).image (KLshiftOut J) := by
  have hJw := KLdiag_width hF hJ
  unfold KLFlong KLFOut
  rw [filter_image]
  congr 1
  ext d
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hdF, hdJ⟩, hl⟩
    obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ
      (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hdF) hdJ) hJw
    exact ⟨⟨hdF, by rwa [e1, e2] at hl⟩, hdJ⟩
  · rintro ⟨⟨hdF, hl⟩, hdJ⟩
    obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ
      (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hdF) hdJ) hJw
    exact ⟨⟨hdF, hdJ⟩, by rwa [e1, e2]⟩

omit hn hJ in
/-- The long edges of the inside family are the long edges of `F` strictly inside `J`. -/
private theorem Flong_FIn (σ : Fin n → Bool) :
    KLFlong (KLFIn F J) (sigmaIn σ J) =
      ((KLFlong F σ).filter fun d => KLArcLe d J ∧ d ≠ J).image (KLshiftIn J) := by
  have h12 : ∀ d ∈ F, d.1 ≤ d.2 := fun d hd => le_of_lt (hF.1 d hd).1
  unfold KLFlong KLFIn
  rw [filter_image]
  congr 1
  ext d
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hdF, hdJ, hne⟩, hl⟩
    obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
    exact ⟨⟨hdF, by rwa [e1, e2] at hl⟩, hdJ, hne⟩
  · rintro ⟨⟨hdF, hl⟩, hdJ, hne⟩
    obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
    exact ⟨⟨hdF, hdJ, hne⟩, by rwa [e1, e2]⟩

/-- **The layer condition across the cut.**  Let `π = F_long(F₀, σ)` for some tree `F₀` and let
`J ∈ π` be innermost.  Then a tree `F ∋ J` lies in the layer `π` iff its inside family has no
long edges and the long edges of its outside family are `π ∖ {J}`, collapsed. -/
private theorem Flong_eq_iff_cut (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)}
    (hF₀ : KLIsTSP F₀)
    {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π)
    (hinner : ∀ e ∈ π, KLArcLe e J → e = J) :
    KLFlong F σ = π ↔
      KLFlong (KLFOut F J) (sigmaOut σ J) = (π.erase J).image (KLshiftOut J) ∧
      KLFlong (KLFIn F J) (sigmaIn σ J) = ∅ := by
  have hJw := KLdiag_width hF hJ
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJπ)).2
  have hπout : ∀ e ∈ π.erase J, KLOutEnds J e ∧ ¬KLArcLe e J := by
    intro e he
    obtain ⟨hne, heπ⟩ := mem_erase.1 he
    have hnot : ¬KLArcLe e J := fun h => hne (hinner e heπ h)
    exact ⟨KLoutEnds_of hF₀ hn hJF₀ (KLmem_nodes_of_mem (Flong_subset F₀ σ (hπ ▸ heπ))) hnot,
      hnot⟩
  have hπerase : π.filter (fun d => ¬KLArcLe d J) = π.erase J := by
    ext e
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨heπ, hnot⟩
      exact ⟨fun h => hnot (h ▸ ⟨le_rfl, le_rfl⟩), heπ⟩
    · rintro ⟨hne, heπ⟩
      exact ⟨heπ, fun h => hne (hinner e heπ h)⟩
  have hπin : π.filter (fun d => KLArcLe d J ∧ d ≠ J) = ∅ := by
    refine filter_eq_empty_iff.2 fun e heπ h => h.2 (hinner e heπ h.1)
  rw [Flong_FOut hF hn hJ, Flong_FIn hF σ]
  constructor
  · intro h
    rw [h, hπerase, hπin, image_empty]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hout, hin⟩
    have hin' : (KLFlong F σ).filter (fun d => KLArcLe d J ∧ d ≠ J) = ∅ := image_eq_empty.1 hin
    have hout' : (KLFlong F σ).filter (fun d => ¬KLArcLe d J) = π.erase J := by
      ext e
      constructor
      · intro he
        obtain ⟨heF, heJ⟩ := mem_filter.1 he
        have heO := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem (Flong_subset F σ heF)) heJ
        have : KLshiftOut J e ∈ (π.erase J).image (KLshiftOut J) := hout ▸ mem_image_of_mem _ he
        obtain ⟨e', he', hee'⟩ := mem_image.1 this
        rwa [← KLshiftOut_injOn (hπout e' he').1 heO hJw hee']
      · intro he
        have : KLshiftOut J e ∈ ((KLFlong F σ).filter fun d => ¬KLArcLe d J).image (KLshiftOut J) :=
          hout ▸ mem_image_of_mem _ he
        obtain ⟨e', he', hee'⟩ := mem_image.1 this
        obtain ⟨he'F, he'J⟩ := mem_filter.1 he'
        have he'O := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem (Flong_subset F σ he'F)) he'J
        rwa [← KLshiftOut_injOn he'O (hπout e he).1 hJw hee']
    ext e
    constructor
    · intro he
      by_cases heJ : e = J
      · exact heJ ▸ hJπ
      by_cases hin : KLArcLe e J
      · have : e ∈ (KLFlong F σ).filter (fun d => KLArcLe d J ∧ d ≠ J) :=
          mem_filter.2 ⟨he, hin, heJ⟩
        rw [hin'] at this
        exact absurd this (notMem_empty e)
      · have : e ∈ (KLFlong F σ).filter (fun d => ¬KLArcLe d J) := mem_filter.2 ⟨he, hin⟩
        rw [hout'] at this
        exact (mem_erase.1 this).2
    · intro he
      by_cases heJ : e = J
      · exact heJ ▸ mem_Flong.2 ⟨hJ, hJlong⟩
      · have : e ∈ π.erase J := mem_erase.2 ⟨heJ, he⟩
        rw [← hout'] at this
        exact (mem_filter.1 this).1

end LayerFacts

/-! ## 3. The molecule factorization at an innermost long edge -/

section MoleculeCut

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **A product over the edges of `F ∋ J` splits over the cut**: the edge `J`, the outside
family and the inside family, each with its own charges. -/
private theorem prod_cut {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
    (σ : Fin n → Bool) (w : Bool → Bool → ℂ) :
    ∏ e ∈ F, w (σ e.1) (σ e.2) =
      w (σ J.1) (σ J.2) * (∏ g ∈ KLFOut F J, w (sigmaOut σ J g.1) (sigmaOut σ J g.2)) *
        ∏ h ∈ KLFIn F J, w (sigmaIn σ J h.1) (sigmaIn σ J h.2) := by
  have hJw := KLdiag_width hF hJ
  have h12 : ∀ d ∈ F, d.1 ≤ d.2 := fun d hd => le_of_lt (hF.1 d hd).1
  rw [← mul_prod_erase F _ hJ, mul_assoc]
  congr 1
  rw [← prod_filter_mul_prod_filter_not (F.erase J) (fun d => KLArcLe d J), mul_comm]
  have hout : (F.erase J).filter (fun d => ¬KLArcLe d J) = F.filter (fun d => ¬KLArcLe d J) := by
    ext d
    simp only [mem_filter, mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · exact fun h => ⟨⟨fun hdJ => h.2 (hdJ ▸ ⟨le_rfl, le_rfl⟩), h.1⟩, h.2⟩
  have hin : (F.erase J).filter (fun d => KLArcLe d J) =
      F.filter (fun d => KLArcLe d J ∧ d ≠ J) := by
    ext d
    simp only [mem_filter, mem_erase]
    tauto
  rw [hout, hin]
  congr 1
  · unfold KLFOut
    rw [prod_image]
    · refine prod_congr rfl fun d hd => ?_
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      obtain ⟨e1, e2⟩ := sigmaOut_shiftOut σ
        (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hdF) hdJ) hJw
      rw [e1, e2]
    · intro d hd e he h
      obtain ⟨hdF, hdJ⟩ := mem_filter.1 hd
      obtain ⟨heF, heJ⟩ := mem_filter.1 he
      exact KLshiftOut_injOn (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem hdF) hdJ)
        (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem heF) heJ) hJw h
  · unfold KLFIn
    rw [prod_image]
    · refine prod_congr rfl fun d hd => ?_
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      obtain ⟨e1, e2⟩ := sigmaIn_shiftIn σ hdJ (h12 d hdF)
      rw [e1, e2]
    · intro d hd e he h
      obtain ⟨hdF, hdJ, -⟩ := mem_filter.1 hd
      obtain ⟨heF, heJ, -⟩ := mem_filter.1 he
      exact KLshiftIn_injOn hdJ (h12 d hdF) heJ (h12 e heF) h

/-- **The molecule factorization (3.53)–(3.58), closed form.**  If `J` is an innermost long
edge of the layer `π = F_long(F₀, σ)`, then
`Q(σ, π) = r_J · Q(σ_out, π ∖ {J}) · Q(σ_in, ∅)`.  (`Q` carries no factor `∏ m`.) -/
private theorem Qlayer_cut (hn : 2 ≤ n) (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)}
    (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) :
    Qlayer m t σ π = edgeR m t (σ J.1) (σ J.2) *
      Qlayer m t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) *
        Qlayer m t (sigmaIn σ J) ∅ := by
  have hF₀' := KLisTSP_of_mem_TSP hF₀
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJd : IsDiag n J.1 J.2 := hF₀'.1 J hJF₀
  set π' := (π.erase J).image (KLshiftOut J)
  set f : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) →
      Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ := fun G H =>
    (if KLFlong G (sigmaOut σ J) = π' then
      ∏ g ∈ G, edgeR m t (sigmaOut σ J g.1) (sigmaOut σ J g.2) else 0) *
    (if KLFlong H (sigmaIn σ J) = ∅ then
      ∏ h ∈ H, edgeR m t (sigmaIn σ J h.1) (sigmaIn σ J h.2) else 0)
  have hlayer : KLTSPlong n σ π =
      ((TSP n).filter fun F => J ∈ F).filter fun F => KLFlong F σ = π := by
    ext F
    simp only [KLTSPlong, mem_filter]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨⟨hF, Flong_subset F σ (h ▸ hJπ)⟩, h⟩
    · rintro ⟨⟨hF, -⟩, h⟩
      exact ⟨hF, h⟩
  have hpt : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if KLFlong F σ = π then ∏ e ∈ F, edgeR m t (σ e.1) (σ e.2) else 0)
        = edgeR m t (σ J.1) (σ J.2) * f (KLFOut F J) (KLFIn F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    have hF' := KLisTSP_of_mem_TSP hFT
    have hiff := Flong_eq_iff_cut hF' hn hJF σ hF₀' hπ hJπ hinner
    by_cases h : KLFlong F σ = π
    · obtain ⟨h1, h2⟩ := hiff.1 h
      have h1' : KLFlong (KLFOut F J) (sigmaOut σ J) = π' := h1
      simp only [f, h, h1', h2, ↓reduceIte, prod_cut hF' hn hJF σ]
      ring
    · simp only [f, h, ↓reduceIte]
      by_cases h1 : KLFlong (KLFOut F J) (sigmaOut σ J) = π'
      · have h2 : ¬KLFlong (KLFIn F J) (sigmaIn σ J) = ∅ := fun h2 => h (hiff.2 ⟨h1, h2⟩)
        simp [h2]
      · simp [h1]
  unfold Qlayer
  rw [hlayer, sum_filter, sum_congr rfl hpt, ← mul_sum, KLsum_cut hJd hn f]
  simp only [f, ← sum_mul_sum, ← sum_filter]
  rw [mul_assoc]
  rfl

end MoleculeCut

section Leaves

private theorem fin_congr {N : ℕ} {α : Type*} (σ : Fin N → α) {a b : ℕ} (ha : a < N)
    (hb : b < N) (h : a = b) : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := by
  subst h; rfl

/-- A cyclic product over consecutive pairs, written over `range`. -/
private theorem prod_cyc {k : ℕ} (τ : Fin (k + 1) → Bool) (g : Bool → Bool → ℂ) :
    ∏ v : Fin (k + 1), g (τ v) (τ (v + 1)) =
      (∏ v ∈ range k, g (τ ⟨min v k, by omega⟩) (τ ⟨min (v + 1) k, by omega⟩)) *
        g (τ (Fin.last k)) (τ 0) := by
  rw [Fin.prod_univ_castSucc, Fin.last_add_one]
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← Fin.prod_univ_eq_prod_range
    (fun v => g (τ ⟨min v k, by omega⟩) (τ ⟨min (v + 1) k, by omega⟩)) k]
  refine prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have h1 : Fin.castSucc i = ⟨min i k, by omega⟩ :=
    Fin.ext (by rw [Fin.val_castSucc]; exact (min_eq_left hi.le).symm)
  have h2 : Fin.castSucc i + 1 = ⟨min (i + 1) k, by omega⟩ := by
    ext
    rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), Fin.val_castSucc]
    exact (min_eq_left hi).symm
  rw [h2, h1]

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **The boundary edges across the cut**:
`∏_v g(σ_v, σ_{v+1}) · g(σ_j, σ_i) g(σ_i, σ_j) = ∏_{in} · ∏_{out}`. -/
private theorem prod_leaves_cut (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool)
    (g : Bool → Bool → ℂ) :
    (∏ v : Fin n, g (σ v) (σ (v + 1))) * (g (σ J.2) (σ J.1) * g (σ J.1) (σ J.2)) =
      (∏ k : Fin (KLwIn J + 1), g (sigmaIn σ J k) (sigmaIn σ J (k + 1))) *
        ∏ k : Fin (n - KLwIn J + 1), g (sigmaOut σ J k) (sigmaOut σ J (k + 1)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  obtain ⟨hlt, hne1, hnot⟩ := hJd
  rw [Fin.lt_def] at hlt
  have hjn : J.2.val ≤ n' := by have := J.2.isLt; omega
  have hw : KLwIn J = J.2.val - J.1.val := rfl
  have hunc : ∀ v, v ≤ J.1.val → KLunCol J v = v := fun v hv => KLunCol_of_le hv
  have hunc' : ∀ v, J.1.val < v → KLunCol J v = v + (KLwIn J - 1) := fun v hv => KLunCol_of_gt hv
  set σ' : ℕ → Bool := fun r => σ ⟨min r n', by omega⟩ with hσ'
  set G : ℕ → ℂ := fun r => g (σ' r) (σ' (r + 1)) with hG
  have hJ1 : σ J.1 = σ' J.1.val := fin_congr σ J.1.isLt (by omega) (by omega)
  have hJ2 : σ J.2 = σ' J.2.val := fin_congr σ J.2.isLt (by omega) (by omega)
  have horig : ∏ v : Fin (n' + 1), g (σ v) (σ (v + 1)) =
      (∏ v ∈ range n', G v) * g (σ' n') (σ' 0) := by
    rw [prod_cyc σ g]
    refine congrArg₂ (· * ·) rfl (congrArg₂ g ?_ ?_) <;>
      exact fin_congr σ _ _ (by simp)
  have hin : ∏ k : Fin (KLwIn J + 1), g (sigmaIn σ J k) (sigmaIn σ J (k + 1)) =
      (∏ v ∈ Ico J.1.val J.2.val, G v) * g (σ' J.2.val) (σ' J.1.val) := by
    rw [prod_cyc (sigmaIn σ J) g, prod_Ico_eq_prod_range]
    refine congrArg₂ (· * ·) (prod_congr rfl fun v hv => ?_) (congrArg₂ g ?_ ?_)
    · rw [mem_range] at hv
      exact congrArg₂ g (fin_congr σ _ _ (by simp; omega)) (fin_congr σ _ _ (by simp; omega))
    · exact fin_congr σ _ _ (by simp; omega)
    · exact fin_congr σ _ _ (by simp)
  have hout : ∏ k : Fin (n' + 1 - KLwIn J + 1), g (sigmaOut σ J k) (sigmaOut σ J (k + 1)) =
      (∏ v ∈ range J.1.val, G v) * g (σ' J.1.val) (σ' J.2.val) *
        (∏ v ∈ Ico J.2.val n', G v) * g (σ' n') (σ' 0) := by
    rw [prod_cyc (sigmaOut σ J) g]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ g ?_ ?_)
    · rw [← prod_range_mul_prod_Ico _ (show J.1.val ≤ n' + 1 - KLwIn J by omega),
        prod_eq_prod_Ico_succ_bot (show J.1.val < n' + 1 - KLwIn J by omega), ← mul_assoc]
      refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_congr rfl fun v hv => ?_) ?_) ?_
      · rw [mem_range] at hv
        refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show v ≤ n' + 1 - KLwIn J by omega)]
          rw [hunc _ (by omega)]; omega
        · simp only [min_eq_left (show v + 1 ≤ n' + 1 - KLwIn J by omega)]
          rw [hunc _ (by omega)]; omega
      · refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show J.1.val ≤ n' + 1 - KLwIn J by omega)]
          rw [hunc _ le_rfl]; omega
        · simp only [min_eq_left (show J.1.val + 1 ≤ n' + 1 - KLwIn J by omega)]
          rw [hunc' _ (by omega)]; omega
      · rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range,
          show n' + 1 - KLwIn J - (J.1.val + 1) = n' - J.2.val by omega]
        refine prod_congr rfl fun v hv => ?_
        rw [mem_range] at hv
        refine congrArg₂ g (fin_congr σ _ _ ?_) (fin_congr σ _ _ ?_)
        · simp only [min_eq_left (show J.1.val + 1 + v ≤ n' + 1 - KLwIn J by omega)]
          rw [hunc' _ (by omega)]; omega
        · simp only [min_eq_left (show J.1.val + 1 + v + 1 ≤ n' + 1 - KLwIn J by omega)]
          rw [hunc' _ (by omega)]; omega
    · refine fin_congr σ _ _ ?_
      simp only [Fin.val_last, min_self]
      rw [hunc' _ (by omega)]; omega
    · refine fin_congr σ _ _ ?_
      simp only [Fin.val_zero, Nat.zero_min]
      rw [hunc _ (Nat.zero_le _)]; omega
  rw [horig, hin, hout, hJ1, hJ2]
  rw [← prod_range_mul_prod_Ico G (show J.1.val ≤ n' by omega),
    ← prod_Ico_consecutive G (show J.1.val ≤ J.2.val by omega) hjn]
  ring

end Leaves

section MoleculeA

variable {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- **(3.60)–(3.64) in closed form, with the factor `∏_i m(σ_i)` of the merged `Alayer`**
(DECISIONS §23).  At an innermost long edge `J` of the layer `π`,
`A(σ, π) = t (1 - ξ_J) · A(σ_in, ∅) · A(σ_out, π ∖ {J})`, `ξ_J = t m(σ_i) m(σ_j)`.
RBM2D's prefactor is `ξ_J (1 - ξ_J)`; the new one is `ξ_J (1 - ξ_J) / (m(σ_i) m(σ_j))`, because the
vertices `i`, `j` of `J` lie on both polygons, so `∏_in m · ∏_out m = (∏ m) m(σ_i) m(σ_j)`
(`prod_leaves_cut` with `g s s' = m s`). -/
private theorem Alayer_cut (hn : 2 ≤ n) (m : Bool → ℂ) {t : ℝ}
    (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)}
    (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) :
    Alayer m t σ π = (t : ℂ) * (1 - t * (m (σ J.1) * m (σ J.2))) *
      Alayer m t (sigmaIn σ J) ∅ *
        Alayer m t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) := by
  have hJd : IsDiag n J.1 J.2 :=
    (KLisTSP_of_mem_TSP hF₀).1 J (Flong_subset F₀ σ (hπ ▸ hJπ))
  set g : Bool → Bool → ℂ := fun s s' => (1 - (t : ℂ) * (m s * m s'))⁻¹ with hg
  have hP := prod_leaves_cut hJd σ g
  have hPm := prod_leaves_cut hJd σ (fun s _ => m s)
  set ξ : ℂ := (t : ℂ) * (m (σ J.1) * m (σ J.2)) with hξ
  have hx : 1 - ξ ≠ 0 := by
    intro h
    have : ‖ξ‖ = 1 := by rw [show ξ = 1 by linear_combination -h, norm_one]
    exact absurd (hm (σ J.1) (σ J.2)) (by rw [this]; exact lt_irrefl 1)
  have hgJ : g (σ J.2) (σ J.1) = (1 - ξ)⁻¹ := by simp only [g, ξ, mul_comm (m (σ J.2))]
  have hgJ' : g (σ J.1) (σ J.2) = (1 - ξ)⁻¹ := rfl
  rw [hgJ, hgJ'] at hP
  unfold Alayer
  rw [Qlayer_cut hn m t σ hF₀ hπ hJπ hinner]
  unfold edgeR
  simp only [g] at hP
  rw [← hξ]
  have hP' : ∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹ =
      (∏ k : Fin (KLwIn J + 1),
          (1 - (t : ℂ) * (m (sigmaIn σ J k) * m (sigmaIn σ J (k + 1))))⁻¹) *
        (∏ k : Fin (n - KLwIn J + 1),
          (1 - (t : ℂ) * (m (sigmaOut σ J k) * m (sigmaOut σ J (k + 1))))⁻¹) * (1 - ξ) ^ 2 := by
    rw [← hP]
    field_simp
  rw [hP']
  have hu : (1 - ξ) * (1 - ξ)⁻¹ = 1 := mul_inv_cancel₀ hx
  linear_combination
    ((∏ i, m (σ i)) * (∏ k : Fin (KLwIn J + 1),
          (1 - (t : ℂ) * (m (sigmaIn σ J k) * m (sigmaIn σ J (k + 1))))⁻¹) *
        (∏ k : Fin (n - KLwIn J + 1),
          (1 - (t : ℂ) * (m (sigmaOut σ J k) * m (sigmaOut σ J (k + 1))))⁻¹) *
        Qlayer m t (sigmaIn σ J) ∅ * Qlayer m t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) *
        (1 - ξ)) * hu +
    ((∏ k : Fin (KLwIn J + 1),
          (1 - (t : ℂ) * (m (sigmaIn σ J k) * m (sigmaIn σ J (k + 1))))⁻¹) *
        (∏ k : Fin (n - KLwIn J + 1),
          (1 - (t : ℂ) * (m (sigmaOut σ J k) * m (sigmaOut σ J (k + 1))))⁻¹) *
        Qlayer m t (sigmaIn σ J) ∅ * Qlayer m t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) *
        (1 - ξ) * (t : ℂ)) * hPm

end MoleculeA

/-! ## 4. Elementary facts on `m(±)` and the layers -/

section Spectral

/-- A long edge has `m(s) m(s') = m m̄ = |m|² = 1` (RBM2D `SumZeroWard_mSig_mul_of_ne`,
RBM1D `mSigma_mul_of_ne`). -/
private theorem mSigma_mul_of_ne {E : ℝ} (hE : |E| ≤ 2) {s s' : Bool} (h : s ≠ s') :
    mSigma E s * mSigma E s' = 1 := by
  have h1 : mE E * (starRingEnd ℂ) (mE E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE hE]; simp
  cases s <;> cases s' <;> simp_all [mSigma, mul_comm]

/-- Flipping every charge conjugates `m`: `m(!s) = conj m(s)`. -/
private theorem mSigma_not (E : ℝ) (s : Bool) :
    mSigma E (!s) = (starRingEnd ℂ) (mSigma E s) := by
  cases s <;> simp [mSigma]

/-- `η_t = (1 - t) Im m`. -/
private theorem etaT_eq (E t : ℝ) : Gauss.etaT E t = (1 - t) * (mE E).im := rfl

/-- `σ^{(alt)}` has `σ₀ = +` and, for even `n`, `σ_{n-1} = -`. -/
private theorem sigAlt_ends {n : ℕ} (hn : 2 ≤ n) (hev : Even n) :
    KLsigAlt n ⟨0, by omega⟩ = true ∧ KLsigAlt n ⟨n - 1, by omega⟩ = false := by
  obtain ⟨k, hk⟩ := hev
  have h : (n - 1) % 2 = 1 := by omega
  simp [KLsigAlt, h]

/-- For even `n`, `σ^{(alt)}` alternates cyclically: `σ_v ≠ σ_{v+1}` for every `v : Fin n`. -/
private theorem sigAlt_alt {n : ℕ} [NeZero n] (hev : Even n) (v : Fin n) :
    KLsigAlt n v ≠ KLsigAlt n (v + 1) := by
  obtain ⟨k, hk⟩ := hev
  have hv := v.isLt
  have hval : (v + 1 : Fin n).val = (v.val + 1) % n := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [KLsigAlt, hval]
  by_cases h : v.val + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    rcases Nat.mod_two_eq_zero_or_one v.val with h2 | h2
    · have h3 : (v.val + 1) % 2 = 1 := by omega
      simp [h2, h3]
    · have h3 : (v.val + 1) % 2 = 0 := by omega
      simp [h2, h3]
  · rw [show v.val + 1 = n by omega, Nat.mod_self]
    have h2 : v.val % 2 = 1 := by omega
    simp [h2]

/-- For even `n`, `∏_i m(σ^{(alt)}_i) = (m(+) m(-))^{n/2} = 1`
(copy of the private `KLSumZero_prod_mSigma_alt`). -/
private theorem prod_mSigma_alt {E : ℝ} (hE : |E| ≤ 2) {n : ℕ} (hev : Even n) :
    ∏ i : Fin n, mSigma E (KLsigAlt n i) = 1 := by
  have hmm : mSigma E true * mSigma E false = 1 := mSigma_mul_of_ne hE (by decide)
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
      exact hmm
  obtain ⟨j, rfl⟩ := hev
  rw [← key j]
  exact Fin.prod_univ_eq_prod_range (fun k => mSigma E (decide (k % 2 = 0))) (j + j)

end Spectral

section Layers

variable {n : ℕ}

/-- **An innermost long edge**: a long edge of `π` of smallest arc has no other edge of `π`
inside its arc (RBM2D `KBoundCut.lean:1876`, a port of RBM1D `exists_innermost`,
`SumZero.lean:814`; not in the merged `KLCut`). -/
private theorem exists_innermost {π : Finset (Fin n × Fin n)}
    (hπ : π ⊆ diagonals n) (hne : π.Nonempty) :
    ∃ J ∈ π, ∀ e ∈ π, KLArcLe e J → e = J := by
  obtain ⟨J, hJ, hmin⟩ := π.exists_min_image KLarcWidth hne
  refine ⟨J, hJ, fun e he heJ => ?_⟩
  have hJd : IsDiag n J.1 J.2 := (Finset.mem_filter.1 (hπ hJ)).2
  have hed : IsDiag n e.1 e.2 := (Finset.mem_filter.1 (hπ he)).2
  have hw := hmin e he
  obtain ⟨h1, h2⟩ := heJ
  have hJ12 := hJd.1
  have he12 := hed.1
  simp only [KLarcWidth] at hw
  rw [Fin.le_def] at h1 h2
  rw [Fin.lt_def] at hJ12 he12
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- `π ⊆ diagonals n` for the long edges of a tree (RBM2D `KBoundCut.lean:1893`). -/
private theorem Flong_subset_diagonals {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n)
    (σ : Fin n → Bool) : KLFlong F₀ σ ⊆ diagonals n :=
  (Finset.filter_subset _ _).trans (Finset.mem_powerset.1 (Finset.mem_filter.1 hF₀).1)

private theorem Alayer_eq_zero_of_empty [NeZero n] (m : Bool → ℂ) (t : ℝ)
    {σ : Fin n → Bool} {π : Finset (Fin n × Fin n)} (h : KLTSPlong n σ π = ∅) :
    Alayer m t σ π = 0 := by
  simp [Alayer, Qlayer, h]

/-- The end charges of the inside polygon of the cut at `J = (i, j)` are `σ_i` and `σ_j`. -/
private theorem sigmaIn_ends [NeZero n] {J : Fin n × Fin n}
    (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool) :
    sigmaIn σ J ⟨0, by omega⟩ = σ J.1 ∧
      sigmaIn σ J ⟨KLwIn J + 1 - 1, by omega⟩ = σ J.2 := by
  have hJ1 := J.1.isLt
  have hJ2 := J.2.isLt
  have h12 := hJd.1
  rw [Fin.lt_def] at h12
  constructor <;> (simp only [sigmaIn]; congr 1; ext; simp only [KLwIn]; omega)

/-- The end charges of the outside polygon of the cut at `J` are `σ₀` and `σ_{n-1}`. -/
private theorem sigmaOut_ends [NeZero n] {J : Fin n × Fin n}
    (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool) :
    sigmaOut σ J ⟨0, by omega⟩ = σ ⟨0, NeZero.pos n⟩ ∧
      sigmaOut σ J ⟨n - KLwIn J + 1 - 1, by omega⟩ =
        σ ⟨n - 1, by have := NeZero.pos n; omega⟩ := by
  have hJ2 := J.2.isLt
  have hJw := KLwidth_of_isDiag hJd
  have hw : KLwIn J = J.2.val - J.1.val := rfl
  constructor
  · simp only [sigmaOut]
    congr 1
  · simp only [sigmaOut]
    congr 1
    ext
    change min (KLunCol J (n - KLwIn J + 1 - 1)) (n - 1) = n - 1
    rw [KLunCol_of_gt (J := J) (by omega)]
    omega

end Layers

/-! ## 5. Flipping all charges -/

section Flip

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem Flong_not (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) :
    KLFlong F (fun v => !σ v) = KLFlong F σ := by
  unfold KLFlong
  refine filter_congr fun d _ => ?_
  change (!σ d.1) ≠ (!σ d.2) ↔ σ d.1 ≠ σ d.2
  cases σ d.1 <;> cases σ d.2 <;> simp

/-- `A(!σ, π) = conj A(σ, π)` for real `t`.  The factor `∏_i m(σ_i)` of the merged `Alayer`
goes to its conjugate (`mSigma_not`); the statement is RBM2D's. -/
private theorem Alayer_not (E t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    Alayer (mSigma E) t (fun v => !σ v) π = (starRingEnd ℂ) (Alayer (mSigma E) t σ π) := by
  have hT : KLTSPlong n (fun v => !σ v) π = KLTSPlong n σ π := by
    unfold KLTSPlong
    refine filter_congr fun F _ => ?_
    rw [Flong_not]
  unfold Alayer Qlayer edgeR
  rw [hT]
  simp only [mSigma_not, map_mul, map_prod, map_sum, map_inv₀, map_sub, map_one,
    Complex.conj_ofReal]

end Flip

/-! ## 6. The base bound (3.49) from the Ward bound `KLK_sumAll_le` -/

section Bound349

/-- **(3.49)** for `σ₀ = +`, `σ_{n-1} = -`, in closed form: `|∑_π A(σ, π)| ≤ 2^{n²} c_κ^{-2n}
η_t^{-(n-1)}`.  `A` does not depend on `d`, `g` (nor on `W`, `L`), so the bound is proved on the
lattice `Z_3^3` (`d = 3`, `g = 1`) from `KLK_sumAll_le` (T2048) at `L = 3`, `W = 1` (`W^d = 1`,
so `W^d` disappears), with `KLK_eq_sum_Kpi` (3.41) and the closed form
`∑_a K^(π) = 3^d A(σ, π)` (`sum_Kpi_closed`; RBM2D: `|Z_3²| = 9`).  The merged `KLKpi` carries
`∏ m(σ_i)`, so (3.41) at `W = 1` reads `∑_π KLKpi = KLK` (RBM2D: `∑_π Kpi = (∏ m)⁻¹ 𝒦`, and a
step `‖∏ m‖ = 1`). -/
private theorem norm_sum_Alayer_le_pm {κ : ℝ} (hκ : 0 < κ) {E : ℝ}
    (hE : |E| ≤ 2 - κ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ : Fin n → Bool) (h0 : σ ⟨0, by omega⟩ = true) (h1 : σ ⟨n - 1, by omega⟩ = false) :
    ‖∑ π ∈ (diagonals n).powerset, Alayer (mSigma E) t σ π‖ ≤
      2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (Gauss.etaT E t)⁻¹ ^ (n - 1) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hm := fun s s' => norm_mul_mSigma_lt_one hE2 ht.1 ht.2 s s'
  -- `∑_π A = (3^d)⁻¹ ∑_a ∑_π K^(π)`
  have e1 : ∑ π ∈ (diagonals n).powerset, Alayer (mSigma E) t σ π
      = ((3 : ℂ) ^ 3)⁻¹ * ∑ a : Fin n → Zd 3 3,
          ∑ π ∈ (diagonals n).powerset, KLKpi 3 3 1 (mSigma E) t σ a π := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun π _ => ?_
    rw [sum_Kpi_closed 3 3 1 (mSigma E) hm (by norm_num) σ π]
    push_cast
    field_simp
  -- `∑_π K^(π) = 𝒦` (3.41), with `W = 1`
  have e2 : ∀ a : Fin n → Zd 3 3, ∑ π ∈ (diagonals n).powerset, KLKpi 3 3 1 (mSigma E) t σ a π
      = KLK 3 3 1 1 E t (KLloopOf 3 3 σ a) := by
    intro a
    rw [KLK_eq_sum_Kpi 3 3 1 1 E t hn σ a]
    simp
  -- the fibres `a₀ = a₁`
  have e3 : ∑ a : Fin n → Zd 3 3, KLK 3 3 1 1 E t (KLloopOf 3 3 σ a)
      = ∑ a₁ : Zd 3 3, ∑ a ∈ Finset.univ.filter (fun a : Fin n → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
          KLK 3 3 1 1 E t (KLloopOf 3 3 σ a) :=
    (sum_fiberwise univ (fun a : Fin n → Zd 3 3 => a ⟨0, by omega⟩) _).symm
  have hB : ∀ a₁ : Zd 3 3,
      ‖∑ a ∈ Finset.univ.filter (fun a : Fin n → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
          KLK 3 3 1 1 E t (KLloopOf 3 3 σ a)‖
        ≤ 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (Gauss.etaT E t)⁻¹ ^ (n - 1) := by
    intro a₁
    have h := KLK_sumAll_le 3 1 κ hκ 3 1 (by norm_num) le_rfl E hE t ht n (by omega) σ h0 h1 a₁
    simpa using h
  simp_rw [e2] at e1
  rw [e1, e3, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  have hsum := (norm_sum_le _ _).trans
    (sum_le_sum fun a₁ (_ : a₁ ∈ (univ : Finset (Zd 3 3))) => hB a₁)
  rw [sum_const, card_univ, card_Zd, nsmul_eq_mul] at hsum
  have h27 : ((3 : ℝ) ^ 3)⁻¹ * (((3 ^ 3 : ℕ) : ℝ)) = 1 := by norm_num
  calc ((3 : ℝ) ^ 3)⁻¹ * ‖∑ a₁ : Zd 3 3,
        ∑ a ∈ Finset.univ.filter (fun a : Fin n → Zd 3 3 => a ⟨0, by omega⟩ = a₁),
          KLK 3 3 1 1 E t (KLloopOf 3 3 σ a)‖
      ≤ ((3 : ℝ) ^ 3)⁻¹ * (((3 ^ 3 : ℕ) : ℝ) *
          (2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (Gauss.etaT E t)⁻¹ ^ (n - 1))) := by
        gcongr
    _ = 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (Gauss.etaT E t)⁻¹ ^ (n - 1) := by
        rw [← mul_assoc, h27, one_mul]

/-- **(3.49)** for every `σ` with `σ₀ ≠ σ_{n-1}`: the case `σ₀ = -` is the conjugate of the
case `σ₀ = +` (`Alayer_not`). -/
private theorem norm_sum_Alayer_le {κ : ℝ} (hκ : 0 < κ) {E : ℝ}
    (hE : |E| ≤ 2 - κ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ : Fin n → Bool) (hσ : σ ⟨0, by omega⟩ ≠ σ ⟨n - 1, by omega⟩) :
    ‖∑ π ∈ (diagonals n).powerset, Alayer (mSigma E) t σ π‖ ≤
      2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (Gauss.etaT E t)⁻¹ ^ (n - 1) := by
  cases h0 : σ ⟨0, by omega⟩
  · have h1 : σ ⟨n - 1, by omega⟩ = true := by
      rw [h0] at hσ; cases h : σ ⟨n - 1, by omega⟩ <;> simp_all
    set σ' : Fin n → Bool := fun v => !σ v with hσ'
    have hσσ : σ = fun v => !σ' v := by funext v; simp [σ']
    have hsum : ∑ π ∈ (diagonals n).powerset, Alayer (mSigma E) t σ π
        = (starRingEnd ℂ) (∑ π ∈ (diagonals n).powerset, Alayer (mSigma E) t σ' π) := by
      rw [map_sum]
      refine sum_congr rfl fun π _ => ?_
      rw [hσσ, Alayer_not]
    rw [hsum, Complex.norm_conj]
    exact norm_sum_Alayer_le_pm hκ hE ht hn σ'
      (by simp only [σ']; rw [h0]; rfl) (by simp only [σ']; rw [h1]; rfl)
  · have h1 : σ ⟨n - 1, by omega⟩ = false := by
      rw [h0] at hσ; cases h : σ ⟨n - 1, by omega⟩ <;> simp_all
    exact norm_sum_Alayer_le_pm hκ hE ht hn σ h0 h1

end Bound349

/-! ## 7. The induction (3.50) on the class `σ₀ ≠ σ_{n-1}` -/

section Induction350

variable {E : ℝ}

/-- **(3.50)**: `|A(σ, π)| ≤ C η_t^{-(n-1)}` for every `σ` with `σ₀ ≠ σ_{n-1}` and every `π`,
in the bulk, by induction on `n` (port of RBM1D `norm_Alayer_le`).  For `π ≠ ∅` cut at an
innermost long edge (`Alayer_cut`); for `π = ∅` subtract the other layers from (3.49).  The
class `σ₀ ≠ σ_{n-1}` is closed under the cut (`sigmaIn_ends`, `sigmaOut_ends`).  At a long edge
`m(σ_i) m(σ_j) = 1`, so the prefactor `t (1 - ξ_J)` of `Alayer_cut` is `t (1 - t)`, which is
RBM2D's `ξ_J (1 - ξ_J)` at a long edge: the induction is RBM2D's. -/
private theorem norm_Alayer_le {κ : ℝ} (hκ : 0 < κ) (hEk : |E| ≤ 2 - κ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (hn3 : 3 ≤ n), n ≤ N →
      ∀ σ : Fin n → Bool, σ ⟨0, by omega⟩ ≠ σ ⟨n - 1, by omega⟩ →
      ∀ (π : Finset (Fin n × Fin n)) (t : ℝ), t ∈ Set.Ico (0 : ℝ) 1 →
        ‖Alayer (mSigma E) t σ π‖ ≤ C * (Gauss.etaT E t)⁻¹ ^ (n - 1) := by
  have hE2 : |E| ≤ 2 := by linarith
  have hE : |E| < 2 := by linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  set ι := (mE E).im with hι
  have hι0 : 0 < ι := mE_im_pos hE
  have hc0 : 0 < gapK κ := by
    unfold gapK
    refine lt_min one_pos (Real.sqrt_pos.2 ?_)
    nlinarith
  induction N with
  | zero => exact ⟨0, le_rfl, fun n _ h3 hN => by omega⟩
  | succ N ih =>
  obtain ⟨C, hC0, hC⟩ := ih
  set B : ℝ := 2 ^ ((N + 1) ^ 2) * (gapK κ)⁻¹ ^ (2 * (N + 1)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  refine ⟨C + B + (2 ^ ((N + 1) * (N + 1)) + 1) * (C * C * ι⁻¹),
    by positivity, fun n _ h3 hN σ hσ π t ht => ?_⟩
  have ht0 := ht.1
  have ht1 := ht.2
  have hη : 0 < Gauss.etaT E t := by
    rw [etaT_eq]; exact mul_pos (by linarith) hι0
  set η := Gauss.etaT E t with hηdef
  have hη' : η = (1 - t) * ι := etaT_eq E t
  have hpow0 : 0 ≤ η⁻¹ ^ (n - 1) := by positivity
  have hCC : 0 ≤ C * C * ι⁻¹ := by positivity
  rcases Nat.lt_or_ge n (N + 1) with hlt | hge
  · refine (hC n h3 (by omega) σ hσ π t ht).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) + 1) hCC
    linarith
  have hn : n = N + 1 := by omega
  -- the layers with a long edge
  have hne_bound : ∀ π : Finset (Fin n × Fin n), π.Nonempty →
      ‖Alayer (mSigma E) t σ π‖ ≤ C * C * ι⁻¹ * η⁻¹ ^ (n - 1) := by
    intro π hπne
    rcases (KLTSPlong n σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
    · rw [Alayer_eq_zero_of_empty _ _ hemp, norm_zero]; positivity
    obtain ⟨hF₀T, hπ⟩ := mem_filter.1 hF₀
    have hF₀' := KLisTSP_of_mem_TSP hF₀T
    obtain ⟨J, hJ, hinner⟩ := exists_innermost (hπ ▸ Flong_subset_diagonals hF₀T σ) hπne
    have hm := norm_mul_mSigma_lt_one hE2 ht0 ht1
    have hJd : IsDiag n J.1 J.2 := hF₀'.1 J (Flong_subset F₀ σ (hπ ▸ hJ))
    have hJlong : σ J.1 ≠ σ J.2 := (mem_Flong.1 (hπ ▸ hJ)).2
    rw [Alayer_cut (by omega) (mSigma E) hm σ hF₀T hπ hJ hinner,
      mSigma_mul_of_ne hE2 hJlong, mul_one]
    have hw := KLwidth_of_isDiag hJd
    have hw' : KLwIn J + 1 < n := by
      obtain ⟨-, -, hnot⟩ := hJd
      have := J.2.isLt
      simp only [KLwIn]
      omega
    have hwv : KLwIn J = J.2.val - J.1.val := rfl
    obtain ⟨hi0, hi1⟩ := sigmaIn_ends hJd σ
    obtain ⟨ho0, ho1⟩ := sigmaOut_ends hJd σ
    have hin := hC (KLwIn J + 1) (by omega) (by omega) (sigmaIn σ J)
      (by rw [hi0, hi1]; exact hJlong) ∅ t ht
    have hout := hC (n - KLwIn J + 1) (by omega) (by omega) (sigmaOut σ J)
      (by rw [ho0, ho1]; exact hσ) ((π.erase J).image (KLshiftOut J)) t ht
    simp only [Nat.add_sub_cancel] at hin hout
    have htn : ‖(t : ℂ)‖ = t := Complex.norm_of_nonneg ht0
    have h1t : ‖(1 : ℂ) - t‖ = 1 - t := by
      rw [show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_of_nonneg (by linarith)
    rw [norm_mul, norm_mul, norm_mul, htn, h1t]
    have hkey : (1 - t) * (η⁻¹ ^ KLwIn J * η⁻¹ ^ (n - KLwIn J)) = ι⁻¹ * η⁻¹ ^ (n - 1) := by
      have h1t0 : 1 - t ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
      have hι0' : ι ≠ 0 := hι0.ne'
      rw [← pow_add, show KLwIn J + (n - KLwIn J) = n - 1 + 1 by omega, pow_succ, hη']
      field_simp
    calc t * (1 - t) * ‖Alayer (mSigma E) t (sigmaIn σ J) ∅‖ *
          ‖Alayer (mSigma E) t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J))‖
        ≤ (1 - t) * (C * η⁻¹ ^ KLwIn J) * (C * η⁻¹ ^ (n - KLwIn J)) := by
          gcongr
          all_goals nlinarith
        _ = C * C * ((1 - t) * (η⁻¹ ^ KLwIn J * η⁻¹ ^ (n - KLwIn J))) := by ring
        _ = C * C * ι⁻¹ * η⁻¹ ^ (n - 1) := by rw [hkey]; ring
  rcases π.eq_empty_or_nonempty with rfl | hπne
  · -- the layer without long edges: (3.49) minus the others
    have hsum := norm_sum_Alayer_le hκ hEk ht h3 σ hσ
    have hmem : (∅ : Finset (Fin n × Fin n)) ∈ (diagonals n).powerset := empty_mem_powerset _
    rw [← add_sum_erase _ _ hmem] at hsum
    have hrest : ‖∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π‖
        ≤ 2 ^ ((N + 1) * (N + 1)) * (C * C * ι⁻¹ * η⁻¹ ^ (n - 1)) := by
      refine (norm_sum_le _ _).trans ?_
      refine (sum_le_sum fun π hπ => hne_bound π
        (nonempty_iff_ne_empty.2 (mem_erase.1 hπ).1)).trans ?_
      rw [sum_const, nsmul_eq_mul]
      gcongr
      have hc : ((diagonals n).powerset.erase ∅).card ≤ 2 ^ (n * n) := by
        refine (card_erase_le).trans ?_
        rw [card_powerset]
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have := card_le_univ (diagonals n)
        simpa using this
      rw [← hn]
      exact_mod_cast hc
    have htri : ‖Alayer (mSigma E) t σ ∅‖ ≤
        ‖Alayer (mSigma E) t σ ∅ +
            ∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π‖ +
          ‖∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π‖ := by
      have := norm_sub_le (Alayer (mSigma E) t σ ∅ +
        ∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π)
        (∑ π ∈ ((diagonals n).powerset).erase ∅, Alayer (mSigma E) t σ π)
      rwa [add_sub_cancel_right] at this
    have hBn : 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) = B := by rw [hn]
    rw [hBn] at hsum
    calc ‖Alayer (mSigma E) t σ ∅‖
        ≤ B * η⁻¹ ^ (n - 1) +
            2 ^ ((N + 1) * (N + 1)) * (C * C * ι⁻¹ * η⁻¹ ^ (n - 1)) := by
          linarith
      _ ≤ _ := by
          have h2 : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1)) := by positivity
          nlinarith [mul_nonneg hC0 hpow0, mul_nonneg hCC hpow0]
  · refine (hne_bound π hπne).trans ?_
    gcongr
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ ((N + 1) * (N + 1))) hCC
    linarith

end Induction350

/-! ## 8. The Lipschitz step `t → 1`

The estimates of `RBM2D/Loop/SumZero.lean` (section `Estimates`), which are private in the merged
`KLSumZero.lean`; `gapK` and `gapK_le_norm` (F3) are public there and are used directly. -/

section Lipschitz

private theorem KLSumZeroWard_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < gapK κ := by
  unfold gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

private theorem KLSumZeroWard_gapK_le_one (κ : ℝ) : gapK κ ≤ 1 := min_le_left _ _

/-- The factor `f(t) = (1 - tμ)⁻¹ - 1` is bounded by `c⁻¹`. -/
private theorem KLSumZeroWard_norm_edge_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hc : 0 < c) (hct : c ≤ ‖1 - (t : ℂ) * μ‖) :
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
private theorem KLSumZeroWard_norm_edge_sub_le {μ : ℂ} (hμ : ‖μ‖ = 1) {t c : ℝ} (ht1 : t ≤ 1)
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
private theorem KLSumZeroWard_norm_prod_sub_prod_le {ι : Type*} (s : Finset ι)
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

/-- **The Lipschitz step**: `‖Q(σ, ∅)(t) - Q(σ, ∅)(1)‖ ≤ 2^{n²} n² c_κ^{-(n²+2)} (1 - t)` on
`[0, 1)`, in the bulk (every edge of a tree of the layer `∅` joins equal charges, so its factor
is `(1 - t m(s)²)⁻¹ - 1`, with `|1 - t m(s)²| ≥ c_κ` on `[0, 1]`).  `Q` has no factor `∏ m`, so
this is RBM2D's estimate. -/
private theorem norm_Qlayer_sub_le {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} (σ : Fin n → Bool) :
    ‖Qlayer (mSigma E) t σ ∅ - Qlayer (mSigma E) 1 σ ∅‖ ≤
      2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * (gapK κ)⁻¹ ^ (n ^ 2) * (gapK κ)⁻¹ ^ 2) * (1 - t) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hc := KLSumZeroWard_gapK_pos hκ hκ2
  set c := gapK κ with hcdef
  have hc1 : 1 ≤ c⁻¹ := one_le_inv₀ hc |>.2 (KLSumZeroWard_gapK_le_one κ)
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hμ : ∀ s : Bool, ‖mSigma E s * mSigma E s‖ = 1 := fun s => by
    rw [norm_mul, norm_mSigma hE2]; norm_num
  -- one tree
  have hF : ∀ F ∈ KLTSPlong n σ ∅,
      ‖∏ e ∈ F, edgeR (mSigma E) t (σ e.1) (σ e.2) - ∏ e ∈ F, edgeR (mSigma E) 1 (σ e.1) (σ e.2)‖
        ≤ (n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t) := by
    intro F hFm
    obtain ⟨-, hFl⟩ := mem_filter.1 hFm
    have hsame : ∀ e ∈ F, σ e.2 = σ e.1 := by
      intro e he
      by_contra h
      have : e ∈ KLFlong F σ := mem_filter.2 ⟨he, Ne.symm h⟩
      rw [hFl] at this
      exact notMem_empty e this
    have htel := KLSumZeroWard_norm_prod_sub_prod_le F
      (fun e => edgeR (mSigma E) t (σ e.1) (σ e.2))
      (fun e => edgeR (mSigma E) 1 (σ e.1) (σ e.2)) hc1
      (by positivity : 0 ≤ (1 - t) * c⁻¹ ^ 2)
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact KLSumZeroWard_norm_edge_le (hμ _) ht.1 ht.2.le hc
          (gapK_le_norm hκ hE ht.1 _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        exact KLSumZeroWard_norm_edge_le (hμ _) zero_le_one le_rfl hc
          (gapK_le_norm hκ hE zero_le_one _))
      (fun e he => by
        simp only [edgeR, hsame e he]
        have h1 := gapK_le_norm hκ hE zero_le_one (σ e.1)
        rw [Complex.ofReal_one, one_mul] at h1 ⊢
        exact KLSumZeroWard_norm_edge_sub_le (hμ _) ht.2.le hc
          (gapK_le_norm hκ hE ht.1 _) h1)
    refine htel.trans ?_
    have hkn' : F.card ≤ n ^ 2 := by
      have := card_le_univ F
      simpa [sq] using this
    have hkn : (F.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hkn'
    have hpow : c⁻¹ ^ F.card ≤ c⁻¹ ^ (n ^ 2) := pow_le_pow_right₀ hc1 hkn'
    calc (F.card : ℝ) * c⁻¹ ^ F.card * ((1 - t) * c⁻¹ ^ 2)
        = (F.card : ℝ) * c⁻¹ ^ F.card * c⁻¹ ^ 2 * (1 - t) := by ring
      _ ≤ (n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t) := by gcongr
  have hdiff : Qlayer (mSigma E) t σ ∅ - Qlayer (mSigma E) 1 σ ∅ = ∑ F ∈ KLTSPlong n σ ∅,
      (∏ e ∈ F, edgeR (mSigma E) t (σ e.1) (σ e.2) -
        ∏ e ∈ F, edgeR (mSigma E) 1 (σ e.1) (σ e.2)) := by
    rw [sum_sub_distrib]
    rfl
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum hF).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard : ((KLTSPlong n σ ∅).card : ℝ) ≤ 2 ^ (n ^ 2) := by
    have h : (KLTSPlong n σ ∅).card ≤ 2 ^ (n ^ 2) := by
      calc (KLTSPlong n σ ∅).card ≤ (TSP n).card := card_filter_le _ _
        _ ≤ (diagonals n).powerset.card := card_filter_le _ _
        _ = 2 ^ (diagonals n).card := card_powerset _
        _ ≤ 2 ^ (n ^ 2) := by
            refine Nat.pow_le_pow_right (by norm_num) ?_
            calc (diagonals n).card ≤ (univ : Finset (Fin n × Fin n)).card := card_le_univ _
              _ = n ^ 2 := by simp [sq]
    exact_mod_cast h
  have h0 : 0 ≤ (n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t) := by positivity
  calc ((KLTSPlong n σ ∅).card : ℝ) * ((n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t))
      ≤ 2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2 * (1 - t)) :=
        mul_le_mul_of_nonneg_right hcard h0
    _ = 2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * c⁻¹ ^ (n ^ 2) * c⁻¹ ^ 2) * (1 - t) := by ring

end Lipschitz

/-! ## 9. Target 1: `R_n(1) = 0` -/

section Target1

/-- **Target 1, [YY_25] Lemma 3.10 (2) in closed form (`R_n(1) = 0`)**: for every even `n ≥ 4`
and every `|E| < 2`, the single-molecule layer of the alternating loop vanishes at `t = 1`:
`Q(σ^{(alt)}, ∅)|_{t=1} = ∑_{F ∈ T_SP(σ^{(alt)}, ∅)} ∏_{e ∈ F} ((1 - m_e²)⁻¹ - 1) = 0`.
Proof (RBM2D `SumZeroWard.lean:1921`): (3.51) `Q(t) = (1 - t)^n A(σ^{(alt)}, ∅)(t)`, using
`∏ m(σ^{(alt)}_i) = 1` for the factor `∏ m` of the merged `Alayer`; (3.50)
`|A| ≤ C η_t^{-(n-1)}`, so `|Q(t)| ≤ C (Im m)^{-(n-1)} (1 - t)`; with the Lipschitz step,
`|Q(1)| ≤ K (1 - t)` for all `t ∈ [0, 1)`.  `Q` is independent of `d`, `g`, `L`, `W`. -/
theorem Qlayer_alt_one_eq_zero :
    ∀ E : ℝ, |E| < 2 → ∀ (n : ℕ) [NeZero n], 4 ≤ n → Even n →
      Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0 := by
  intro E hE n _ hn hev
  set κ : ℝ := 2 - |E| with hκdef
  have hκ : 0 < κ := by linarith
  have hEk : |E| ≤ 2 - κ := by linarith
  have hE2 : |E| ≤ 2 := hE.le
  set ι := (mE E).im with hι
  have hι0 : 0 < ι := mE_im_pos hE
  obtain ⟨C, hC0, hC⟩ := norm_Alayer_le hκ hEk n
  obtain ⟨he0, he1⟩ := sigAlt_ends (by omega : 2 ≤ n) hev
  have hends : KLsigAlt n ⟨0, by omega⟩ ≠ KLsigAlt n ⟨n - 1, by omega⟩ := by
    rw [he0, he1]; decide
  -- (3.51) and (3.50): `|Q(t)| ≤ C ι^{-(n-1)} (1 - t)`
  have hQt : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖Qlayer (mSigma E) t (KLsigAlt n) ∅‖ ≤ C * ι⁻¹ ^ (n - 1) * (1 - t) := by
    intro t ht
    have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
    have hξ : ∀ v : Fin n,
        (1 : ℂ) - t * (mSigma E (KLsigAlt n v) * mSigma E (KLsigAlt n (v + 1)))
          = ((1 - t : ℝ) : ℂ) := by
      intro v
      rw [mSigma_mul_of_ne hE2 (sigAlt_alt hev v)]
      push_cast; ring
    have hQ : Qlayer (mSigma E) t (KLsigAlt n) ∅ =
        ((1 - t : ℝ) : ℂ) ^ n * Alayer (mSigma E) t (KLsigAlt n) ∅ := by
      unfold Alayer
      rw [prod_mSigma_alt hE2 hev, one_mul]
      simp_rw [hξ]
      rw [prod_const, card_univ, Fintype.card_fin, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ (by exact_mod_cast h1t.ne'), one_pow, one_mul]
    have hA := hC n (by omega) le_rfl (KLsigAlt n) hends ∅ t ht
    rw [hQ, norm_mul, norm_pow, Complex.norm_of_nonneg h1t.le]
    have hη : Gauss.etaT E t = (1 - t) * ι := etaT_eq E t
    rw [hη] at hA
    calc (1 - t) ^ n * ‖Alayer (mSigma E) t (KLsigAlt n) ∅‖
        ≤ (1 - t) ^ n * (C * ((1 - t) * ι)⁻¹ ^ (n - 1)) := by gcongr
      _ = C * ι⁻¹ ^ (n - 1) * (1 - t) := by
          obtain ⟨p, hp⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
          rw [hp, Nat.add_sub_cancel, mul_inv, mul_pow, inv_pow, pow_succ]
          have h1 : (1 - t) ^ p ≠ 0 := pow_ne_zero _ h1t.ne'
          field_simp
  -- the limit `t → 1`
  set K : ℝ := 2 ^ (n ^ 2) * ((n : ℝ) ^ 2 * (gapK κ)⁻¹ ^ (n ^ 2) * (gapK κ)⁻¹ ^ 2)
    with hKdef
  set M : ℝ := C * ι⁻¹ ^ (n - 1) + K with hMdef
  have hK0 : 0 ≤ K := by
    have := KLSumZeroWard_gapK_pos hκ (by linarith [abs_nonneg E])
    positivity
  have hM0 : 0 ≤ M := by positivity
  have hQ1 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖Qlayer (mSigma E) 1 (KLsigAlt n) ∅‖ ≤ M * (1 - t) := by
    intro t ht
    have h1 := hQt t ht
    have h2 := norm_Qlayer_sub_le hκ hEk ht (KLsigAlt n)
    have h3 := norm_sub_le (Qlayer (mSigma E) t (KLsigAlt n) ∅)
      (Qlayer (mSigma E) t (KLsigAlt n) ∅ - Qlayer (mSigma E) 1 (KLsigAlt n) ∅)
    rw [sub_sub_cancel] at h3
    calc ‖Qlayer (mSigma E) 1 (KLsigAlt n) ∅‖
        ≤ C * ι⁻¹ ^ (n - 1) * (1 - t) + K * (1 - t) := by linarith
      _ = M * (1 - t) := by ring
  by_contra hne
  have hx : 0 < ‖Qlayer (mSigma E) 1 (KLsigAlt n) ∅‖ := norm_pos_iff.2 hne
  set x := ‖Qlayer (mSigma E) 1 (KLsigAlt n) ∅‖ with hxdef
  set δ : ℝ := min 1 (x / (2 * (M + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδx : δ ≤ x / (2 * (M + 1)) := min_le_right _ _
  have h := hQ1 (1 - δ) ⟨by linarith, by linarith⟩
  rw [sub_sub_cancel] at h
  have hMδ : M * δ ≤ M * (x / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hδx hM0
  have hlt : M * (x / (2 * (M + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end Target1

/-! ## 10. Target 2: the signed sum-zero bound `(eq:Sigma-empty-sum-zero)`, first estimate -/

section Target2

variable (d : ℕ) (g : ℝ)

/-- **The signed sum-zero bound `(eq:Sigma-empty-sum-zero)`, first estimate**
(RBM2D `SigmaPi_alt_sumZero_le`, `SumZeroWard.lean:2002`): the conditional adapter
`SigmaPi_alt_sumZero_le_of_Qlayer_one` (KL7a, T2043) with its hypothesis
`Q(σ^{(alt)}, ∅)|_{t=1} = 0` discharged by `Qlayer_alt_one_eq_zero`.  The constant is explicit
and the bulk `|E| ≤ 2 - κ` is assumed, as in RBM2D (paper-delta T2004a-11 of RBM2D). -/
theorem KLSigmaPi_alt_sumZero_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Zd d L,
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ ⟨0, by omega⟩ = d₁),
          KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ‖
        ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t := by
  intro κ hκ L _ hL E hE t ht n _ hn hev d₁
  have hE2 : |E| < 2 := by linarith
  exact SigmaPi_alt_sumZero_le_of_Qlayer_one d g κ hκ L hL E hE t ht n hn hev
    (Qlayer_alt_one_eq_zero E hE2 n hn hev) d₁

end Target2

/-! ## 11. The compiled instances

Target 1 at `(E, n) = (0, 4)` and `(1, 6)`; target 2 at `κ = 1`, `d = 3`, `L = 3` (`27` sites),
`g = 1/2`, `E = 0`, `t = 1/2`, `n = 4` (RBM2D's Check 2 in `d = 3`) and at the bulk edge
`E = 1 = 2 - κ`, `n = 6`.  Every deterministic hypothesis is discharged; nothing is left.
Nondegeneracy: `Q(σ^{(alt)}, ∅)` is `1` at `t = 0` (only the empty tree survives) and `0` at
`t = 1` (target 1), so the vanishing at `t = 1` is a cancellation, not `Q ≡ 0`. -/

section Instances

/-- `Q(σ, ∅)(0) = 1`: at `t = 0` every internal edge factor `(1 - 0)⁻¹ - 1` vanishes and only the
empty tree, which lies in the layer `∅`, contributes. -/
theorem KLSumZeroWard_Qlayer_zero (m : Bool → ℂ) {n : ℕ} (σ : Fin n → Bool) :
    Qlayer m 0 σ ∅ = 1 := by
  unfold Qlayer
  rw [sum_eq_single ∅]
  · simp
  · intro F _ hne
    obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hne
    exact prod_eq_zero he (by simp [edgeR])
  · intro h
    exact absurd (mem_filter.2 ⟨empty_mem_TSP n, by simp [KLFlong]⟩) h

/-- **Instance of `Qlayer_alt_one_eq_zero`** at `E = 0`, `n = 4` (`|0| < 2`, `4 ≤ 4`, `Even 4`):
`m(+) = i`; the layer `∅` has `3` trees (`KLSumZeroWard_inst_card`).  The direct computation of
the same identity is `KLSumZero_inst_Qlayer_one` (KL7a). -/
theorem KLSumZeroWard_inst_Q_four : Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅ = 0 :=
  Qlayer_alt_one_eq_zero 0 (by norm_num) 4 le_rfl (by decide)

/-- **Instance of `Qlayer_alt_one_eq_zero`** at `E = 1`, `n = 6` (`|1| < 2`, `4 ≤ 6`, `Even 6`):
`m(+) = (-1 + i√3)/2`; `18` of the `45` trees of the hexagon lie in the layer `∅`
(`KLSumZeroWard_inst_card`). -/
theorem KLSumZeroWard_inst_Q_six : Qlayer (mSigma 1) 1 (KLsigAlt 6) ∅ = 0 :=
  Qlayer_alt_one_eq_zero 1 (by norm_num) 6 (by norm_num) (by decide)

/-- Nondegeneracy of the instance `(E, n) = (0, 4)`: `Q(0) = 1 ≠ 0 = Q(1)`. -/
theorem KLSumZeroWard_inst_Q_four_nondeg :
    Qlayer (mSigma 0) 0 (KLsigAlt 4) ∅ ≠ Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅ := by
  rw [KLSumZeroWard_Qlayer_zero, KLSumZeroWard_inst_Q_four]
  exact one_ne_zero

/-- Nondegeneracy of the instance `(E, n) = (1, 6)`: `Q(0) = 1 ≠ 0 = Q(1)`. -/
theorem KLSumZeroWard_inst_Q_six_nondeg :
    Qlayer (mSigma 1) 0 (KLsigAlt 6) ∅ ≠ Qlayer (mSigma 1) 1 (KLsigAlt 6) ∅ := by
  rw [KLSumZeroWard_Qlayer_zero, KLSumZeroWard_inst_Q_six]
  exact one_ne_zero

set_option maxRecDepth 100000 in
/-- The layer `∅` of `σ^{(alt)}` has `3` trees for `n = 4` and `18` of the `45` trees of the
hexagon for `n = 6`: the instances of target 1 are cancellations of `3`, resp. `18` terms. -/
theorem KLSumZeroWard_inst_card :
    (KLTSPlong 4 (KLsigAlt 4) ∅).card = 3 ∧ (TSP 6).card = 45 ∧
      (KLTSPlong 6 (KLsigAlt 6) ∅).card = 18 :=
  ⟨by decide, by decide, by decide⟩

/-- **Instance of `KLSigmaPi_alt_sumZero_le`** (RBM2D's Check 2 in `d = 3`): `κ = 1`, `d = 3`,
`L = 3`, `g = 1/2`, `E = 0`, `t = 1/2`, `n = 4`, every `d₁` (in particular `d₁ = 0`). -/
theorem KLSumZeroWard_inst_bound (d₁ : Zd 3 3) :
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
        KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ‖
      ≤ 2 ^ (4 ^ 2) * ((4 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 4 * (2 / Real.sqrt (1 * (4 - 1)))
          * Gauss.etaT 0 (1 / 2) :=
  KLSigmaPi_alt_sumZero_le 3 (1 / 2) 1 one_pos 3 le_rfl 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 le_rfl (by decide) d₁

/-- The instance at `d₁ = 0`, as in the ticket. -/
theorem KLSumZeroWard_inst_bound_zero :
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = 0),
        KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ‖
      ≤ 2 ^ (4 ^ 2) * ((4 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 4 * (2 / Real.sqrt (1 * (4 - 1)))
          * Gauss.etaT 0 (1 / 2) :=
  KLSumZeroWard_inst_bound 0

/-- The left side of the instance is `1/3 ≠ 0` for every `d₁` (the bound is not `0 ≤ B`):
`Q(σ^{(alt)}, ∅)(1/2) = 1 + 2((1 + 1/2)⁻¹ - 1) = 1/3` (KL7a, `KLSumZero_inst_slice_alt`). -/
theorem KLSumZeroWard_inst_bound_lhs (d₁ : Zd 3 3) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
      KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ = 1 / 3 :=
  KLSumZero_inst_slice_alt d₁

/-- **Instance of `KLSigmaPi_alt_sumZero_le`** at the bulk edge `E = 1 = 2 - κ` (`κ = 1`), `n = 6`,
`d = 3`, `L = 3`, `g = 1/2`, `t = 1/2`, every `d₁`. -/
theorem KLSumZeroWard_inst_bound_six (d₁ : Zd 3 3) :
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 6 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
        KLSigmaPi 3 3 (1 / 2) (mSigma 1) (1 / 2) (KLsigAlt 6) ∅ δ‖
      ≤ 2 ^ (6 ^ 2) * ((6 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 6 * (2 / Real.sqrt (1 * (4 - 1)))
          * Gauss.etaT 1 (1 / 2) :=
  KLSigmaPi_alt_sumZero_le 3 (1 / 2) 1 one_pos 3 le_rfl 1 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 6 (by norm_num) (by decide) d₁

end Instances

end RBM.Loop
