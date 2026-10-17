/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.DecayLoopA
import RBM3D.Induction.KDecay
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.KLWard

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# S3-19 (ticket T2136): `(eq:Ward_typeP)` and `(y27kasdfg)`, the pins `STWardTypePPin` and `STB45Pin`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `(eq:Ward_typeP)` `3_5:1264`,
`(jywiiwsoks)` `3_5:1271`, `(y27kasdfg)` `3_5:1692`, `(A5)` `3_5:1698`, `(A4)` `3_5:1702`; Ward's identities
`lem_WI_K` `1_2:1034-1042`; fast decay `lem_decayLoop` `3_5:1126`.  Namespace `RBM.Gauss.Sizes`.

Targets (`Step34Pins.lean:576, 579`): `stWardTypePPin_holds : STWardTypePPin d`,
`stB45Pin_holds : STB45Pin d`, case (i): for alternating `σ`, uniformly in `u ∈ [s,t]`,
`[𝒫∘(𝓛-𝒦)_{u,σ}] ϑ_u ≺ (W^{-d}B_{u,0})^{m+1} X` and `‖ℬ₄‖ + ‖ℬ₅‖ ≺ η_u⁻¹ (W^{-d}B_{u,0})^{m+1} X`.
Both come from `B45_pins`, from the hypotheses `STStep2Concl` (only its part `STGdecayW` is used), `Ξ̂ ≺ X` and
`STMollifierProps` (any real `C, c`); `STKbound`, `STKward`, `STLK`, `STConStInd` of `STIngR` are not used.

## Proof (the route of RBM2D `Induction/B45.lean`, header, with the `d ≥ 3` counts)

* §1 Ward step (`(WI_calL)`, `lem_WI_K`): for alternating `σ` the last label is `¬σ_0`, so Ward's
  identity at the last label (`B45_loopL_ward`, `KLK_ward`) gives
  `Σ_x (𝓛-𝒦)^{(m+2)}_{σ,(a',x)} = (2iW^dη)⁻¹ ((𝓛-𝒦)^{(m+1)}_{σ⁺,a'} - (𝓛-𝒦)^{(m+1)}_{σ⁻,a'})`
  (`B45_ward_fin`); no rotation is needed.
* §2 window count (`B45_Psum_le`, `B45_Psum_LK_le`): near entries (`diam_∞ a' < R`) number
  `((2R+2)^d)^m`, far entries at most `(L^d)^m`.
* §3 far entries uniformly in `u` (`B45_far`): the deterministic chain of `lem_decayLoop`
  (copied from `DecayLoopA.lean`, which is per time) is run pathwise on the good event of the uniform
  decay input `STGdecayW`.
* §4 exponents (`B45_scale`, `B45_scales`, `B45_master_real`): at `d ≥ 3` the powers of `ℓ` do **not** cancel
  as in RBM2D (`ℓ^{2+2(k-2)-2(k-1)} = 1`): `(W^dη)⁻¹ ℓ^{-d}` is absorbed by `2Γ W^{-d}B_{u,0}`,
  `Γ = 2/√κ`, because `(ℓ_u^d (1-u))⁻¹ ≤ 2 B_{u,0}` for every `u < 1` (`d ≥ 2`; the condition
  `1 - u ≥ g²/L²` of case (i) is not needed for this inequality).
* §5 the mollifier (`B45_vth_sup`): `|ϑ| ≤ C(e^{|c|md/2} + 2/(dm) + 2 max(0,-log g)) (ℓ^d)^{-m}` for every real
  `c`.  For `c ≥ 0` the factor `exp(-cS/ℓ)` of `STMollifierProps` is `≤ 1`; for `c < 0` it is controlled
  at the later time `1 - g²/L²` and transported back by the derivative bound (`B45_cmp`), at the cost
  `log(1/g²) ≤ log N`, absorbed by `N^{τ}`.
* §6 `ℬ₄` (`B45_B4_le`, `QopAlgebra_commutator_ThetaN`): `‖Θ‖_{∞→∞} ≤ (m+1)(1-u)⁻¹` and
  `‖𝒫Θ𝒜‖ ≤ (m+1)(1-u)⁻¹‖𝒫𝒜‖`; `ℬ₅` by `‖∂_uϑ‖ ≤ C(1-u)⁻¹ ℓ^{-dm}` and `(1-u)⁻¹ ≤ η⁻¹`.
* §7 assembly (`B45_det`, `B45_det2`, `B45_prec_assemble`, `B45_key`, `B45_pins`): the union bound of the two
  sources (`Ξ̂ ≺ X`, far entries), `τ₁ = min(τ/6, 1/4)`; with the Lean `m` of `B45_pins` (pin `m` minus one)
  the window exponent is `τ₁/(m+1)` and `D' = (2m+4)/𝔠`.
* §8 compiled nonempty instances at `d = 3` (`sz0`, `flow_z0`, `m = 1, 3`, the merged mollifier).

## Ports (read-only sources, copied here as `private` `B45_*` helpers)

From merged RBM3D files: `DecayLoopA.lean:118-701` (deterministic steps of `lem_decayLoop`, merge `6179d8c`);
`NewPQ.lean:168-253` (`npq_loopL_eq_prod`, `npq_Gres_conj`, `npq_loopL_conj`, `npq_loopL_ward`, merge `f28fd9c`);
`QopNorm.lean:36-169` (`qn_card_zball`, `qn_card_ball`, `qn_card_pi`, `qn_Psum_le`, merge `eb6d67a`, with `zdistD`
replaced by `zdistInf` and `‖𝒜‖` by an entry bound); `QopAlgebra.lean:714-781` (`qa_slot_zero`, `qa_slot_succ`,
merge `6b2494e`).  RBM2D `Induction/B45.lean` (read at `9e0f275`, header) is followed in structure only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM

section B45Loops

open RBM.Gauss RBM.Loop

variable {d L W : ℕ} [NeZero L]

private theorem B45_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : LoopIdx (Zd d L)) :
    loopL d L W H z I
      = Matrix.trace (((I.σ.zip I.a).map fun p => Gres H z p.1 * Eblk d L W p.2).prod) := by
  have hfold : ∀ l : List (Bool × Zd d L),
      l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1
        = (l.map fun p => Gres H z p.1 * Eblk d L W p.2).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  unfold loopL
  rw [hfold]

private theorem B45_Gres_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ)
    (s : Bool) : Gres H ((starRingEnd ℂ) z) (!s) = Gres H z s := by
  cases s <;> simp [Gres]

/-- `𝓛_{z̄, (¬σ), a} = 𝓛_{z, σ, a}`. -/
private theorem B45_loopL_conj (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (σ : List Bool)
    (a : List (Zd d L)) :
    loopL d L W H ((starRingEnd ℂ) z) ⟨σ.map not, a⟩ = loopL d L W H z ⟨σ, a⟩ := by
  rw [B45_loopL_eq_prod, B45_loopL_eq_prod]
  congr 2
  simp only [List.zip_map_left, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp [B45_Gres_conj]

/-- **`(WI_calL)` at the last index, both charge orders**. -/
private theorem B45_loopL_ward [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : Bool) (μ : List Bool)
    (a : List (Zd d L)) (ha : a.length = μ.length + 1) :
    ∑ x : Zd d L, loopL d L W H z ⟨s :: μ ++ [!s], a ++ [x]⟩
      = (2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ))⁻¹ *
          (loopL d L W H z ⟨true :: μ, a⟩ - loopL d L W H z ⟨false :: μ, a⟩) := by
  obtain ⟨x0, a', rfl⟩ : ∃ x0 a', a = x0 :: a' := by
    cases a with
    | nil => simp at ha
    | cons x0 a' => exact ⟨x0, a', rfl⟩
  have hμ : μ.length = a'.length := by simpa using ha.symm
  have hz1 : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hz2 : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    Ind.isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz)
  cases s
  · -- `s = -`: the identity at `z̄`
    have hz3 : IsUnit (H - (starRingEnd ℂ) ((starRingEnd ℂ) z) •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by rwa [Complex.conj_conj]
    have h' := sum_gloop_ward_last_div d L W (z := (starRingEnd ℂ) z) hz2 hz3
      (by simpa using hz) (μ.map not) x0 a' (by simpa using hμ)
    have hA : ∀ x : Zd d L, loopL d L W H z ⟨false :: μ ++ [!false], x0 :: a' ++ [x]⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨true :: μ.map not ++ [false], x0 :: a' ++ [x]⟩ := by
      intro x
      have := B45_loopL_conj H z (false :: μ ++ [!false]) (x0 :: a' ++ [x])
      simpa [List.map_append] using this.symm
    have hB : loopL d L W H z ⟨true :: μ, x0 :: a'⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨false :: μ.map not, x0 :: a'⟩ := by
      have := B45_loopL_conj H z (true :: μ) (x0 :: a')
      simpa using this.symm
    have hC : loopL d L W H z ⟨false :: μ, x0 :: a'⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨true :: μ.map not, x0 :: a'⟩ := by
      have := B45_loopL_conj H z (false :: μ) (x0 :: a')
      simpa using this.symm
    simp only [hA]
    rw [h', hB, hC, Complex.conj_im, Complex.ofReal_neg, div_eq_inv_mul]
    have hne : (2 * Complex.I * (W : ℂ) ^ d * -(z.im : ℂ)) = -(2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ)) := by
      ring
    rw [hne, inv_neg]
    ring
  · have h' := sum_gloop_ward_last_div d L W hz1 hz2 hz μ x0 a' hμ
    simp only [List.cons_append, Bool.not_true] at h' ⊢
    rw [h', div_eq_inv_mul]

end B45Loops

end RBM

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The sign vector `(b, σ_1, …, σ_{m})` of length `m + 1` obtained from `σ : Fin (m+2) → Bool` by
replacing `σ_0` by `b` and dropping the last sign. -/
def B45_sgnCons {m : ℕ} (b : Bool) (σ : Fin (m + 2) → Bool) : Fin (m + 1) → Bool :=
  Fin.cons b (fun i : Fin m => σ (Fin.succ (Fin.castSucc i)))

theorem B45_ofFn_sigma {m : ℕ} (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) :
    List.ofFn σ = σ 0 :: List.ofFn (fun i : Fin m => σ (Fin.succ (Fin.castSucc i))) ++ [!σ 0] := by
  rw [List.ofFn_succ, List.ofFn_succ' (fun i : Fin (m + 1) => σ (Fin.succ i))]
  simp [Fin.succ_last, hσ]

theorem B45_ofFn_sgnCons {m : ℕ} (b : Bool) (σ : Fin (m + 2) → Bool) :
    List.ofFn (B45_sgnCons b σ) = b :: List.ofFn (fun i : Fin m => σ (Fin.succ (Fin.castSucc i))) := by
  rw [B45_sgnCons, List.ofFn_succ]
  simp

theorem B45_ofFn_snoc {α : Type*} {m : ℕ} (a' : Fin (m + 1) → α) (x : α) :
    List.ofFn (Fin.snoc (α := fun _ => α) a' x) = List.ofFn a' ++ [x] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

theorem B45_Lloop_eq (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    Lloop sz n E u σ a ω = loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω)) (zt E u) ⟨List.ofFn σ, List.ofFn a⟩ :=
  loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a

theorem B45_STKloop_eq (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    STKloop sz n E u σ a = KLK d (sz.L n) (sz.lam n) (sz.W n) E u ⟨List.ofFn σ, List.ofFn a⟩ := rfl

/-- **Ward's identities at the last index** for `𝓛 - 𝒦` (`lem_WI_K`, `(WI_calL)`), alternating `σ`
(`σ_last = ¬σ_0`): `Σ_x (𝓛-𝒦)^{(m+2)}_{σ,(a',x)} = (2iW^d η)⁻¹ ((𝓛-𝒦)^{(m+1)}_{σ⁺,a'} - (𝓛-𝒦)^{(m+1)}_{σ⁻,a'})`. -/
theorem B45_ward_fin (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz.SeqΩ)
    {m : ℕ} (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
    (a' : Fin (m + 1) → Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), STLKtensor sz n E u ω σ (Fin.snoc (α := fun _ => Zd d (sz.L n)) a' x) =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (STLKtensor sz n E u ω (B45_sgnCons true σ) a' - STLKtensor sz n E u ω (B45_sgnCons false σ) a') := by
  have hL3 := sz.three_le_L n
  have hW1 := sz.W_pos n
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hzim : (zt E u).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
  have hH : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω)).IsHermitian :=
    (Sizes.seqHflow_isHermitian sz n u ω).submatrix _
  set μ : List Bool := List.ofFn (fun i : Fin m => σ (Fin.succ (Fin.castSucc i))) with hμ
  have hlen : (List.ofFn a').length = μ.length + 1 := by simp [hμ]
  have hlist := B45_ofFn_sigma σ hσ
  have hLw := B45_loopL_ward (W := sz.W n) hH hzim (σ 0) μ (List.ofFn a') hlen
  have hKw := KLK_ward d (sz.L n) (sz.W n) (sz.lam n) E hL3 hW1 hE u hu0 hu1 (σ 0) μ (List.ofFn a') hlen
  simp only [STLKtensor, Finset.sum_sub_distrib]
  simp only [B45_Lloop_eq, B45_STKloop_eq, B45_ofFn_snoc, hlist, B45_ofFn_sgnCons, hμ.symm]
  rw [hLw, hKw, ← etaT_eq_zt_im]
  ring
end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## Counting and the window split of `𝒫` -/

/-- The cyclic ball: `#{z : ZMod L | zdist L z < R} ≤ 2R + 2` (port of `QopNorm.qn_card_zball`). -/
private theorem B45_card_zball (L : ℕ) [NeZero L] {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R).card : ℝ) ≤ 2 * R + 2 := by
  set n := ⌈R⌉₊ with hn
  have hsub : (Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R) ⊆
      (Finset.range n).image (fun k : ℕ => (k : ZMod L)) ∪
        (Finset.range n).image (fun k : ℕ => -(k : ZMod L)) := by
    intro z hz
    have hz' : (zdist L z : ℝ) < R := (Finset.mem_filter.1 hz).2
    have hv : z.val ≤ L := (ZMod.val_lt z).le
    simp only [zdist] at hz'
    rcases le_total z.val (L - z.val) with h | h
    · rw [min_eq_left h] at hz'
      have : z.val < n := Nat.lt_ceil.2 hz'
      exact Finset.mem_union_left _
        (Finset.mem_image.2 ⟨z.val, Finset.mem_range.2 this, ZMod.natCast_zmod_val z⟩)
    · rw [min_eq_right h] at hz'
      have : L - z.val < n := Nat.lt_ceil.2 hz'
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨L - z.val, Finset.mem_range.2 this, ?_⟩)
      rw [Nat.cast_sub hv, ZMod.natCast_self, ZMod.natCast_zmod_val]
      simp
  have hcard : (Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R).card ≤ n + n := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ n + n := by
        gcongr
        · exact Finset.card_image_le.trans (by simp)
        · exact Finset.card_image_le.trans (by simp)
  have hnR : (n : ℝ) < R + 1 := Nat.ceil_lt_add_one hR
  have : ((Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R).card : ℝ) ≤ (n : ℝ) + n := by
    exact_mod_cast hcard
  linarith

/-- The `ℓ^∞` ball of radius `R` about `c` in `Z_L^d` has at most `(2R + 2)^d` points. -/
private theorem B45_card_ball (d L : ℕ) [NeZero L] (c : Zd d L) {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.univ.filter fun x : Zd d L => (zdistInf d L (x - c) : ℝ) < R).card : ℝ) ≤ (2 * R + 2) ^ d := by
  set Z := Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R with hZ
  have hsub : (Finset.univ.filter fun x : Zd d L => (zdistInf d L (x - c) : ℝ) < R) ⊆
      Fintype.piFinset (fun j : Fin d => Z.image (fun z => z + c j)) := by
    intro x hx
    have hx' : (zdistInf d L (x - c) : ℝ) < R := (Finset.mem_filter.1 hx).2
    rw [Fintype.mem_piFinset]
    intro j
    refine Finset.mem_image.2 ⟨x j - c j, ?_, by ring⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_lt ?_ hx'⟩
    have : zdist L (x j - c j) ≤ zdistInf d L (x - c) :=
      Finset.le_sup (f := fun i => zdist L ((x - c) i)) (Finset.mem_univ j)
    exact_mod_cast this
  have h1 := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h1
  have h2 : (((Finset.univ.filter fun x : Zd d L => (zdistInf d L (x - c) : ℝ) < R).card : ℕ) : ℝ) ≤
      ∏ j : Fin d, ((Z.image (fun z => z + c j)).card : ℝ) := by
    exact_mod_cast h1
  refine h2.trans ?_
  calc ∏ j : Fin d, ((Z.image (fun z => z + c j)).card : ℝ) ≤ ∏ _j : Fin d, (2 * R + 2) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity)
          (fun j _ => by
            have := (Nat.cast_le (α := ℝ)).2 (Finset.card_image_le (s := Z) (f := fun z => z + c j))
            exact this.trans (B45_card_zball L hR))
    _ = (2 * R + 2) ^ d := by simp

/-- The tensors with first index `a₁` and the other indices in `B` number `|B|^m`. -/
private theorem B45_card_pi (d L m : ℕ) [NeZero L] (a₁ : Zd d L) (B : Finset (Zd d L)) :
    (Fintype.piFinset (fun i : Fin (m + 1) => if i = 0 then ({a₁} : Finset (Zd d L)) else B)).card
      = B.card ^ m := by
  rw [Fintype.card_piFinset, Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero]

/-- `|b_i - b_0|_∞ ≤ diam_∞ b`. -/
private theorem B45_zdistInf_le_diam {d L k : ℕ} [NeZero L] (b : Fin k → Zd d L) (i j : Fin k) :
    zdistInf d L (b i - b j) ≤ STdiamInf b :=
  Finset.le_sup (f := fun p : Fin k × Fin k => zdistInf d L (b p.1 - b p.2)) (Finset.mem_univ (i, j))

/-- **`𝒫𝒜` split into the near and the far part.**  If `‖𝒜_b‖ ≤ Y` for all `b` and `‖𝒜_b‖ ≤ F` whenever
`b₀ = a₁` and `diam_∞ b ≥ R`, then `|(𝒫𝒜)_{a₁}| ≤ ((2R+2)^d)^m Y + (L^d)^m F`. -/
theorem B45_Psum_le {d L m : ℕ} [NeZero L] (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L)
    {R Y F : ℝ} (hR : 0 ≤ R) (hY : ∀ b, ‖A b‖ ≤ Y) (hF0 : 0 ≤ F)
    (hF : ∀ b : Fin (m + 1) → Zd d L, b 0 = a₁ → R ≤ (STdiamInf b : ℝ) → ‖A b‖ ≤ F) :
    ‖STPsum (d := d) A a₁‖ ≤ ((2 * R + 2) ^ d) ^ m * Y + ((L : ℝ) ^ d) ^ m * F := by
  classical
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY (fun _ => 0))
  unfold STPsum
  set fib := Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁) with hfib
  set P : (Fin (m + 1) → Zd d L) → Prop := fun b => (STdiamInf b : ℝ) < R with hP
  have h1 : ‖∑ a ∈ fib, A a‖ ≤ ∑ a ∈ fib, ‖A a‖ := norm_sum_le _ _
  have h1' := Finset.sum_filter_add_sum_filter_not fib P (fun a => ‖A a‖)
  -- near part
  have hnear : ∑ a ∈ fib.filter P, ‖A a‖ ≤ ((2 * R + 2) ^ d) ^ m * Y := by
    have hsub : fib.filter P ⊆ Fintype.piFinset
        (fun i : Fin (m + 1) => if i = 0 then ({a₁} : Finset (Zd d L))
          else Finset.univ.filter fun x : Zd d L => (zdistInf d L (x - a₁) : ℝ) < R) := by
      intro b hb
      rw [Finset.mem_filter, hfib, Finset.mem_filter] at hb
      obtain ⟨⟨_, hb0⟩, hbP⟩ := hb
      rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i = 0
      · simp [hi, hb0]
      · simp only [hi, ite_false, Finset.mem_filter, Finset.mem_univ, true_and]
        have h2 := B45_zdistInf_le_diam b i 0
        rw [hb0] at h2
        exact lt_of_le_of_lt (by exact_mod_cast h2) hbP
    have hcard : ((fib.filter P).card : ℝ) ≤ ((2 * R + 2) ^ d) ^ m := by
      have h2 := Finset.card_le_card hsub
      rw [B45_card_pi] at h2
      have h3 : ((fib.filter P).card : ℝ) ≤
          (((Finset.univ.filter fun x : Zd d L => (zdistInf d L (x - a₁) : ℝ) < R).card : ℕ) : ℝ) ^ m := by
        exact_mod_cast h2
      exact h3.trans (pow_le_pow_left₀ (by positivity) (B45_card_ball d L a₁ hR) m)
    calc ∑ a ∈ fib.filter P, ‖A a‖ ≤ ∑ _a ∈ fib.filter P, Y :=
          Finset.sum_le_sum fun a _ => hY a
      _ = ((fib.filter P).card : ℝ) * Y := by simp
      _ ≤ _ := by gcongr
  -- far part
  have hfar : ∑ a ∈ fib.filter (fun b => ¬ P b), ‖A a‖ ≤ ((L : ℝ) ^ d) ^ m * F := by
    have hbd : ∀ a ∈ fib.filter (fun b => ¬ P b), ‖A a‖ ≤ F := by
      intro b hb
      rw [Finset.mem_filter, hfib, Finset.mem_filter] at hb
      obtain ⟨⟨_, hb0⟩, hbP⟩ := hb
      refine hF b hb0 ?_
      simp only [hP, not_lt] at hbP
      exact hbP
    have hsub : fib ⊆ Fintype.piFinset
        (fun i : Fin (m + 1) => if i = 0 then ({a₁} : Finset (Zd d L)) else Finset.univ) := by
      intro b hb
      rw [hfib, Finset.mem_filter] at hb
      rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i = 0
      · simp [hi, hb.2]
      · simp [hi]
    have hcard : ((fib.filter (fun b => ¬ P b)).card : ℝ) ≤ ((L : ℝ) ^ d) ^ m := by
      have h2 := (Finset.card_le_card (Finset.filter_subset (fun b => ¬ P b) fib)).trans
        (Finset.card_le_card hsub)
      rw [B45_card_pi, Finset.card_univ, card_Zd] at h2
      exact_mod_cast h2
    calc ∑ a ∈ fib.filter (fun b => ¬ P b), ‖A a‖ ≤ ∑ _a ∈ fib.filter (fun b => ¬ P b), F :=
          Finset.sum_le_sum hbd
      _ = ((fib.filter (fun b => ¬ P b)).card : ℝ) * F := by simp
      _ ≤ _ := by gcongr
  linarith

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- `𝒫` as a sum over the first `m+1` labels and the last label. -/
theorem B45_Psum_snoc {d L m : ℕ} [NeZero L] (A : (Fin (m + 2) → Zd d L) → ℂ) (a₁ : Zd d L) :
    STPsum (d := d) A a₁ =
      ∑ a' ∈ Finset.univ.filter (fun a' : Fin (m + 1) → Zd d L => a' 0 = a₁),
        ∑ x : Zd d L, A (Fin.snoc (α := fun _ => Zd d L) a' x) := by
  classical
  unfold STPsum
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 2) => Zd d L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  by_cases h : a' 0 = a₁
  · simp [Fin.snocEquiv, h]
  · simp [Fin.snocEquiv, h]

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

theorem B45_norm_kappa (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1) :
    ‖(2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹‖ =
      (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E u))⁻¹ := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  rw [norm_inv, norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hη.le]
  simp only [Complex.norm_natCast, Complex.norm_ofNat, mul_one]
  congr 1
  ring

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`(ℓ_u^d (1-u))⁻¹ ≤ 2 B_{u,0}`** (the content of `(ℓ^d η)⁻¹ ≲ B_{u,0}`, `3_5:1264`, `(eq:Bu0asymp)`):
three cases, `g² ≤ 1-u` (`ℓ = 1`), `1-u < g²` with `ℓ = g/√(1-u)` (`d ≥ 2`) and with `ℓ = L`
(the zero-mode term of `B`).  It holds for every `u < 1`: the condition `1-u ≥ g²/L²` of case (i)
is not used. -/
theorem B45_scale {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L) {g u : ℝ} (hg : 0 < g) (hu : u < 1) :
    ((ellT L g u) ^ d * (1 - u))⁻¹ ≤ 2 * Bparam d L g u 0 := by
  have hv : 0 < 1 - u := by linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hB1 : (g ^ 2 + (1 - u))⁻¹ ≤ Bparam d L g u 0 := by
    unfold Bparam
    rw [abs_of_pos hv]
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    have : 0 ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ := by positivity
    linarith
  have hB2 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ Bparam d L g u 0 := by
    unfold Bparam
    rw [abs_of_pos hv]
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    have : 0 ≤ (g ^ 2 + (1 - u))⁻¹ := by positivity
    linarith
  have hsq : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr hv
  have hxsq : (g / Real.sqrt |1 - u|) ^ 2 = g ^ 2 / (1 - u) := by
    rw [div_pow, abs_of_pos hv, Real.sq_sqrt hv.le]
  set x := g / Real.sqrt |1 - u| with hx
  have hx0 : 0 < x := by rw [hx, abs_of_pos hv]; positivity
  have hℓ : ellT L g u = min (max x 1) L := rfl
  by_cases hgv : g ^ 2 ≤ 1 - u
  · -- `x ≤ 1`, `ℓ = 1`
    have hx1 : x ≤ 1 := by
      by_contra h
      push Not at h
      have : 1 < x ^ 2 := by nlinarith
      rw [hxsq, lt_div_iff₀ hv] at this
      linarith
    have hℓ1 : ellT L g u = 1 := by
      rw [hℓ, max_eq_right hx1]; exact min_eq_left hLr
    rw [hℓ1, one_pow, one_mul]
    have h1 : (1 - u)⁻¹ ≤ 2 * (g ^ 2 + (1 - u))⁻¹ := by
      rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ hv (by positivity)]
      nlinarith
    linarith
  · push Not at hgv
    have hx1 : 1 < x := by
      by_contra h
      push Not at h
      have : x ^ 2 ≤ 1 := by nlinarith
      rw [hxsq, div_le_iff₀ hv] at this
      linarith
    have hmax : max x 1 = x := max_eq_left hx1.le
    by_cases hxL : x ≤ L
    · have hℓx : ellT L g u = x := by rw [hℓ, hmax]; exact min_eq_left hxL
      rw [hℓx]
      have h2 : x ^ 2 ≤ x ^ d := pow_le_pow_right₀ hx1.le hd
      have h3 : (x ^ d * (1 - u))⁻¹ ≤ (x ^ 2 * (1 - u))⁻¹ :=
        inv_anti₀ (by positivity) (by gcongr)
      have h4 : (x ^ 2 * (1 - u))⁻¹ = (g ^ 2)⁻¹ := by
        rw [hxsq]; field_simp
      have h5 : (g ^ 2)⁻¹ ≤ 2 * (g ^ 2 + (1 - u))⁻¹ := by
        rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · push Not at hxL
      have hℓL : ellT L g u = L := by rw [hℓ, hmax]; exact min_eq_right hxL.le
      rw [hℓL]
      have hB0 : 0 ≤ Bparam d L g u 0 := (inv_nonneg.2 (by positivity)).trans hB1
      linarith

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

/-- **The exponent count of `(eq:Ward_typeP)`** in real quantities.  `Pi` bounds `|𝒫𝒜_{a₀}|` by the
window split, `ϑb` bounds the mollifier by `Λ (ℓ^d)^{-(m+1)}`; the conclusion is the bound
`Pi ϑb ≤ 3·4^{dm} Γ Λ ν² (W^{-d}B)^{m+2} X`.  The `ℓ`-powers do not cancel at `d ≥ 3`: the left over
`(W^d η)⁻¹ ℓ^{-d}` is absorbed by `2 Γ B` (`hKB`, `B45_scale`). -/
theorem B45_master_real {d m : ℕ} {Wd Ld N η B ℓ X ν ω Γ Λ ϑb Pi Fv : ℝ}
    (hWd : 0 < Wd) (hLd : 1 ≤ Ld) (hN : N = Wd * Ld) (hℓ : 1 ≤ ℓ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hB : 0 < B) (hη : 0 < η) (hω1 : 1 ≤ ω) (hωd : ω ^ (d * m) ≤ ν) (hΓ : 0 ≤ Γ) (hΛ : 0 ≤ Λ)
    (hWd1 : 1 ≤ Wd)
    (hKB : (Wd * η)⁻¹ * (ℓ ^ d)⁻¹ ≤ 2 * Γ * B) (hηN : η⁻¹ ≤ Γ * N) (hBN : N⁻¹ ≤ B)
    (hFv : Fv ≤ ν * (N ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hνN : ν ≤ N)
    (hPi0 : 0 ≤ Pi) (hϑ0 : 0 ≤ ϑb)
    (hPi : Pi ≤ (Wd * η)⁻¹ * (((2 * (ℓ * ω) + 2) ^ d) ^ m * (ν * X * B ^ (m + 1)) + Ld ^ m * Fv))
    (hϑ : ϑb ≤ Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) :
    Pi * ϑb ≤ (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (B ^ (m + 2) * X) := by
  have hN1 : 1 ≤ N := by rw [hN]; nlinarith
  have hN0 : 0 < N := by linarith
  have hℓd : 1 ≤ ℓ ^ d := one_le_pow₀ hℓ
  have hℓd0 : 0 < ℓ ^ d := by linarith
  have hWη : 0 < Wd * η := mul_pos hWd hη
  have hWη' : (Wd * η)⁻¹ ≤ Γ * N := by
    calc (Wd * η)⁻¹ ≤ η⁻¹ := by
          rw [mul_inv]
          exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hWd1)
      _ ≤ Γ * N := hηN
  -- the window factor
  have hwin : ((2 * (ℓ * ω) + 2) ^ d) ^ m ≤ 4 ^ (d * m) * (ℓ ^ d) ^ m * ν := by
    have h1 : 2 * (ℓ * ω) + 2 ≤ 4 * (ℓ * ω) := by nlinarith
    have h2 : (2 * (ℓ * ω) + 2) ^ d ≤ (4 * (ℓ * ω)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    have h3 : ((2 * (ℓ * ω) + 2) ^ d) ^ m ≤ ((4 * (ℓ * ω)) ^ d) ^ m := pow_le_pow_left₀ (by positivity) h2 m
    calc ((2 * (ℓ * ω) + 2) ^ d) ^ m ≤ ((4 * (ℓ * ω)) ^ d) ^ m := h3
      _ = 4 ^ (d * m) * (ℓ ^ d) ^ m * ω ^ (d * m) := by
        rw [← pow_mul, ← pow_mul, mul_pow, mul_pow]
        ring
      _ ≤ 4 ^ (d * m) * (ℓ ^ d) ^ m * ν := by gcongr
  set T1 : ℝ := ((2 * (ℓ * ω) + 2) ^ d) ^ m * (ν * X * B ^ (m + 1)) with hT1
  set T2 : ℝ := Ld ^ m * Fv with hT2
  have hT1le : T1 ≤ 4 ^ (d * m) * (ℓ ^ d) ^ m * ν * (ν * X * B ^ (m + 1)) := by
    rw [hT1]; gcongr
  -- the second term
  have hLdN : Ld ≤ N := by rw [hN]; nlinarith
  have hT2le : T2 ≤ N ^ m * (ν * (N ^ (2 * m + 4))⁻¹) := by
    rw [hT2]
    have h0 : 0 ≤ ν * (N ^ (2 * m + 4))⁻¹ := by positivity
    calc Ld ^ m * Fv ≤ N ^ m * Fv := by gcongr
      _ ≤ N ^ m * (ν * (N ^ (2 * m + 4))⁻¹) := by gcongr
  have hPi' : Pi ≤ (Wd * η)⁻¹ * (T1 + T2) := hPi
  have hϑ' : ϑb ≤ Λ * ((ℓ ^ d)⁻¹) ^ (m + 1) := hϑ
  have hxx : (ℓ ^ d)⁻¹ ^ (m + 1) ≤ (ℓ ^ d)⁻¹ ^ (m + 1) := le_rfl
  -- first part of the product
  have hA : (Wd * η)⁻¹ * T1 * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) ≤
      2 * Γ * 4 ^ (d * m) * Λ * ν ^ 2 * (B ^ (m + 2) * X) := by
    have h1 : (Wd * η)⁻¹ * T1 * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) ≤
        (Wd * η)⁻¹ * (4 ^ (d * m) * (ℓ ^ d) ^ m * ν * (ν * X * B ^ (m + 1))) *
          (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) := by gcongr
    have h2 : (Wd * η)⁻¹ * (4 ^ (d * m) * (ℓ ^ d) ^ m * ν * (ν * X * B ^ (m + 1))) *
          (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) =
        ((Wd * η)⁻¹ * (ℓ ^ d)⁻¹) * (4 ^ (d * m) * Λ * ν ^ 2 * X * B ^ (m + 1)) := by
      have : (ℓ ^ d) ^ m * ((ℓ ^ d)⁻¹) ^ (m + 1) = (ℓ ^ d)⁻¹ := by
        rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hℓd0.ne', one_pow, one_mul]
      calc _ = (Wd * η)⁻¹ * (4 ^ (d * m) * Λ * ν ^ 2 * X * B ^ (m + 1)) *
            ((ℓ ^ d) ^ m * ((ℓ ^ d)⁻¹) ^ (m + 1)) := by ring
        _ = _ := by rw [this]; ring
    rw [h2] at h1
    refine h1.trans ?_
    have h3 : ((Wd * η)⁻¹ * (ℓ ^ d)⁻¹) * (4 ^ (d * m) * Λ * ν ^ 2 * X * B ^ (m + 1)) ≤
        (2 * Γ * B) * (4 ^ (d * m) * Λ * ν ^ 2 * X * B ^ (m + 1)) := by gcongr
    refine h3.trans (le_of_eq ?_)
    ring
  -- second part
  have hBm : N⁻¹ ^ (m + 2) ≤ B ^ (m + 2) := pow_le_pow_left₀ (by positivity) hBN _
  have hB' : (N ^ (m + 2))⁻¹ ≤ B ^ (m + 2) := by rw [← inv_pow]; exact hBm
  have hC : (Wd * η)⁻¹ * T2 * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) ≤ Γ * Λ * (B ^ (m + 2) * X) := by
    have hl1 : ((ℓ ^ d)⁻¹) ^ (m + 1) ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hℓd)
    have h1 : (Wd * η)⁻¹ * T2 * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) ≤
        (Γ * N) * (N ^ m * (ν * (N ^ (2 * m + 4))⁻¹)) * (Λ * 1) := by
      gcongr
    have h2 : (Γ * N) * (N ^ m * (ν * (N ^ (2 * m + 4))⁻¹)) * (Λ * 1) =
        Γ * Λ * ν * (N ^ (m + 1) * (N ^ (2 * m + 4))⁻¹) := by ring
    have h3 : N ^ (m + 1) * (N ^ (2 * m + 4))⁻¹ ≤ (N ^ (m + 2))⁻¹ * N⁻¹ := by
      have e : N ^ (m + 1) * (N ^ (2 * m + 4))⁻¹ = (N ^ (m + 2))⁻¹ * N⁻¹ * (N ^ (m + 1) * N ^ (m + 2) * N / N ^ (2 * m + 4)) := by
        field_simp
      have e2 : N ^ (m + 1) * N ^ (m + 2) * N / N ^ (2 * m + 4) = 1 := by
        rw [div_eq_one_iff_eq (by positivity)]
        ring
      rw [e, e2, mul_one]
    have h4 : ν * ((N ^ (m + 2))⁻¹ * N⁻¹) ≤ B ^ (m + 2) * X := by
      have : ν * N⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hN0]; exact hνN
      calc ν * ((N ^ (m + 2))⁻¹ * N⁻¹) = (N ^ (m + 2))⁻¹ * (ν * N⁻¹) := by ring
        _ ≤ (N ^ (m + 2))⁻¹ * 1 := by gcongr
        _ ≤ B ^ (m + 2) * 1 := by simpa using hB'
        _ ≤ B ^ (m + 2) * X := by gcongr
    refine h1.trans ?_
    rw [h2]
    have hΓΛ : 0 ≤ Γ * Λ := mul_nonneg hΓ hΛ
    calc Γ * Λ * ν * (N ^ (m + 1) * (N ^ (2 * m + 4))⁻¹)
        ≤ Γ * Λ * ν * ((N ^ (m + 2))⁻¹ * N⁻¹) := by gcongr
      _ = Γ * Λ * (ν * ((N ^ (m + 2))⁻¹ * N⁻¹)) := by ring
      _ ≤ Γ * Λ * (B ^ (m + 2) * X) := by gcongr
  -- assemble
  have hprod : Pi * ϑb ≤ (Wd * η)⁻¹ * (T1 + T2) * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) := by
    gcongr
  have hsplit : (Wd * η)⁻¹ * (T1 + T2) * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) =
      (Wd * η)⁻¹ * T1 * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) + (Wd * η)⁻¹ * T2 * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) := by ring
  have h4m : (1 : ℝ) ≤ 4 ^ (d * m) := one_le_pow₀ (by norm_num)
  have hν2 : (1 : ℝ) ≤ ν ^ 2 := one_le_pow₀ hν
  have hK : (1 : ℝ) ≤ 4 ^ (d * m) * ν ^ 2 := one_le_mul_of_one_le_of_one_le h4m hν2
  have hZ : 0 ≤ Γ * Λ * (B ^ (m + 2) * X) := by positivity
  have hZK : Γ * Λ * (B ^ (m + 2) * X) ≤ (4 ^ (d * m) * ν ^ 2) * (Γ * Λ * (B ^ (m + 2) * X)) :=
    le_mul_of_one_le_left hZ hK
  have hA' : 2 * Γ * 4 ^ (d * m) * Λ * ν ^ 2 * (B ^ (m + 2) * X) =
      2 * ((4 ^ (d * m) * ν ^ 2) * (Γ * Λ * (B ^ (m + 2) * X))) := by ring
  have hfin : (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (B ^ (m + 2) * X) =
      3 * ((4 ^ (d * m) * ν ^ 2) * (Γ * Λ * (B ^ (m + 2) * X))) := by ring
  rw [hfin]
  have hC' : (Wd * η)⁻¹ * T2 * (Λ * ((ℓ ^ d)⁻¹) ^ (m + 1)) ≤ Γ * Λ * (B ^ (m + 2) * X) := hC
  linarith [hprod, hsplit, hA, hC', hA', hZK]

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss
open scoped Matrix.Norms.Operator

section ThetaNorm

variable {d L : ℕ} [NeZero L]

/-- Row sums of the one-index kernel: `Σ_c |thetaKer μ t (x,c)| ≤ (1-t)⁻¹` for `|μ| = 1`. -/
theorem B45_row_thetaKer (g : ℝ) (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖thetaKer d L g μ t x c‖ ≤ (1 - t)⁻¹ := by
  refine (sum_norm_row_le (thetaKer d L g μ t) x).trans ?_
  unfold thetaKer
  calc ‖(μ • SB d L g) * Theta d L g ((t : ℂ) * μ)‖
      ≤ ‖μ • SB d L g‖ * ‖Theta d L g ((t : ℂ) * μ)‖ := norm_mul_le _ _
    _ ≤ (‖μ‖ * ‖SB d L g‖) * (1 - t)⁻¹ := by
        gcongr
        · exact norm_smul_le _ _
        · exact norm_Theta_le (g := g) hL ht0 ht1 hμ
    _ = (1 - t)⁻¹ := by rw [hμ, norm_SB d L g hL]; ring

/-- `‖Θ^{(k)}_{u,σ} 𝒜‖_max ≤ k (1-u)⁻¹ ‖𝒜‖_max` (row sums of the one-index kernels). -/
theorem B45_norm_ThetaN_le (g : ℝ) (hL : 3 ≤ L) {k : ℕ} {μs : Fin k → ℂ} (hμ : ∀ i, ‖μs i‖ = 1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {A : (Fin k → Zd d L) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (a : Fin k → Zd d L) :
    ‖ThetaN d L g μs u A a‖ ≤ (k : ℝ) * (1 - u)⁻¹ * M := by
  have hM : 0 ≤ M := by
    by_cases h : IsEmpty (Fin k → Zd d L)
    · exact absurd (⟨a⟩ : Nonempty (Fin k → Zd d L)) (not_nonempty_iff.2 h)
    · exact (norm_nonneg _).trans (hA a)
  unfold ThetaN
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin k, ‖∑ b : Zd d L, thetaKer d L g (cycProd μs i) u (a i) b *
          A (Function.update a i b)‖
      ≤ ∑ _i : Fin k, (1 - u)⁻¹ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hrow := B45_row_thetaKer (d := d) g hL (norm_cycProd hμ i) hu0 hu1 (a i)
        calc ‖∑ b : Zd d L, thetaKer d L g (cycProd μs i) u (a i) b * A (Function.update a i b)‖
            ≤ ∑ b : Zd d L, ‖thetaKer d L g (cycProd μs i) u (a i) b * A (Function.update a i b)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ b : Zd d L, ‖thetaKer d L g (cycProd μs i) u (a i) b‖ * M :=
              Finset.sum_le_sum fun b _ => by
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)
          _ = (∑ b : Zd d L, ‖thetaKer d L g (cycProd μs i) u (a i) b‖) * M := (Finset.sum_mul _ _ _).symm
          _ ≤ (1 - u)⁻¹ * M := mul_le_mul_of_nonneg_right hrow hM
    _ = (k : ℝ) * (1 - u)⁻¹ * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end ThetaNorm

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss
open scoped Matrix.Norms.Operator

section ThetaP

variable {d L m : ℕ} [NeZero L]

/-- Slot `0`: port of `QopAlgebra.qa_slot_zero` (`RBM2D SumZeroQ_slot_zero`). -/
private theorem B45_slot_zero (G : Zd d L → Zd d L → ℂ) (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
        ∑ b : Zd d L, G (a 0) b * A (Function.update a 0 b)
      = ∑ b : Zd d L, G a₁ b * STPsum (d := d) A b := by
  have h1 : ∀ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
      ∑ b : Zd d L, G (a 0) b * A (Function.update a 0 b)
        = ∑ b : Zd d L, G a₁ b * A (Function.update a 0 b) := by
    intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp only [ha0]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold STPsum
  refine Finset.sum_nbij' (fun a => Function.update a 0 b) (fun a => Function.update a 0 a₁)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro a ha
    have ha0 : a 0 = b := (Finset.mem_filter.mp ha).2
    simp
  · intro a ha
    have ha0 : a 0 = a₁ := (Finset.mem_filter.mp ha).2
    simp [ha0]
  · intro a ha
    have ha0 : a 0 = b := (Finset.mem_filter.mp ha).2
    simp [ha0]
  · intro a _
    rfl

/-- Slot `i ≠ 0`: port of `QopAlgebra.qa_slot_succ`. -/
private theorem B45_slot_succ {i : Fin (m + 1)} (hi : i ≠ 0) (G : Zd d L → Zd d L → ℂ)
    (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
        ∑ b : Zd d L, G (a i) b * A (Function.update a i b)
      = ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
          (∑ c : Zd d L, G c (a i)) * A a := by
  classical
  set F : Finset (Fin (m + 1) → Zd d L) :=
    Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁) with hF
  have h1 : ∑ a ∈ F, ∑ b : Zd d L, G (a i) b * A (Function.update a i b)
      = ∑ x ∈ F ×ˢ (Finset.univ : Finset (Zd d L)), G (x.1 i) x.2 * A (Function.update x.1 i x.2) :=
    (Finset.sum_product' F Finset.univ (fun a b => G (a i) b * A (Function.update a i b))).symm
  have h2 : ∑ x ∈ F ×ˢ (Finset.univ : Finset (Zd d L)), G (x.1 i) x.2 * A (Function.update x.1 i x.2)
      = ∑ x ∈ F ×ˢ (Finset.univ : Finset (Zd d L)), G x.2 (x.1 i) * A x.1 := by
    refine Finset.sum_nbij' (fun x => (Function.update x.1 i x.2, x.1 i))
      (fun x => (Function.update x.1 i x.2, x.1 i)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx0 : x.1 0 = a₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
      simp [hF, Function.update_of_ne hi.symm, hx0]
    · intro x hx
      have hx0 : x.1 0 = a₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
      simp [hF, Function.update_of_ne hi.symm, hx0]
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      simp
  rw [h1, h2, Finset.sum_product' F Finset.univ (fun a b => G b (a i) * A a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]

/-- `‖μ (1 - tμ)⁻¹‖ ≤ (1-t)⁻¹` for `‖μ‖ = 1`, `0 ≤ t < 1`. -/
private theorem B45_norm_colsum {μ : ℂ} (hμ : ‖μ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖μ * (1 - (t : ℂ) * μ)⁻¹‖ ≤ (1 - t)⁻¹ := by
  have htμ : ‖(t : ℂ) * μ‖ = t := by rw [norm_mul, hμ, mul_one, Complex.norm_of_nonneg ht0]
  have h1 : 1 - t ≤ ‖1 - (t : ℂ) * μ‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * μ)
    rw [htμ, norm_one] at this
    exact this
  have hpos : 0 < 1 - t := by linarith
  rw [norm_mul, hμ, one_mul, norm_inv]
  exact inv_anti₀ hpos h1

/-- **`‖𝒫(Θ_{t,σ}𝒜)‖_max ≤ (m+1)(1-t)⁻¹ ‖𝒫𝒜‖_max`**: slot `0` gives `Σ_b K₀(a₁,b)(𝒫𝒜)_b`, every slot
`i ≥ 1` the constant column sum of `K_i` times `(𝒫𝒜)_{a₁}`. -/
theorem B45_Psum_ThetaN_le (g : ℝ) (hL : 3 ≤ L) {μs : Fin (m + 1) → ℂ} (hμ : ∀ i, ‖μs i‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {A : (Fin (m + 1) → Zd d L) → ℂ} {M : ℝ}
    (hA : ∀ b₁, ‖STPsum (d := d) A b₁‖ ≤ M) (a₁ : Zd d L) :
    ‖STPsum (d := d) (ThetaN d L g μs t A) a₁‖ ≤ ((m + 1 : ℕ) : ℝ) * (1 - t)⁻¹ * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA a₁)
  have hpos : 0 ≤ (1 - t)⁻¹ := inv_nonneg.2 (by linarith)
  unfold STPsum
  simp only [ThetaN]
  rw [Finset.sum_comm]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin (m + 1), ‖∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁),
          ∑ b : Zd d L, thetaKer d L g (cycProd μs i) t (a i) b * A (Function.update a i b)‖
      ≤ ∑ _i : Fin (m + 1), (1 - t)⁻¹ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          rw [B45_slot_zero (d := d) (fun x y => thetaKer d L g (cycProd μs 0) t x y) A a₁]
          refine (norm_sum_le _ _).trans ?_
          calc ∑ b : Zd d L, ‖thetaKer d L g (cycProd μs 0) t a₁ b * STPsum (d := d) A b‖
              ≤ ∑ b : Zd d L, ‖thetaKer d L g (cycProd μs 0) t a₁ b‖ * M :=
                Finset.sum_le_sum fun b _ => by
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left (hA b) (norm_nonneg _)
            _ = (∑ b : Zd d L, ‖thetaKer d L g (cycProd μs 0) t a₁ b‖) * M :=
                (Finset.sum_mul _ _ _).symm
            _ ≤ (1 - t)⁻¹ * M :=
                mul_le_mul_of_nonneg_right
                  (B45_row_thetaKer (d := d) g hL (norm_cycProd hμ 0) ht0 ht1 a₁) hM
        · rw [B45_slot_succ (d := d) hi (fun x y => thetaKer d L g (cycProd μs i) t x y) A a₁]
          have hcol : ∀ y : Zd d L, ∑ c : Zd d L, thetaKer d L g (cycProd μs i) t c y
              = cycProd μs i * (1 - (t : ℂ) * cycProd μs i)⁻¹ := fun y =>
            QopAlgebra_col_sum_thetaKer g hL
              (by rw [norm_mul, norm_cycProd hμ i, mul_one, Complex.norm_of_nonneg ht0]; exact ht1) y
          simp only [hcol]
          rw [← Finset.mul_sum]
          calc ‖cycProd μs i * (1 - (t : ℂ) * cycProd μs i)⁻¹ *
                ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), A a‖
              = ‖cycProd μs i * (1 - (t : ℂ) * cycProd μs i)⁻¹‖ * ‖STPsum (d := d) A a₁‖ := by
                rw [norm_mul]; rfl
            _ ≤ (1 - t)⁻¹ * M :=
                mul_le_mul (B45_norm_colsum (norm_cycProd hμ i) ht0 ht1) (hA a₁) (norm_nonneg _) hpos
    _ = ((m + 1 : ℕ) : ℝ) * (1 - t)⁻¹ * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end ThetaP

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss
open scoped Matrix.Norms.Operator

section B4

variable {d L m : ℕ} [NeZero L]

theorem B45_norm_EKsgn {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) (i : Fin k) :
    ‖EKsgn (mE E) σ i‖ = 1 := by
  unfold EKsgn PropSpin
  have := norm_mE hE
  split_ifs
  · exact this
  · rw [RCLike.norm_conj]; exact this

/-- **`‖ℬ₄‖` bound** (`(A4)`, `3_5:1700`): `[𝒬_u, Θ] 𝒜 = Θ((𝒫𝒜) ϑ) - (𝒫Θ𝒜) ϑ`, with
`‖Θ‖_{∞→∞} ≤ (m+1)(1-u)⁻¹` and `‖𝒫Θ𝒜‖_max ≤ (m+1)(1-u)⁻¹ ‖𝒫𝒜‖_max`: if `‖𝒫𝒜‖_max ≤ Π` and `‖ϑ‖ ≤ ϑs`
then `‖ℬ₄‖ ≤ 2 (m+1)(1-u)⁻¹ Π ϑs`. -/
theorem B45_B4_le (g : ℝ) (hL : 3 ≤ L) {μs : Fin (m + 1) → ℂ} (hμ : ∀ i, ‖μs i‖ = 1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ)
    (A : (Fin (m + 1) → Zd d L) → ℂ) {Pi vs : ℝ}
    (hP : ∀ b₁, ‖STPsum (d := d) A b₁‖ ≤ Pi) (hϑ : ∀ b, ‖ϑ u b‖ ≤ vs) (a : Fin (m + 1) → Zd d L) :
    ‖STQop (d := d) ϑ u (ThetaN d L g μs u A) a - ThetaN d L g μs u (STQop (d := d) ϑ u A) a‖ ≤
      2 * ((m + 1 : ℕ) : ℝ) * (1 - u)⁻¹ * (Pi * vs) := by
  have hPi : 0 ≤ Pi := (norm_nonneg _).trans (hP (a 0))
  have hvs : 0 ≤ vs := (norm_nonneg _).trans (hϑ a)
  rw [QopAlgebra_commutator_ThetaN g μs ϑ u A a]
  have h1 : ‖ThetaN d L g μs u (fun b => STPsum (d := d) A (b 0) * ϑ u b) a‖ ≤
      ((m + 1 : ℕ) : ℝ) * (1 - u)⁻¹ * (Pi * vs) :=
    B45_norm_ThetaN_le g hL hμ hu0 hu1 (fun b => by
      rw [norm_mul]; exact mul_le_mul (hP _) (hϑ b) (norm_nonneg _) hPi) a
  have h2 : ‖STPsum (d := d) (ThetaN d L g μs u A) (a 0) * ϑ u a‖ ≤
      ((m + 1 : ℕ) : ℝ) * (1 - u)⁻¹ * (Pi * vs) := by
    rw [norm_mul]
    have h3 := B45_Psum_ThetaN_le g hL hμ hu0 hu1 hP (a 0)
    calc ‖STPsum (d := d) (ThetaN d L g μs u A) (a 0)‖ * ‖ϑ u a‖
        ≤ (((m + 1 : ℕ) : ℝ) * (1 - u)⁻¹ * Pi) * vs := mul_le_mul h3 (hϑ a) (norm_nonneg _) (by
          have : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
          positivity)
      _ = _ := by ring
  calc _ ≤ ‖ThetaN d L g μs u (fun b => STPsum (d := d) A (b 0) * ϑ u b) a‖ +
        ‖STPsum (d := d) (ThetaN d L g μs u A) (a 0) * ϑ u a‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

end B4

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss
open RBM.Ind (symIdx norm_sq_gloop_le_symIdx exists_split_loopIdx norm_gloop_le_of_le_abs_im
  symIdx_a_length)

/-! ## 2. Deterministic: the adjacent far pair and the cut -/

/-! ## 3. Deterministic: scales, exponents -/

section Scales

/-- `Im m(E) ≥ √κ / 2` for `|E| ≤ 2 - κ` (the same bound as `ST_mE_im_ge`, `Step2Events.lean:555`,
which is not imported here). -/
private theorem B45_mE_im_ge {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    Real.sqrt κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h := abs_le.mp hE
    nlinarith [h.1, h.2]
  have : κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

end Scales

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

section Cmp

/-- **Time-reversed fencing.**  If `f` is continuous on `[t,T]`, differentiable on `(t,T]` with
`‖f'‖ ≤ Φ'` for a function `Φ` with derivative `Φ'` on `[t,T]`, and `‖f(T)‖ ≤ b₀`, then
`‖f(t)‖ ≤ b₀ + Φ(T) - Φ(t)` (`image_norm_le_of_norm_deriv_right_le_deriv_boundary'` applied to
`s ↦ f(T-s)`).  The derivative of `f` is needed on `(t,T]` only, so `t = 0` is allowed. -/
theorem B45_cmp {f : ℝ → ℂ} {t T : ℝ} (htT : t ≤ T)
    (hcont : ContinuousOn f (Set.Icc t T))
    (hdiff : ∀ τ ∈ Set.Ioc t T, DifferentiableAt ℝ f τ)
    {Φ Φ' : ℝ → ℝ} (hΦ : ∀ τ ∈ Set.Icc t T, HasDerivAt Φ (Φ' τ) τ)
    (hbound : ∀ τ ∈ Set.Ioc t T, ‖deriv f τ‖ ≤ Φ' τ)
    {b₀ : ℝ} (hb : ‖f T‖ ≤ b₀) : ‖f t‖ ≤ b₀ + (Φ T - Φ t) := by
  set F : ℝ → ℂ := fun s => f (T - s) with hF
  set B : ℝ → ℝ := fun s => b₀ + Φ T - Φ (T - s) with hB
  have hmaps : Set.MapsTo (fun s : ℝ => T - s) (Set.Icc 0 (T - t)) (Set.Icc t T) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hFc : ContinuousOn F (Set.Icc 0 (T - t)) :=
    hcont.comp (continuousOn_const.sub continuousOn_id) hmaps
  have hF' : ∀ s ∈ Set.Ico 0 (T - t), HasDerivWithinAt F (-deriv f (T - s)) (Set.Ici s) s := by
    intro s hs
    have hτ : T - s ∈ Set.Ioc t T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h1 : HasDerivAt f (deriv f (T - s)) (T - s) := (hdiff _ hτ).hasDerivAt
    exact (HasDerivAt.comp_const_sub T s h1).hasDerivWithinAt
  have hBc : ContinuousOn B (Set.Icc 0 (T - t)) := by
    intro s hs
    have hτ : T - s ∈ Set.Icc t T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h1 : ContinuousAt Φ (T - s) := (hΦ _ hτ).continuousAt
    have h2 : ContinuousAt (fun s : ℝ => Φ (T - s)) s :=
      ContinuousAt.comp (f := fun s : ℝ => T - s) (x := s) h1 (by fun_prop)
    have h3 : ContinuousAt B s := by
      have : B = fun s => (b₀ + Φ T) - Φ (T - s) := by funext s; simp [hB]
      rw [this]
      exact continuousAt_const.sub h2
    exact h3.continuousWithinAt
  have hB' : ∀ s ∈ Set.Ico 0 (T - t), HasDerivWithinAt B (Φ' (T - s)) (Set.Ici s) s := by
    intro s hs
    have hτ : T - s ∈ Set.Icc t T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h1 := HasDerivAt.comp_const_sub T s (hΦ _ hτ)
    have h2 := (h1.const_sub (b₀ + Φ T))
    have h3 : HasDerivAt B (Φ' (T - s)) s := by
      have : B = fun s => b₀ + Φ T - Φ (T - s) := rfl
      rw [this]
      simpa using h2
    exact h3.hasDerivWithinAt
  have hbd : ∀ s ∈ Set.Ico 0 (T - t), ‖-deriv f (T - s)‖ ≤ Φ' (T - s) := by
    intro s hs
    have hτ : T - s ∈ Set.Ioc t T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [norm_neg]; exact hbound _ hτ
  have ha : ‖F 0‖ ≤ B 0 := by simp [hF, hB, hb]
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := 0) (b := T - t)
    (f := F) (f' := fun s => -deriv f (T - s)) hFc hF' (B := B) (B' := fun s => Φ' (T - s)) ha hBc hB' hbd
    (x := T - t) ⟨by linarith, le_rfl⟩
  have key2 : ‖f t‖ ≤ b₀ + Φ T - Φ t := by simpa [hF, hB] using key
  linarith

end Cmp

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Vth

variable {d L m : ℕ} [NeZero L]

/-- `|u|_L ≤ L/2` on the circle. -/
private theorem B45_two_mul_zdist_le (u : ZMod L) : 2 * zdist L u ≤ L := by
  unfold zdist
  have := ZMod.val_lt u
  omega

/-- `2 |x|_{ℓ¹} ≤ d L`. -/
private theorem B45_two_mul_zdistD_le (x : Zd d L) : 2 * zdistD d L x ≤ d * L := by
  unfold zdistD
  calc 2 * ∑ i, zdist L (x i) = ∑ i, 2 * zdist L (x i) := by rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin d, L := Finset.sum_le_sum fun i _ => B45_two_mul_zdist_le _
    _ = d * L := by simp

/-- The exponent of the exponential factor of the mollifier is at most `|c| m d / 2` at `ℓ = L`. -/
theorem B45_exp_at_L (g c : ℝ) (a : Fin (m + 1) → Zd d L) (hL : 1 ≤ L) :
    Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) / (L : ℝ))
      ≤ Real.exp (|c| * ((m : ℝ) * d / 2)) := by
  refine Real.exp_le_exp.2 ?_
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hS0 : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hSle : ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ) ≤
      (m : ℝ) * (d * L / 2) := by
    calc _ ≤ ∑ _i ∈ Finset.univ.erase (0 : Fin (m + 1)), ((d : ℝ) * L / 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := B45_two_mul_zdistD_le (d := d) (a i - a 0)
          have h2 : (2 : ℝ) * (zdistD d L (a i - a 0) : ℝ) ≤ d * L := by exact_mod_cast this
          linarith
      _ = (m : ℝ) * (d * L / 2) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
          simp
  rw [div_le_iff₀ hLr]
  calc -c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ))
      ≤ |c| * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) := by
        have : -c ≤ |c| := neg_le_abs c
        exact mul_le_mul_of_nonneg_right this hS0
    _ ≤ |c| * ((m : ℝ) * (d * L / 2)) := mul_le_mul_of_nonneg_left hSle (abs_nonneg c)
    _ = |c| * ((m : ℝ) * d / 2) * L := by ring

/-- `C ≥ 0` for any mollifier (the sup bound at `t = 0` is `‖ϑ‖ ≤ C · (positive)`). -/
theorem B45_C_nonneg (hL : 3 ≤ L) {g C c : ℝ} (hg : 0 < g)
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (h : STMollifierProps (d := d) g C c ϑ) : 0 ≤ C := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h2 := h.2.1 0 le_rfl zero_lt_one (fun _ => 0)
  have hℓ : 0 < ellT L g 0 := ellT_pos hL1
  have hpos : 0 < (((ellT L g 0) ^ d)⁻¹) ^ m * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
      (zdistD d L ((fun _ : Fin (m + 1) => (0 : Zd d L)) i - (fun _ : Fin (m + 1) => (0 : Zd d L)) 0) : ℝ)) / ellT L g 0) := by
    positivity
  have h3 : 0 ≤ C * (((ellT L g 0) ^ d)⁻¹) ^ m * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
      (zdistD d L ((fun _ : Fin (m + 1) => (0 : Zd d L)) i - (fun _ : Fin (m + 1) => (0 : Zd d L)) 0) : ℝ)) / ellT L g 0) :=
    (norm_nonneg _).trans h2
  rw [mul_assoc] at h3
  exact nonneg_of_mul_nonneg_left h3 hpos

end Vth

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section VthPhi

/-- The antiderivative of `C (1-τ)⁻¹ ((1-τ)/g²)^{k/2}`: `Φ(τ) = -(2C/k) (√(1-τ)/g)^k`. -/
theorem B45_hasDerivAt_Phi {g : ℝ} (hg : 0 < g) (C : ℝ) {k : ℕ} (hk : 1 ≤ k) {τ : ℝ} (hτ : τ < 1) :
    HasDerivAt (fun τ => -(2 * C / (k : ℝ)) * (Real.sqrt (1 - τ) / g) ^ k)
      (C * (1 - τ)⁻¹ * (Real.sqrt (1 - τ) / g) ^ k) τ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hv : 0 < 1 - τ := by linarith
  have hr : 0 < Real.sqrt (1 - τ) := Real.sqrt_pos.2 hv
  have h1 : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) τ := by
    simpa using (hasDerivAt_id τ).const_sub 1
  have h2 : HasDerivAt (fun τ : ℝ => Real.sqrt (1 - τ)) (-1 / (2 * Real.sqrt (1 - τ))) τ := by
    have := (Real.hasDerivAt_sqrt hv.ne').comp τ h1
    exact this.congr_deriv (by ring)
  have h3 : HasDerivAt (fun τ : ℝ => Real.sqrt (1 - τ) / g) (-1 / (2 * Real.sqrt (1 - τ)) / g) τ :=
    h2.div_const g
  have h4 := (h3.pow (k' + 1)).const_mul (-(2 * C / ((k' + 1 : ℕ) : ℝ)))
  refine h4.congr_deriv ?_
  have hsq : Real.sqrt (1 - τ) ^ 2 = 1 - τ := Real.sq_sqrt hv.le
  have hk0 : ((k' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  have hinv : (1 - τ)⁻¹ = (Real.sqrt (1 - τ) ^ 2)⁻¹ := by rw [hsq]
  rw [hinv]
  generalize Real.sqrt (1 - τ) = r at *
  field_simp
  rw [pow_succ]
  field_simp

end VthPhi

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section VthRegions

variable {d L m : ℕ} [NeZero L]

private theorem B45_ellT_eq_L {g τ : ℝ} (hτ : τ < 1) (hL : 1 ≤ L)
    (h : (L : ℝ) ≤ g / Real.sqrt (1 - τ)) : ellT L g τ = L := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold ellT
  rw [abs_of_pos (by linarith : 0 < 1 - τ)]
  exact min_eq_right (le_max_of_le_left h)

private theorem B45_ellT_eq_x {g τ : ℝ} (hτ : τ < 1) (h1 : 1 ≤ g / Real.sqrt (1 - τ))
    (h2 : g / Real.sqrt (1 - τ) ≤ L) : ellT L g τ = g / Real.sqrt (1 - τ) := by
  unfold ellT
  rw [abs_of_pos (by linarith : 0 < 1 - τ), max_eq_left h1]
  exact min_eq_left h2

private theorem B45_x_mono {g : ℝ} (hg : 0 < g) {τ τ' : ℝ} (hτ : τ ≤ τ') (hτ' : τ' < 1) :
    g / Real.sqrt (1 - τ) ≤ g / Real.sqrt (1 - τ') := by
  have h1 : 0 < Real.sqrt (1 - τ') := Real.sqrt_pos.2 (by linarith)
  exact div_le_div_of_nonneg_left hg.le h1 (Real.sqrt_le_sqrt (by linarith))

/-- `((x^d)⁻¹)^m = (x⁻¹)^{dm}`. -/
private theorem B45_inv_pow_eq (d m : ℕ) (x : ℝ) : ((x ^ d)⁻¹) ^ m = (x⁻¹) ^ (d * m) := by
  rw [pow_mul, inv_pow x d]

/-- **The mollifier bound in the window `1 ≤ g/√(1-τ) ≤ L`** (the sup bound with the exponential factor
`exp(-c S/ℓ)` of the pin, `c` any real: the factor is controlled at the later time `T = 1 - g²/L²`, where
`ℓ_T = L`, and transported back by the derivative bound `‖∂_τϑ‖ ≤ C (1-τ)⁻¹ ℓ_τ^{-dm}`,
`B45_cmp` with the antiderivative `Φ`). -/
theorem B45_vth_mid (hL : 3 ≤ L) {g C c : ℝ} (hg : 0 < g)
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (h : STMollifierProps (d := d) g C c ϑ)
    (hdm : 1 ≤ d * m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hx1 : 1 ≤ g / Real.sqrt (1 - t)) (hxL : g / Real.sqrt (1 - t) ≤ L)
    (a : Fin (m + 1) → Zd d L) :
    ‖ϑ t a‖ ≤ (C * Real.exp (|c| * ((m : ℝ) * d / 2)) + 2 * C / ((d * m : ℕ) : ℝ)) *
      (((ellT L g t) ^ d)⁻¹) ^ m := by
  have hL1 : 1 ≤ L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hC := B45_C_nonneg hL hg h
  have hv : 0 < 1 - t := by linarith
  have hsq : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 hv
  have hℓt : ellT L g t = g / Real.sqrt (1 - t) := B45_ellT_eq_x ht1 hx1 hxL
  -- the later time `T`
  set T : ℝ := 1 - g ^ 2 / (L : ℝ) ^ 2 with hT
  have hgL : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
  have hT1 : T < 1 := by rw [hT]; linarith
  have htT : t ≤ T := by
    have h1 : g ≤ L * Real.sqrt (1 - t) := by
      rw [div_le_iff₀ hsq] at hxL; linarith
    have h2 : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) := by
      have := pow_le_pow_left₀ hg.le h1 2
      rwa [mul_pow, Real.sq_sqrt hv.le] at this
    rw [hT, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by positivity)]
    nlinarith
  have hT0 : 0 ≤ T := ht0.trans htT
  have hvT : 0 < 1 - T := by linarith
  have h1T : 1 - T = g ^ 2 / (L : ℝ) ^ 2 := by rw [hT]; ring
  have hxT : g / Real.sqrt (1 - T) = L := by
    rw [h1T, Real.sqrt_div (by positivity), Real.sqrt_sq hg.le, Real.sqrt_sq hLr.le]
    field_simp
  have hℓT : ellT L g T = L := B45_ellT_eq_L hT1 hL1 hxT.ge
  have hKc := B45_exp_at_L (d := d) (m := m) g c a hL1
  -- the value at `T`
  have hfT : ‖ϑ T a‖ ≤ C * (((L : ℝ) ^ d)⁻¹) ^ m * Real.exp (|c| * ((m : ℝ) * d / 2)) := by
    have h2 := h.2.1 T hT0 hT1 a
    rw [hℓT] at h2
    refine h2.trans ?_
    have : 0 ≤ C * (((L : ℝ) ^ d)⁻¹) ^ m := by positivity
    exact mul_le_mul_of_nonneg_left hKc this
  -- the comparison
  have hcont : ContinuousOn (fun τ => ϑ τ a) (Set.Icc t T) :=
    ((h.2.2.1 a).continuousOn).mono (fun τ hτ => ⟨ht0.trans hτ.1, lt_of_le_of_lt hτ.2 hT1⟩)
  have hdiff : ∀ τ ∈ Set.Ioc t T, DifferentiableAt ℝ (fun τ => ϑ τ a) τ := by
    intro τ hτ
    exact (h.2.2.1 a).differentiableAt (Ico_mem_nhds (by linarith [hτ.1]) (by linarith [hτ.2]))
  have hΦ : ∀ τ ∈ Set.Icc t T, HasDerivAt
      (fun τ => -(2 * C / ((d * m : ℕ) : ℝ)) * (Real.sqrt (1 - τ) / g) ^ (d * m))
      (C * (1 - τ)⁻¹ * (Real.sqrt (1 - τ) / g) ^ (d * m)) τ := fun τ hτ =>
    B45_hasDerivAt_Phi hg C hdm (by linarith [hτ.2])
  have hbound : ∀ τ ∈ Set.Ioc t T, ‖deriv (fun τ => ϑ τ a) τ‖ ≤
      C * (1 - τ)⁻¹ * (Real.sqrt (1 - τ) / g) ^ (d * m) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := by linarith [hτ.1]
    have hτ1 : τ < 1 := by linarith [hτ.2]
    have h4 := h.2.2.2 τ hτ0 hτ1 a
    have hx1' : 1 ≤ g / Real.sqrt (1 - τ) :=
      hx1.trans (B45_x_mono hg hτ.1.le hτ1)
    have hxL' : g / Real.sqrt (1 - τ) ≤ L := by
      calc g / Real.sqrt (1 - τ) ≤ g / Real.sqrt (1 - T) := B45_x_mono hg hτ.2 hT1
        _ = L := hxT
    rw [B45_ellT_eq_x hτ1 hx1' hxL', B45_inv_pow_eq, inv_div] at h4
    exact h4
  have hcmp := B45_cmp htT hcont hdiff hΦ hbound hfT
  refine hcmp.trans ?_
  -- bookkeeping
  have hQ : (((ellT L g t) ^ d)⁻¹) ^ m = (Real.sqrt (1 - t) / g) ^ (d * m) := by
    rw [hℓt, B45_inv_pow_eq, inv_div]
  rw [hQ]
  have hq : 0 ≤ (Real.sqrt (1 - T) / g) ^ (d * m) := by positivity
  have hdm0 : (0 : ℝ) < ((d * m : ℕ) : ℝ) := by exact_mod_cast hdm
  have h5 : (((L : ℝ) ^ d)⁻¹) ^ m ≤ (Real.sqrt (1 - t) / g) ^ (d * m) := by
    rw [B45_inv_pow_eq]
    have h6 : (L : ℝ)⁻¹ ≤ Real.sqrt (1 - t) / g := by
      have : (Real.sqrt (1 - t) / g) = (g / Real.sqrt (1 - t))⁻¹ := by rw [inv_div]
      rw [this]
      exact inv_anti₀ (by positivity) hxL
    exact pow_le_pow_left₀ (by positivity) h6 _
  have hKe : 0 ≤ Real.exp (|c| * ((m : ℝ) * d / 2)) := (Real.exp_pos _).le
  have h7 : C * (((L : ℝ) ^ d)⁻¹) ^ m * Real.exp (|c| * ((m : ℝ) * d / 2)) ≤
      C * Real.exp (|c| * ((m : ℝ) * d / 2)) * (Real.sqrt (1 - t) / g) ^ (d * m) := by
    have : C * (((L : ℝ) ^ d)⁻¹) ^ m * Real.exp (|c| * ((m : ℝ) * d / 2)) =
        (C * Real.exp (|c| * ((m : ℝ) * d / 2))) * (((L : ℝ) ^ d)⁻¹) ^ m := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h5 (mul_nonneg hC hKe)
  have h8 : -(2 * C / ((d * m : ℕ) : ℝ)) * (Real.sqrt (1 - T) / g) ^ (d * m) -
      -(2 * C / ((d * m : ℕ) : ℝ)) * (Real.sqrt (1 - t) / g) ^ (d * m) ≤
      2 * C / ((d * m : ℕ) : ℝ) * (Real.sqrt (1 - t) / g) ^ (d * m) := by
    have h9 : 0 ≤ 2 * C / ((d * m : ℕ) : ℝ) * (Real.sqrt (1 - T) / g) ^ (d * m) :=
      mul_nonneg (by positivity) hq
    nlinarith
  calc _ ≤ C * Real.exp (|c| * ((m : ℝ) * d / 2)) * (Real.sqrt (1 - t) / g) ^ (d * m) +
        2 * C / ((d * m : ℕ) : ℝ) * (Real.sqrt (1 - t) / g) ^ (d * m) := add_le_add h7 h8
    _ = _ := by ring

end VthRegions

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Scales45

variable {d : ℕ}

/-- The scale inputs of the exponent count: `(W^d η)⁻¹ ℓ^{-d} ≤ 2Γ W^{-d}B_{u,0}` (`d ≥ 2`, `B45_scale`),
`η⁻¹ ≤ Γ N` and `N⁻¹ ≤ W^{-d}B_{u,0}`, `Γ = 2/√κ`. -/
theorem B45_scales (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) {Γ : ℝ} (hΓ : Γ = 2 / Real.sqrt κ) :
    ((((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ≤
        2 * Γ * sz.Bctl n u) ∧
      (etaT E u)⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) ∧ ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n u ∧
      0 < etaT E u ∧ etaT E u ≤ 1 - u := by
  have hv : 0 < 1 - u := by linarith
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hμ : Real.sqrt κ / 2 ≤ (mE E).im := B45_mE_im_ge hκ hE
  have hμ0 : 0 < (mE E).im := lt_of_lt_of_le (by positivity) hμ
  have hμ1 : (mE E).im ≤ 1 := by
    have h2 : |E| ≤ 2 := by
      have : 0 < κ := hκ
      have := abs_nonneg E; linarith
    calc (mE E).im ≤ |(mE E).im| := le_abs_self _
      _ ≤ ‖mE E‖ := Complex.abs_im_le_norm _
      _ = 1 := norm_mE h2
  have hη : 0 < etaT E u := mul_pos hv hμ0
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by rw [hNe]; positivity
  refine ⟨?_, ?_, ?_, hη, ?_⟩
  · -- `(W^d η)⁻¹ ℓ^{-d} ≤ 2Γ B`
    have hsc := B45_scale (d := d) (L := sz.L n) hd (by have := sz.three_le_L n; omega) hg hu1
    have h1 : (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) =
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((mE E).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹) := by
      unfold etaT
      field_simp
    rw [h1]
    have h2 : ((mE E).im)⁻¹ ≤ Γ := by
      rw [hΓ]
      calc ((mE E).im)⁻¹ ≤ (Real.sqrt κ / 2)⁻¹ := inv_anti₀ (by positivity) hμ
        _ = 2 / Real.sqrt κ := by field_simp
    have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
    unfold Sizes.Bctl
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((mE E).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Γ * (2 * Bparam d (sz.L n) (sz.lam n) u 0) := by
          have hpos : 0 ≤ (ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹ := by
            have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := u) (by
              have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n))
            positivity
          gcongr
      _ = 2 * Γ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0) := by ring
  · -- `η⁻¹ ≤ Γ N`
    have h1 : (1 - u) * (Real.sqrt κ / 2) ≤ etaT E u := mul_le_mul_of_nonneg_left hμ hv.le
    have h2 : (etaT E u)⁻¹ ≤ ((1 - u) * (Real.sqrt κ / 2))⁻¹ := inv_anti₀ (by positivity) h1
    have h3 : ((1 - u) * (Real.sqrt κ / 2))⁻¹ = Γ * (1 - u)⁻¹ := by
      rw [hΓ]; field_simp
    have h4 : (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
    calc (etaT E u)⁻¹ ≤ ((1 - u) * (Real.sqrt κ / 2))⁻¹ := h2
      _ = Γ * (1 - u)⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by gcongr
  · -- `N⁻¹ ≤ B`
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hv, hNe, mul_inv]
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
      apply inv_anti₀ (by positivity)
      have : 1 - u ≤ 1 := by linarith
      calc ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.L n : ℕ) : ℝ) ^ d * 1 := by gcongr
        _ = _ := mul_one _
    have h2 : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    have key : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
            (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
      gcongr
      linarith
    exact key
  · have e : etaT E u = (1 - u) * (mE E).im := rfl
    rw [e]
    have := mul_le_mul_of_nonneg_left hμ1 hv.le
    linarith

end Scales45

end RBM.Gauss.Sizes

set_option maxHeartbeats 400000 in
-- the pointwise chain of the far/near split elaborates a long `have` list: 200000 is not enough
/-! ## Compiled nonempty instances (`d = 3`)

Data: the merged size sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the flow
`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, `s ≡ 0`, `t ≡ 1/16` (case (i),
`lam²/L² ≤ 1/16`), the merged mollifier `QopAlgebra_mollifier` (`QopAlgebra_mollifier_props`), `X ≡ 1`, and
tensors of `m + 1 = 2` (`m = 1`) and `m + 1 = 4` (`m = 3`) indices.  The hypotheses of the pins that are the
outputs of other gates stay hypotheses of the examples (`STKbound`, `STKward`, `STLK`, `STStep2Concl`, and
the induction bound `Ξ̂ ≺ X`); every deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`,
case (i), `(con_st_ind)`, `1 ≤ X`, the properties of the mollifier) is discharged. -/
