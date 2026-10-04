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

/-- **`(jywiiwsoks)`, deterministic window step.**  For alternating `σ` (`σ_last = ¬σ_0`), Ward's
identity at the last label reduces `𝒫(𝓛-𝒦)^{(m+2)}` to `(2iW^dη)⁻¹` times the difference of two `𝒫`
of `(𝓛-𝒦)^{(m+1)}`, each split into the window `diam_∞ < R` and its complement. -/
theorem B45_Psum_LK_le (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz.SeqΩ)
    {m : ℕ} (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a₁ : Zd d (sz.L n))
    {R Y F : ℝ} (hR : 0 ≤ R) (hF0 : 0 ≤ F)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKtensor sz n E u ω σ' a'‖ ≤ Y)
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)), a' 0 = a₁ →
      R ≤ (STdiamInf a' : ℝ) → ‖STLKtensor sz n E u ω σ' a'‖ ≤ F) :
    ‖STPsum (d := d) (STLKtensor sz n E u ω σ) a₁‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ *
        (((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F) := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hP : ∀ b : Bool, ‖STPsum (d := d) (STLKtensor sz n E u ω (B45_sgnCons b σ)) a₁‖ ≤
      ((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F := fun b =>
    B45_Psum_le _ a₁ hR (hY _) hF0 (fun a' h0 hfar => hF _ a' h0 hfar)
  have hsum : STPsum (d := d) (STLKtensor sz n E u ω σ) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (STPsum (d := d) (STLKtensor sz n E u ω (B45_sgnCons true σ)) a₁ -
          STPsum (d := d) (STLKtensor sz n E u ω (B45_sgnCons false σ)) a₁) := by
    rw [B45_Psum_snoc]
    simp only [B45_ward_fin sz n hE hu0 hu1 ω σ hσ]
    unfold STPsum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum, norm_mul, B45_norm_kappa sz n hE hu1]
  have hd := norm_sub_le (STPsum (d := d) (STLKtensor sz n E u ω (B45_sgnCons true σ)) a₁)
    (STPsum (d := d) (STLKtensor sz n E u ω (B45_sgnCons false σ)) a₁)
  have h2 := add_le_add (hP true) (hP false)
  have hpos : 0 ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E u))⁻¹ := by positivity
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E u))⁻¹ * ‖STPsum (d := d) (STLKtensor sz n E u ω (B45_sgnCons true σ)) a₁ -
          STPsum (d := d) (STLKtensor sz n E u ω (B45_sgnCons false σ)) a₁‖
      ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E u))⁻¹ * (2 * (((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = _ := by
        rw [mul_inv]; field_simp

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

section Adjacent

variable {d L : ℕ} [NeZero L]

private theorem B45_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem B45_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

omit [NeZero L] in
private theorem B45_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

private theorem B45_zdistInf_comm (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a, B45_zdistInf_neg]

private theorem B45_zdistInf_tri (a b c : Zd d L) :
    zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
  have := B45_zdistInf_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

/-- `2 |x|_∞ ≤ L`: no two labels are farther than `L/2` on the torus. -/
private theorem B45_two_mul_zdistInf_le (x : Zd d L) : 2 * zdistInf d L x ≤ L := by
  have h : zdistInf d L x ≤ L / 2 := by
    unfold zdistInf
    refine Finset.sup_le fun i _ => ?_
    unfold zdist
    omega
  omega

/-- `diam_∞ a ≤ L / 2`. -/
private theorem B45_two_mul_diam_le {k : ℕ} (a : Fin k → Zd d L) :
    2 * STdiamInf a ≤ L := by
  have h : STdiamInf a ≤ L / 2 := by
    unfold STdiamInf
    refine Finset.sup_le fun p _ => ?_
    have := B45_two_mul_zdistInf_le (a p.1 - a p.2)
    omega
  omega

/-- `diam_∞ a ≤ KLmaxDist a` (`zdistInf ≤ zdistD`). -/
private theorem B45_diam_le_KLmaxDist {k : ℕ} (a : Fin k → Zd d L) :
    STdiamInf a ≤ KLmaxDist d L a := by
  unfold STdiamInf
  refine Finset.sup_le fun p _ => ?_
  exact (zdistInf_le_zdistD d L _).trans
    (Finset.le_sup (f := fun q : Fin k × Fin k => zdistD d L (a q.1 - a q.2)) (Finset.mem_univ p))

/-- `diam_∞ a = 0` for a single label. -/
private theorem B45_diam_one (a : Fin 1 → Zd d L) : STdiamInf a = 0 := by
  unfold STdiamInf
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun p _ => ?_
  have : p.1 = p.2 := Subsingleton.elim _ _
  simp [this, B45_zdistInf_zero]

/-- **Some adjacent pair is far.**  `diam_∞ a ≤ (k-1) |a_m - a_{m+1}|_∞` for some `m + 1 < k`
(triangle inequality along the chain `a_i, a_{i+1}, …, a_j`, which has at most `k - 1` steps). -/
private theorem B45_adjacent {k : ℕ} (hk : 2 ≤ k) (a : Fin k → Zd d L) :
    ∃ (m : ℕ) (h : m + 1 < k),
      STdiamInf a ≤ (k - 1) * zdistInf d L (a ⟨m, by omega⟩ - a ⟨m + 1, h⟩) := by
  classical
  let a' : ℕ → Zd d L := fun i => if h : i < k then a ⟨i, h⟩ else 0
  have ha' : ∀ i (h : i < k), a' i = a ⟨i, h⟩ := fun i h => by simp [a', h]
  let δ : ℕ → ℕ := fun i => zdistInf d L (a' i - a' (i + 1))
  have hne : (Finset.range (k - 1)).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨m, hm, hΔ⟩ := Finset.exists_mem_eq_sup (Finset.range (k - 1)) hne δ
  have hm' : m + 1 < k := by have := Finset.mem_range.mp hm; omega
  refine ⟨m, hm', ?_⟩
  set Δ := (Finset.range (k - 1)).sup δ with hΔdef
  have hδΔ : ∀ i, i + 1 < k → δ i ≤ Δ := fun i hi =>
    Finset.le_sup (f := δ) (Finset.mem_range.mpr (by omega))
  have hchain : ∀ e i, i + e < k → zdistInf d L (a' i - a' (i + e)) ≤ e * Δ := by
    intro e
    induction e with
    | zero =>
      intro i _
      simp [B45_zdistInf_zero]
    | succ e ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hδΔ (i + e) (by omega)
      have h3 := B45_zdistInf_tri (a' i) (a' (i + e)) (a' (i + (e + 1)))
      have h4 : δ (i + e) = zdistInf d L (a' (i + e) - a' (i + (e + 1))) := by
        simp only [δ]; rfl
      rw [h4] at h2
      calc zdistInf d L (a' i - a' (i + (e + 1)))
          ≤ zdistInf d L (a' i - a' (i + e)) + zdistInf d L (a' (i + e) - a' (i + (e + 1))) := h3
        _ ≤ e * Δ + Δ := by omega
        _ = (e + 1) * Δ := by ring
  have hmax : STdiamInf a ≤ (k - 1) * Δ := by
    unfold STdiamInf
    refine Finset.sup_le fun p _ => ?_
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
    simp only
    rcases le_total i j with hij | hij
    · have := hchain (j - i) i (by omega)
      rw [show i + (j - i) = j by omega, ha' i hi, ha' j hj] at this
      calc _ ≤ (j - i) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
    · have := hchain (i - j) j (by omega)
      rw [show j + (i - j) = i by omega, ha' i hi, ha' j hj] at this
      rw [B45_zdistInf_comm]
      calc _ ≤ (i - j) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
  have hmm : Δ = zdistInf d L (a ⟨m, by omega⟩ - a ⟨m + 1, hm'⟩) := by
    rw [hΔ]
    simp only [δ]
    rw [ha' m (by omega), ha' (m + 1) hm']
  rw [← hmm]
  exact hmax

end Adjacent

section Cut

variable {d L W : ℕ} [NeZero L]

private theorem B45_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) :
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

/-- Cyclic invariance of `𝓛`: moving the first edge to the end (trace cyclicity). -/
private theorem B45_loopL_rotate (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s : Bool)
    (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    loopL d L W H z ⟨s :: σ, b :: a⟩ = loopL d L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [B45_loopL_eq_prod, B45_loopL_eq_prod]
  simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
  rw [List.zip_append h]
  simp only [List.map_append, List.prod_append, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

/-- Rotating a loop by `j` positions does not change `𝓛`. -/
private theorem B45_loopL_rotate_iter {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} :
    ∀ (j : ℕ) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      loopL d L W H z ⟨σ.rotate j, a.rotate j⟩ = loopL d L W H z ⟨σ, a⟩ := by
  intro j
  induction j with
  | zero => intro σ a _; simp
  | succ j ih =>
    intro σ a h
    cases σ with
    | nil =>
      have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst this; simp
    | cons s σ =>
      cases a with
      | nil => simp at h
      | cons b a =>
        have h' : σ.length = a.length := by simpa using h
        rw [List.rotate_cons_succ, List.rotate_cons_succ]
        rw [ih (σ ++ [s]) (a ++ [b]) (by simp [h'])]
        exact (B45_loopL_rotate H z s b σ a h').symm

variable [NeZero W]

/-- **The cut.**  For a loop of length `k ≥ 2` and `m + 1 < k`, with `s = σ_{m+1}`,
`b' = a_{m+1}`, `b = a_m`: `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛 ⟨[s, !s], [b', b]⟩|`.  The loop is rotated by
`m + 1` so that `(a_{m+1}, a_m)` is (first label, last label), then cut into the one-`G` chain
`G_{σ_{m+1}}` and the `(k-1)`-chain; `norm_sq_gloop_le_symIdx` (Cauchy-Schwarz) and
`norm_gloop_le_of_le_abs_im` (operator norm bound of the symmetric `(k-1)`-loop) finish. -/
private theorem B45_cut
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) {k : ℕ} (hk : 2 ≤ k) (σl : List Bool) (al : List (Zd d L))
    (hσ : σl.length = k) (ha : al.length = k) (m : ℕ) (hm : m + 1 < k) :
    ∃ (s : Bool) (b' b : Zd d L), σl[m + 1]? = some s ∧ al[m + 1]? = some b' ∧ al[m]? = some b ∧
      ‖loopL d L W H z ⟨σl, al⟩‖ ^ 2 ≤
        η⁻¹ ^ (2 * (k - 1)) * ‖loopL d L W H z ⟨[s, !s], [b', b]⟩‖ := by
  have hlen : σl.length = al.length := by omega
  have hrot := B45_loopL_rotate_iter (H := H) (z := z) (m + 1) σl al hlen
  obtain ⟨σA, σB, aA, aB, b', b, hσeq, haeq, hσA, haA, hσB, haB⟩ :=
    exists_split_loopIdx (k₁ := 1) (k₂ := k - 1) (by omega) (by omega)
      (σ := σl.rotate (m + 1)) (a := al.rotate (m + 1)) (by simp [hσ]; omega) (by simp [ha]; omega)
  have haA0 : aA = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨s, hs⟩ : ∃ s, σA = [s] := by
    match σA, hσA with
    | [s], _ => exact ⟨s, rfl⟩
  subst haA0
  subst hs
  refine ⟨s, b', b, ?_, ?_, ?_, ?_⟩
  · have h1 : (σl.rotate (m + 1))[0]? = some s := by
      rw [hσeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % σl.length = m + 1 := by
      rw [hσ]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[0]? = some b' := by
      rw [haeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % al.length = m + 1 := by
      rw [ha]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[k - 1]? = some b := by
      have : (al.rotate (m + 1)).getLast? = some b := by
        rw [haeq, List.nil_append, List.singleton_append, ← List.cons_append, List.getLast?_concat]
      rwa [List.getLast?_eq_getElem?, List.length_rotate, ha] at this
    rw [List.getElem?_rotate (by omega)] at h1
    have : (k - 1 + (m + 1)) % al.length = m := by
      rw [ha]
      have : k - 1 + (m + 1) = m + k := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rwa [this] at h1
  · rw [← hrot, hσeq, haeq]
    have h := norm_sq_gloop_le_symIdx (z := z) hH (σA := [s]) (σB := σB) (aA := []) (aB := aB)
      (by simp) (by omega) b' b
    refine h.trans ?_
    have hsym : symIdx [s] ([] : List (Zd d L)) b' b = ⟨[s, !s], [b', b]⟩ := by
      simp [symIdx]
    rw [hsym, mul_comm (η⁻¹ ^ (2 * (k - 1)))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hB := norm_gloop_le_of_le_abs_im (z := z) (W := W) hH hη hz (symIdx σB aB b b')
      (by simp; omega) (by simp; omega)
    refine hB.trans ?_
    simp only [symIdx_a_length]
    have h2 : 2 * (aB.length + 1) = 2 * (k - 1) := by omega
    rw [h2]
    have hW : (((W : ℝ) ^ d)⁻¹) ≤ 1 := by
      have : (1 : ℝ) ≤ (W : ℝ) ^ d :=
        one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W))
      exact inv_le_one_of_one_le₀ this
    have hW' : (((W : ℝ) ^ d)⁻¹) ^ (2 * (k - 1) - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) hW
    calc η⁻¹ ^ (2 * (k - 1)) * (((W : ℝ) ^ d)⁻¹) ^ (2 * (k - 1) - 1)
        ≤ η⁻¹ ^ (2 * (k - 1)) * 1 := by gcongr
      _ = _ := mul_one _

/-- `⟨[s, !s], [b', b]⟩` is the `(+,-)` two-loop at `(b', b)` (`s = +`) or at `(b, b')`
(`s = -`, by one rotation). -/
private theorem B45_loopL_two_sign {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (s : Bool) (b' b : Zd d L) :
    loopL d L W H z ⟨[s, !s], [b', b]⟩ =
      loopL d L W H z ⟨[true, false], [if s then b' else b, if s then b else b']⟩ := by
  cases s
  · have := B45_loopL_rotate (L := L) (W := W) H z false b' [true] [b] rfl
    simpa using this
  · simp

/-- **The far pair and the loop bound, with the pair independent of the matrix.**  For `k ≥ 2` there
is `c = (c₀, c₁)` (a function of `σ`, `a` only) with `diam_∞ a ≤ (k-1) |c₀ - c₁|_∞` and, for
every Hermitian `H` and `η ≤ |Im z|`, `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛_{(+,-),c}|`. -/
private theorem B45_pair {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ∃ c : Zd d L × Zd d L,
      ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d L (c.1 - c.2) : ℝ) ∧
      ∀ (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (η : ℝ), H.IsHermitian →
        0 < η → η ≤ |z.im| →
        ‖loopL d L W H z (loopOf σ a)‖ ^ 2 ≤
          η⁻¹ ^ (2 * (k - 1)) * ‖loopL d L W H z ⟨[true, false], [c.1, c.2]⟩‖ := by
  obtain ⟨m, hm, hmax⟩ := B45_adjacent hk a
  obtain ⟨s, hs⟩ : ∃ s : Bool, s = σ ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Zd d L, b' = a ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Zd d L, b = a ⟨m, by omega⟩ := ⟨_, rfl⟩
  refine ⟨(if s then b' else b, if s then b else b'), ?_, ?_⟩
  · have hcast : ((STdiamInf a : ℕ) : ℝ) ≤
        (((k - 1 : ℕ) : ℝ)) * (zdistInf d L (b - b') : ℝ) := by
      rw [hb, hb']
      exact_mod_cast hmax
    have hk1 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hk1] at hcast
    cases s
    · simpa using hcast
    · simp only [ite_true]
      rw [B45_zdistInf_comm]
      simpa using hcast
  · intro H z η hH hη hz
    obtain ⟨s', b'', b''', hs', hb'', hb''', hbound⟩ := B45_cut (W := W) hH hη hz hk
      (List.ofFn σ) (List.ofFn a) (by simp) (by simp) m hm
    rw [List.getElem?_ofFn] at hs' hb'' hb'''
    simp only [hm, dite_true, show m < k by omega] at hs' hb'' hb'''
    have e1 : s' = s := by rw [hs]; exact (Option.some.inj hs').symm
    have e2 : b'' = b' := by rw [hb']; exact (Option.some.inj hb'').symm
    have e3 : b''' = b := by rw [hb]; exact (Option.some.inj hb''').symm
    rw [e1, e2, e3, B45_loopL_two_sign] at hbound
    exact hbound

end Cut

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

/-- **`1 - u ≥ N⁻¹` from the far premise.**  If `ℓ_u < L` (which the far premise
`ℓ_u W^{τ'} ≤ diam_∞ a ≤ L/2` gives) then `g² < L² (1 - u)`; with `g² ≥ W^{-d}` (`(eq:WO)`) and
`L² ≤ L^d` this is `1 - u > (W L)^{-d} = N⁻¹`. -/
private theorem B45_one_sub_u {d L W : ℕ} (hd : 2 ≤ d) (hL : 3 ≤ L) (hW : 1 ≤ W)
    {g u : ℝ} (hg : 0 < g) (hgW : ((W : ℝ) ^ d)⁻¹ ≤ g ^ 2) (hu : u < 1)
    (hℓ : ellT L g u < L) : ((((W * L) ^ d : ℕ) : ℝ))⁻¹ ≤ 1 - u := by
  have hv : 0 < 1 - u := by linarith
  have h1 : g / Real.sqrt |1 - u| < L := by
    unfold ellT at hℓ
    rcases min_lt_iff.mp hℓ with h | h
    · exact lt_of_le_of_lt (le_max_left _ _) h
    · exact absurd h (lt_irrefl _)
  rw [abs_of_pos hv] at h1
  have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr hv
  have h2 : g < L * Real.sqrt (1 - u) := by rwa [div_lt_iff₀ hs] at h1
  have h3 : g ^ 2 < (L : ℝ) ^ 2 * (1 - u) := by
    have := pow_lt_pow_left₀ h2 hg.le (two_ne_zero)
    rwa [mul_pow, Real.sq_sqrt hv.le] at this
  have hW0 : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have h4 : 1 ≤ (W : ℝ) ^ d * g ^ 2 := by
    have := mul_le_mul_of_nonneg_left hgW hW0.le
    rwa [mul_inv_cancel₀ hW0.ne'] at this
  have hL2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have hN : ((((W * L) ^ d : ℕ) : ℝ)) = (W : ℝ) ^ d * (L : ℝ) ^ d := by
    push_cast; ring
  have h5 : 1 ≤ ((((W * L) ^ d : ℕ) : ℝ)) * (1 - u) := by
    rw [hN]
    calc (1 : ℝ) ≤ (W : ℝ) ^ d * g ^ 2 := h4
      _ ≤ (W : ℝ) ^ d * ((L : ℝ) ^ 2 * (1 - u)) := by gcongr
      _ ≤ (W : ℝ) ^ d * ((L : ℝ) ^ d * (1 - u)) := by gcongr
      _ = _ := by ring
  have hNpos : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by rw [hN]; positivity
  calc ((((W * L) ^ d : ℕ) : ℝ))⁻¹ = ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * 1 := (mul_one _).symm
    _ ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * (((((W * L) ^ d : ℕ) : ℝ)) * (1 - u)) := by gcongr
    _ = 1 - u := by field_simp

/-- **`STWB ≤ 2` in the far regime**: `W^{-d} B_{u,K} ≤ (W^d g²)⁻¹ + (N (1-u))⁻¹ ≤ 2` once
`g² W^d ≥ 1` and `N (1-u) ≥ 1`. -/
private theorem B45_STWB_le {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (K : ℕ) (hu : u < 1)
    (hg : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)
    (hN : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u)) : STWB sz n u K ≤ 2 := by
  have hv : 0 < 1 - u := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  have hg2 : 0 < sz.lam n ^ 2 := by
    by_contra h
    push Not at h
    have : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hW0.le
    linarith
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  unfold STWB Bparam
  rw [abs_of_pos hv]
  have hT1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
      (sz.lam n ^ 2)⁻¹ := by
    have ha : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have hb : ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
    calc (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
        ≤ (sz.lam n ^ 2)⁻¹ * 1 := mul_le_mul ha hb (by positivity) (by positivity)
      _ = _ := mul_one _
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
        ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by gcongr
    _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
          (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hNe]; field_simp
    _ ≤ 1 + 1 := by
        gcongr <;> exact inv_le_one_of_one_le₀ ‹_›
    _ = 2 := by norm_num

/-- `STWB ≥ 0`. -/
private theorem B45_STWB_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (K : ℕ) :
    0 ≤ STWB sz n u K := by
  unfold STWB Bparam
  positivity

/-- The chain of inequalities for a far loop, in abstract real quantities: `Λ = |𝓛_{σ,a}|`,
`Lp = |𝓛_{(+,-),c}|`, `Kp = |𝒦_{(+,-),c}|`, `X = |(𝓛-𝒦)_{(+,-),c}|` bounded through the decay input
(`Pn` the prefactor, `Mi = STWB(u,|c₀-c₁|) ≤ Θ`, `ex = exp(-√(|c₀-c₁|_∞/ℓ_u))`), `Kc = |𝒦_{σ,a}|`,
`ηi = η_u⁻¹`; with `Q = 2D' + A(2(k-1) + 1 + C₀) + 1`, `A = 1/𝔠` and `N ≤ W^A`, then
`2Λ + Kc ≤ W^{-D'}` once `W ≥ max(2, 16 Γ^{2(k-1)}(2 + Θ))`.  (RBM2D `DecayLoop_alg`, with
`M_u^{-2} ≤ Γ²` replaced by the constant `Θ`.) -/
private theorem B45_alg {W N Γ Θ A ηi Λ Kp X Kc Lp Pn Mi ex : ℝ} {k : ℕ} {D' C₀ Q : ℝ}
    (hk : 2 ≤ k) (hC₀ : 0 ≤ C₀) (hΓ : 0 ≤ Γ) (hΘ : 0 ≤ Θ)
    (hW : 2 ≤ W) (hWmin : 16 * Γ ^ (2 * (k - 1)) * (2 + Θ) ≤ W)
    (hN1 : 1 ≤ N) (hNW : N ≤ W ^ A)
    (hQ : Q = 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1)
    (hηi0 : 0 ≤ ηi) (hηi : ηi ≤ Γ * N)
    (hΛ0 : 0 ≤ Λ) (hLp0 : 0 ≤ Lp) (hΛ : Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp)
    (hLp : Lp ≤ Kp + X) (hKp : Kp ≤ W ^ (-Q))
    (hX : X ≤ N * (Pn * Mi * ex + W ^ (-Q)))
    (hPn : Pn ≤ N ^ C₀) (hMi : Mi ≤ Θ) (hex : ex ≤ W ^ (-Q))
    (hMi0 : 0 ≤ Mi) (hex0 : 0 ≤ ex)
    (hKc : Kc ≤ W ^ (-(D' + 1))) :
    2 * Λ + Kc ≤ W ^ (-D') := by
  have hW0 : 0 < W := by linarith
  have hWQ : 0 < W ^ (-Q) := Real.rpow_pos_of_pos hW0 _
  have hN0 : 0 < N := by linarith
  set r : ℝ := 2 * ((k : ℝ) - 1) + 1 + C₀ with hr
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 ≤ r := by rw [hr]; nlinarith
  -- Step 1: Kp + X ≤ W^{-Q} (2 + Θ) N^{1 + C₀}
  have hN1C : 1 ≤ N ^ (1 + C₀) := Real.one_le_rpow hN1 (by linarith)
  have hNN1C : N ≤ N ^ (1 + C₀) := by
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (1 + C₀) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hPMe : Pn * Mi * ex ≤ N ^ C₀ * Θ * W ^ (-Q) := by
    have h1 : Pn * Mi ≤ N ^ C₀ * Θ := mul_le_mul hPn hMi hMi0 (by positivity)
    exact mul_le_mul h1 hex hex0 (mul_nonneg (by positivity) hΘ)
  have hX2 : X ≤ W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := by
    calc X ≤ N * (Pn * Mi * ex + W ^ (-Q)) := hX
      _ ≤ N * (N ^ C₀ * Θ * W ^ (-Q) + W ^ (-Q)) := by gcongr
      _ = W ^ (-Q) * (Θ * (N * N ^ C₀) + N) := by ring
      _ = W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := by
        rw [Real.rpow_add hN0, Real.rpow_one]
  have hKX : Kp + X ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := by
    calc Kp + X ≤ W ^ (-Q) + W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := add_le_add hKp hX2
      _ = W ^ (-Q) * (1 + (Θ * N ^ (1 + C₀) + N)) := by ring
      _ ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := by
        apply mul_le_mul_of_nonneg_left _ hWQ.le
        nlinarith
  -- Step 2: Λ² ≤ Γ^{2(k-1)} (2+Θ) N^r W^{-Q}
  have hηpow : ηi ^ (2 * (k - 1)) ≤ (Γ * N) ^ (2 * (k - 1)) := pow_le_pow_left₀ hηi0 hηi _
  have hLpb : Lp ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := hLp.trans hKX
  have hexp : ((2 * (k - 1) : ℕ) : ℝ) = 2 * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
  have hNr' : N ^ (2 * (k - 1)) * N ^ (1 + C₀) = N ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0, hexp]
    congr 1; rw [hr]; ring
  have hΛ2 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := by
    have hηnn : 0 ≤ ηi ^ (2 * (k - 1)) := by positivity
    calc Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp := hΛ
      _ ≤ (Γ * N) ^ (2 * (k - 1)) * (W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀))) := by
        gcongr
      _ = Γ ^ (2 * (k - 1)) * (2 + Θ) * ((N ^ (2 * (k - 1)) * N ^ (1 + C₀)) * W ^ (-Q)) := by
        rw [mul_pow]; ring
      _ = Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := by rw [hNr']
  -- Step 3: N^r ≤ W^{A r}, W^{A r} W^{-Q} = W^{-D'}² W⁻¹
  have hNr : N ^ r ≤ W ^ (A * r) := by
    calc N ^ r ≤ (W ^ A) ^ r := Real.rpow_le_rpow hN0.le hNW hr0
      _ = W ^ (A * r) := (Real.rpow_mul hW0.le A r).symm
  have ht0 : 0 < W ^ (-D') := Real.rpow_pos_of_pos hW0 _
  have hWQ' : W ^ (A * r) * W ^ (-Q) = (W ^ (-D')) ^ 2 * W⁻¹ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le,
      ← Real.rpow_neg_one, ← Real.rpow_add hW0]
    congr 1
    rw [hQ]; push_cast; ring
  have hΛ3 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * ((W ^ (-D')) ^ 2 * W⁻¹) := by
    have hc : 0 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) := mul_nonneg (by positivity) (by linarith)
    calc Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := hΛ2
      _ ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (W ^ (A * r) * W ^ (-Q)) := by gcongr
      _ = _ := by rw [hWQ']
  -- Step 4: 2 Λ ≤ W^{-D'}/2
  have hcoef : 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹ ≤ 1 / 4 := by
    have h1 : 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹ =
        (16 * Γ ^ (2 * (k - 1)) * (2 + Θ)) / (4 * W) := by
      field_simp; ring
    rw [h1, div_le_iff₀ (by positivity)]
    nlinarith
  have h2Λ : 2 * Λ ≤ W ^ (-D') / 2 := by
    have hsq : (2 * Λ) ^ 2 ≤ (W ^ (-D') / 2) ^ 2 := by
      calc (2 * Λ) ^ 2 = 4 * Λ ^ 2 := by ring
        _ ≤ 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ) * ((W ^ (-D')) ^ 2 * W⁻¹)) := by gcongr
        _ = (4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹) * (W ^ (-D')) ^ 2 := by ring
        _ ≤ (1 / 4) * (W ^ (-D')) ^ 2 := by gcongr
        _ = (W ^ (-D') / 2) ^ 2 := by ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  -- Step 5: Kc ≤ W^{-D'}/2
  have hKc' : Kc ≤ W ^ (-D') / 2 := by
    have : W ^ (-(D' + 1)) = W ^ (-D') * W⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hW0]; congr 1; ring
    have h3 : W⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW
    calc Kc ≤ W ^ (-(D' + 1)) := hKc
      _ = W ^ (-D') * W⁻¹ := this
      _ ≤ W ^ (-D') * (1 / 2) := by gcongr
      _ = W ^ (-D') / 2 := by ring
  linarith

/-- `exp(-√x) ≤ W^{-Q}` for `x ≥ (W^{τ'/2}/K)²`, eventually in `W` (`log W ≤ W^{τ'/4}/(τ'/4)`). -/
private theorem B45_exp_small {τ' : ℝ} (hτ' : 0 < τ') {K Q : ℝ} (hK : 0 < K) (hQ : 0 ≤ Q) :
    ∀ᶠ w : ℝ in atTop, ∀ x : ℝ, (w ^ (τ' / 2) / K) ^ 2 ≤ x →
      Real.exp (-Real.sqrt x) ≤ w ^ (-Q) := by
  have hev : ∀ᶠ w : ℝ in atTop, 4 * Q * K / τ' ≤ w ^ (τ' / 4) :=
    (tendsto_rpow_atTop (by linarith : 0 < τ' / 4)).eventually_ge_atTop _
  filter_upwards [hev, eventually_gt_atTop 0] with w hw hw0
  intro x hx
  have hpos : 0 ≤ w ^ (τ' / 2) / K := by positivity
  have hsq : w ^ (τ' / 2) / K ≤ Real.sqrt x := by
    calc w ^ (τ' / 2) / K = Real.sqrt ((w ^ (τ' / 2) / K) ^ 2) := (Real.sqrt_sq hpos).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hlog : Real.log w ≤ w ^ (τ' / 4) / (τ' / 4) :=
    Real.log_le_rpow_div hw0.le (by linarith)
  have hQlog : Q * Real.log w ≤ w ^ (τ' / 2) / K := by
    have h1 : Q * Real.log w ≤ Q * (w ^ (τ' / 4) / (τ' / 4)) := by gcongr
    have h2 : Q * (w ^ (τ' / 4) / (τ' / 4)) = (4 * Q / τ') * w ^ (τ' / 4) := by
      field_simp
    have h3 : w ^ (τ' / 2) = w ^ (τ' / 4) * w ^ (τ' / 4) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    have hw4 : 0 < w ^ (τ' / 4) := Real.rpow_pos_of_pos hw0 _
    have h4 : (4 * Q / τ') * w ^ (τ' / 4) ≤ w ^ (τ' / 2) / K := by
      rw [h3, le_div_iff₀ hK]
      have : 4 * Q / τ' * K ≤ w ^ (τ' / 4) := by
        have : 4 * Q * K / τ' = 4 * Q / τ' * K := by ring
        linarith
      nlinarith
    linarith
  calc Real.exp (-Real.sqrt x) ≤ Real.exp (-(Q * Real.log w)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = w ^ (-Q) := by
        rw [Real.rpow_def_of_pos hw0]; congr 1; ring

/-- From `ℓ W^{τ'} ≤ (k-1) δ` and `k - 1 ≤ W^{τ'/2}`: `ℓ W^{τ'/2} ≤ δ` and
`(W^{τ'/2}/k)² ≤ δ/ℓ` (the two thresholds used for `STKcalDecay` at length `2` and for the
exponential). -/
private theorem B45_real_geom {Wr ℓ δ τ' kk : ℝ} (hW : 0 < Wr) (hℓ : 0 < ℓ) (hδ0 : 0 ≤ δ)
    (hk : 2 ≤ kk) (hWk : kk - 1 ≤ Wr ^ (τ' / 2)) (hδ : ℓ * Wr ^ τ' ≤ (kk - 1) * δ) :
    ℓ * Wr ^ (τ' / 2) ≤ δ ∧ (Wr ^ (τ' / 2) / kk) ^ 2 ≤ δ / ℓ := by
  have hs : 0 < Wr ^ (τ' / 2) := Real.rpow_pos_of_pos hW _
  have h1 : Wr ^ τ' = Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  have hk1 : 0 < kk - 1 := by linarith
  constructor
  · have h2 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ (kk - 1) * δ := by
      calc ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ ℓ * Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by gcongr
        _ = ℓ * Wr ^ τ' := by rw [h1]; ring
        _ ≤ _ := hδ
    have h3 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ δ * (kk - 1) := by linarith
    exact le_of_mul_le_mul_right h3 hk1
  · have hkk : 0 < kk := by linarith
    rw [div_pow, div_le_div_iff₀ (by positivity) hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    have h4 : (τ' / 2) * ((2 : ℕ) : ℝ) = τ' := by push_cast; ring
    rw [h4]
    calc Wr ^ τ' * ℓ = ℓ * Wr ^ τ' := mul_comm _ _
      _ ≤ (kk - 1) * δ := hδ
      _ ≤ kk ^ 2 * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        nlinarith
      _ = δ * kk ^ 2 := mul_comm _ _

/-- `|a - b|_{ℓ¹} ≤ KLmaxDist ![a, b]`. -/
private theorem B45_zdistD_le_KLmaxDist_two {d L : ℕ} [NeZero L] (a b : Zd d L) :
    zdistD d L (a - b) ≤ KLmaxDist d L (![a, b] : Fin 2 → Zd d L) :=
  Finset.le_sup (f := fun q : Fin 2 × Fin 2 =>
    zdistD d L ((![a, b] : Fin 2 → Zd d L) q.1 - (![a, b] : Fin 2 → Zd d L) q.2))
    (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))

end Scales

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Far

variable {d : ℕ}

/-- **The far entries, uniformly in `u ∈ [s,t]`, for `k ≥ 2`** (`lem_decayLoop` `3_5:1126` over a window
with the time inside `≺`; the uniform form of `stDecayLoopPT_of_step2`, whose proof is the per-time form of
this one).  From the uniform decay input `STGdecayW` at the far pair `c = c(σ,a)`: on its good event the
deterministic chain `B45_alg` gives `(|𝓛| + |𝓛-𝒦|)_{u,σ,a} ≤ W^{-D'}` at every `u ∈ [s_n,t_n]`,
`σ`, far `a`.  Port of `DecayLoopA_main` (`DecayLoopA.lean:713`), the prefactor `P_u` now depends on `u`
and its bound `P_u ≤ N^{C₀}` is derived from the far premise (`1 - u ≥ N⁻¹`). -/
theorem B45_far_main (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n ≤ lemT (z n)) {Cd : ℝ}
    (hStep2 : STStep2Concl sz (STflowE z) s t Cd)
    {k : ℕ} (hk : 2 ≤ k) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  have hA := hflow.1
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  -- constants
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ, C₀ = max Cd 0 + 1 := ⟨_, rfl⟩
  have hC₀ : 0 ≤ C₀ := by rw [hC₀def]; have := le_max_right Cd 0; linarith
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 2 / Real.sqrt κ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 / 𝔠 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1 := ⟨_, rfl⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hQpos : 0 < Q := by
    have : 0 ≤ A * (2 * ((k : ℝ) - 1) + 1 + C₀) := mul_nonneg hA0 (by nlinarith)
    rw [hQ]; linarith
  -- choice of the far pair
  have hpair : ∀ (n : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ∃ c : Zd d (sz.L n) × Zd d (sz.L n),
        ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d (sz.L n) (c.1 - c.2) : ℝ) ∧
        ∀ (H : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (η : ℝ),
          H.IsHermitian → 0 < η → η ≤ |z.im| →
          ‖loopL d (sz.L n) (sz.W n) H z (loopOf σ a)‖ ^ 2 ≤
            η⁻¹ ^ (2 * (k - 1)) *
              ‖loopL d (sz.L n) (sz.W n) H z ⟨[true, false], [c.1, c.2]⟩‖ :=
    fun n σ a => B45_pair hk σ a
  choose cp hcp using hpair
  -- the pulled-back source
  have hpb : Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (STflowE z n) (p.1 : ℝ) ![true, false]
          ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2] ω -
        STKloop sz n (STflowE z n) (p.1 : ℝ) ![true, false]
          ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ)
            (zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2)) *
          Real.exp (-(((zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Q)) :=
    by
    intro τ₁ hτ₁ D₁ hD₁
    filter_upwards [hStep2.2.2 Q hQpos τ₁ hτ₁ D₁ hD₁] with n hn
    refine le_trans (measure_mono ?_) hn
    rintro ω ⟨p, hp⟩
    exact ⟨(p.1, ![true, false], ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]), hp⟩
  refine StochDomAt.of_subset hpb ?_
  intro τ₀ hτ₀
  refine ⟨1, one_pos, ?_⟩
  -- eventual facts
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hB h1
  have hK2 := RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ (k := 2) (by norm_num)
    (τ := τ' / 2) (D := Q) (by linarith) hQpos
  have hKk := RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ (k := k) (by omega)
    (τ := τ') (D := D' + 1) hτ' (by linarith)
  have hexp := hWtend.eventually
    (B45_exp_small (τ' := τ') hτ' (K := (k : ℝ)) (Q := Q) (by linarith) hQpos.le)
  have hW2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hWtend.eventually_ge_atTop 2
  have hWΓ : ∀ᶠ n : ℕ in atTop,
      16 * Γ ^ (2 * (k - 1)) * (2 + 2) ≤ ((sz.W n : ℕ) : ℝ) := hWtend.eventually_ge_atTop _
  have hWk : ∀ᶠ n : ℕ in atTop, (k : ℝ) - 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ' / 2)).comp hWtend).eventually_ge_atTop _
  have hN2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN.eventually_ge_atTop 2
  filter_upwards [hK2, hKk, hexp, hW2, hWΓ, hWk, hB, hWO, hN2] with n hK2n hKkn hexpn hW2n
    hWΓn hWkn hbwn hwo hN2n
  rintro ω ⟨⟨p, σ, a⟩, hlt⟩
  refine ⟨(p, σ, a), ?_⟩
  by_contra hnot
  dsimp only at hlt hnot
  -- the time
  obtain ⟨u, hus, hut⟩ := p
  dsimp only at hlt hnot ⊢
  have hu0 : 0 ≤ u := (hs n).trans hus
  have hu1 : u < 1 := (hut.trans (ht n)).trans_lt (lemT_lt_one (him n))
  have hsu : s n ≤ u := hus
  have hEn : |STflowE z n| ≤ 2 - κ := (abs_lemE_le (him n)).trans (hflow.2 n).1
  -- basic facts at the index n
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  -- not far: trivial
  by_cases hfar : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)
  swap
  · simp only [hfar, ↓reduceIte, mul_zero] at hlt
    have : 0 < ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') := by positivity
    linarith
  simp only [hfar, ↓reduceIte, mul_one] at hlt
  -- the scales: `g`, `1 - u`, `η`
  have hlam0 : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans
      (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) u := one_le_ellT hL1r
  have hℓpos : 0 < ellT (sz.L n) (sz.lam n) u := by linarith
  have hWτ : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW1r hτ'.le
  have hdiam : (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) / 2 := by
    have := B45_two_mul_diam_le a
    have h2 : (2 : ℝ) * (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hℓL : ellT (sz.L n) (sz.lam n) u < ((sz.L n : ℕ) : ℝ) := by
    have h3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL3
    calc ellT (sz.L n) (sz.lam n) u
        ≤ ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' :=
          le_mul_of_one_le_right hℓpos.le hWτ
      _ ≤ (STdiamInf a : ℝ) := hfar
      _ ≤ ((sz.L n : ℕ) : ℝ) / 2 := hdiam
      _ < _ := by linarith
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u :=
    B45_one_sub_u (by omega) hL3 hW1 hlam0 hgW hu1 hℓL
  have hv : 0 < 1 - u := by linarith
  have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := by
    have := mul_le_mul_of_nonneg_left hNu hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  have hμ : Real.sqrt κ / 2 ≤ (mE (STflowE z n)).im := B45_mE_im_ge hκ hEn
  have hη : 0 < etaT (STflowE z n) u := by
    have : 0 < (mE (STflowE z n)).im := lt_of_lt_of_le (by positivity) hμ
    exact mul_pos hv this
  have hηΓ : (etaT (STflowE z n) u)⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by
    have h1 : (1 - u) * (Real.sqrt κ / 2) ≤ etaT (STflowE z n) u :=
      mul_le_mul_of_nonneg_left hμ hv.le
    have h2 : (etaT (STflowE z n) u)⁻¹ ≤ ((1 - u) * (Real.sqrt κ / 2))⁻¹ :=
      inv_anti₀ (by positivity) h1
    have h3 : ((1 - u) * (Real.sqrt κ / 2))⁻¹ = Γ * (1 - u)⁻¹ := by
      rw [hΓ]; field_simp
    have h4 : (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    calc (etaT (STflowE z n) u)⁻¹ ≤ ((1 - u) * (Real.sqrt κ / 2))⁻¹ := h2
      _ = Γ * (1 - u)⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by gcongr
  have hMi : STWB sz n u (zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2)) ≤ 2 :=
    B45_STWB_le sz n _ hu1 hg1 hN1u
  -- the prefactor `P_u ≤ N^{C₀}`
  have hB2 : sz.Bctl n u ≤ 2 := B45_STWB_le sz n 0 hu1 hg1 hN1u
  have hB0 : 0 ≤ sz.Bctl n u := B45_STWB_nonneg sz n _ 0
  have hB5 : (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ 2 :=
    calc (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow hB0 hB2 (by norm_num)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hratio1 : 1 ≤ (1 - s n) / (1 - u) := by
    rw [le_div_iff₀ hv]; linarith only [hsu]
  have hratioN : (1 - s n) / (1 - u) ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [div_le_iff₀ hv]
    have h1 := mul_le_mul_of_nonneg_left hNu hNpos.le
    rw [mul_inv_cancel₀ hNpos.ne'] at h1
    linarith only [h1, hs n]
  have hpow : ((1 - s n) / (1 - u)) ^ Cd ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
    calc ((1 - s n) / (1 - u)) ^ Cd ≤ ((1 - s n) / (1 - u)) ^ (max Cd 0) :=
          Real.rpow_le_rpow_of_exponent_le hratio1 (le_max_left _ _)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
          Real.rpow_le_rpow (by linarith) hratioN (le_max_right _ _)
  have hNC : ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) =
      ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  have hP2n : ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ C₀ := by
    rw [hC₀def]
    calc ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * 2 :=
          mul_le_mul hpow hB5 (Real.rpow_nonneg hB0 _) (by positivity)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) := by gcongr
      _ = _ := hNC
  -- the matrix and the far pair
  have hMh : (sz.seqHflow n u ω).IsHermitian := Sizes.seqHflow_isHermitian sz n u ω
  have hHh : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω)).IsHermitian :=
    hMh.submatrix _
  have hzim : etaT (STflowE z n) u ≤ |(zt (STflowE z n) u).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hη]
  obtain ⟨hcmax, hcb⟩ := hcp n σ a
  have hΛ := hcb (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω)) (zt (STflowE z n) u)
    (etaT (STflowE z n) u) hHh hη hzim
  have hδ : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
      ((k : ℝ) - 1) * (zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2) : ℝ) :=
    hfar.trans hcmax
  obtain ⟨hfar2, hexarg⟩ := B45_real_geom hWpos hℓpos (Nat.cast_nonneg _) hk2 hWkn hδ
  -- the bounds on the far pair
  have hKp : ‖STKloop sz n (STflowE z n) u ![true, false]
      ![(cp n σ a).1, (cp n σ a).2]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    refine hK2n (STflowE z n) hEn u hu0 hu1 ![true, false]
      ![(cp n σ a).1, (cp n σ a).2] (hfar2.trans ?_)
    exact_mod_cast (zdistInf_le_zdistD d (sz.L n) _).trans
      (B45_zdistD_le_KLmaxDist_two (cp n σ a).1 (cp n σ a).2)
  have hKc : ‖STKloop sz n (STflowE z n) u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) :=
    hKkn (STflowE z n) hEn u hu0 hu1 σ a
      (hfar.trans (by exact_mod_cast B45_diam_le_KLmaxDist a))
  have hex : Real.exp (-(((zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    have := hexpn _ hexarg
    rwa [Real.sqrt_eq_rpow] at this
  have hL2 : Lloop sz n (STflowE z n) u ![true, false] ![(cp n σ a).1, (cp n σ a).2] ω =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω))
        (zt (STflowE z n) u) ⟨[true, false], [(cp n σ a).1, (cp n σ a).2]⟩ := by
    refine (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ ![true, false]
      ![(cp n σ a).1, (cp n σ a).2]).trans ?_
    simp [loopOf, List.ofFn_succ]
  have hLσ : Lloop sz n (STflowE z n) u σ a ω =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω))
        (zt (STflowE z n) u) (loopOf σ a) :=
    loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
  have hLp : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n u ω))
        (zt (STflowE z n) u) ⟨[true, false], [(cp n σ a).1, (cp n σ a).2]⟩‖ ≤
      ‖STKloop sz n (STflowE z n) u ![true, false] ![(cp n σ a).1, (cp n σ a).2]‖ +
        ‖Lloop sz n (STflowE z n) u ![true, false] ![(cp n σ a).1, (cp n σ a).2] ω -
          STKloop sz n (STflowE z n) u ![true, false] ![(cp n σ a).1, (cp n σ a).2]‖ := by
    rw [← hL2]
    exact norm_le_norm_add_norm_sub' _ _
  have hX := not_lt.mp hnot
  rw [Real.rpow_one] at hX
  have hNW : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ A := by
    calc ((sz.size n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (1 / 𝔠) := by
          rw [← Real.rpow_mul hNpos.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := Real.rpow_le_rpow (by positivity) hbwn (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ A := by rw [hAdef]
  have key := B45_alg (W := ((sz.W n : ℕ) : ℝ)) (N := ((sz.size n : ℕ) : ℝ)) (Γ := Γ)
    (Θ := 2) (A := A) (k := k) (D' := D') (C₀ := C₀) (Q := Q)
    (Λ := ‖Lloop sz n (STflowE z n) u σ a ω‖) hk hC₀ hΓ0 (by norm_num) hW2n
    hWΓn hN1 hNW hQ (inv_nonneg.mpr hη.le) hηΓ (norm_nonneg _) (norm_nonneg _)
    (by rw [hLσ]; exact hΛ) hLp hKp hX hP2n hMi hex (B45_STWB_nonneg sz n _ _)
    (Real.exp_pos _).le hKc
  have hlk : ‖Lloop sz n (STflowE z n) u σ a ω - STKloop sz n (STflowE z n) u σ a‖ ≤
      ‖Lloop sz n (STflowE z n) u σ a ω‖ + ‖STKloop sz n (STflowE z n) u σ a‖ := norm_sub_le _ _
  have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀.le
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_pos_of_pos hWpos _
  have hle : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
    le_mul_of_one_le_left hWD.le hNτ
  linarith only [hlt, key, hlk, hle]

end Far

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Far1

variable {d : ℕ}

/-- The far entries, uniformly in `u ∈ [s,t]`, for every length `k ≥ 1` (for `k = 1` the far set is
empty: `diam_∞ a = 0 < ℓ_u W^{τ'}`). -/
theorem B45_far (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n ≤ lemT (z n)) {Cd : ℝ}
    (hStep2 : STStep2Concl sz (STflowE z) s t Cd)
    {k : ℕ} (hk : 1 ≤ k) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    refine sz.prec_of_le (fun n u ω => (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _).le)
      (fun n p ω => ?_)
    have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hpos : 0 < ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' :=
      mul_pos (ellT_pos hL) (Real.rpow_pos_of_pos hW _)
    have hmax : (STdiamInf p.2.2 : ℝ) = 0 := by
      rw [B45_diam_one]; simp
    have hnot : ¬ (ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
        (STdiamInf p.2.2 : ℝ)) := by
      rw [hmax]; exact not_le.mpr hpos
    simp only [hnot, ↓reduceIte, mul_zero]
    exact (Real.rpow_pos_of_pos hW _).le
  · exact B45_far_main hd sz hκ hflow hs hst ht hStep2 hk2 hτ' hD'

end Far1

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

private theorem B45_ellT_eq_one {g τ : ℝ} (hτ : τ < 1) (hL : 1 ≤ L)
    (h : g / Real.sqrt (1 - τ) ≤ 1) : ellT L g τ = 1 := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold ellT
  rw [abs_of_pos (by linarith : 0 < 1 - τ), max_eq_right h]
  exact min_eq_left hLr

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

section VthSup

variable {d L m : ℕ} [NeZero L]

/-- **The sup bound of the mollifier for every real `c`**: for `0 ≤ t < 1`,
`‖ϑ_t(a)‖ ≤ C (e^{|c| m d / 2} + 2/(dm) + 2 max(0, -log g)) (ℓ_t^d)^{-m}`.  For `c ≥ 0` the factor
`exp(-c S/ℓ)` is `≤ 1` and the pin gives `C ℓ^{-dm}` directly; for `c < 0` the three windows
(`ℓ_t = L`, `1 ≤ g/√(1-t) ≤ L`, `ℓ_t = 1`) are controlled by `B45_vth_mid` and the logarithmic
integral `∫ C/(1-τ)` over `1 - τ ∈ [g², 1-t]` (the loss `log(1/g²) ≤ log N`). -/
theorem B45_vth_sup (hL : 3 ≤ L) {g C c : ℝ} (hg : 0 < g)
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (h : STMollifierProps (d := d) g C c ϑ)
    (hdm : 1 ≤ d * m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin (m + 1) → Zd d L) :
    ‖ϑ t a‖ ≤ (C * (Real.exp (|c| * ((m : ℝ) * d / 2)) + 2 / ((d * m : ℕ) : ℝ) +
        2 * max 0 (-Real.log g))) * (((ellT L g t) ^ d)⁻¹) ^ m := by
  have hL1 : 1 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hC := B45_C_nonneg hL hg h
  have hv : 0 < 1 - t := by linarith
  have hsq : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 hv
  have hdm0 : (0 : ℝ) < ((d * m : ℕ) : ℝ) := by exact_mod_cast hdm
  have hKe : 0 < Real.exp (|c| * ((m : ℝ) * d / 2)) := Real.exp_pos _
  have hlg : 0 ≤ max 0 (-Real.log g) := le_max_left _ _
  set Kc := Real.exp (|c| * ((m : ℝ) * d / 2)) with hKc
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT hLr
  have hQ0 : 0 ≤ (((ellT L g t) ^ d)⁻¹) ^ m := by positivity
  have hQ1 : (((ellT L g t) ^ d)⁻¹) ^ m ≤ 1 := by
    have h1 : 1 ≤ (ellT L g t) ^ d := one_le_pow₀ hℓ1
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
  have hΛ : C * (Kc + 2 / ((d * m : ℕ) : ℝ)) ≤
      C * (Kc + 2 / ((d * m : ℕ) : ℝ) + 2 * max 0 (-Real.log g)) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  rcases le_total (L : ℝ) (g / Real.sqrt (1 - t)) with hxL | hxL
  · -- `ℓ_t = L`
    have hℓ : ellT L g t = L := B45_ellT_eq_L ht1 hL1 hxL
    have h2 := h.2.1 t ht0 ht1 a
    rw [hℓ] at h2 ⊢
    refine h2.trans ?_
    have h3 := B45_exp_at_L (d := d) (m := m) g c a hL1
    have h4 : C * (((L : ℝ) ^ d)⁻¹) ^ m * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
        (zdistD d L (a i - a 0) : ℝ)) / (L : ℝ)) ≤ C * (((L : ℝ) ^ d)⁻¹) ^ m * Kc :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    refine h4.trans ?_
    have h5 : 0 ≤ (((L : ℝ) ^ d)⁻¹) ^ m := by positivity
    calc C * (((L : ℝ) ^ d)⁻¹) ^ m * Kc = (C * Kc) * (((L : ℝ) ^ d)⁻¹) ^ m := by ring
      _ ≤ (C * (Kc + 2 / ((d * m : ℕ) : ℝ) + 2 * max 0 (-Real.log g))) * (((L : ℝ) ^ d)⁻¹) ^ m := by
        apply mul_le_mul_of_nonneg_right _ h5
        have : 0 ≤ 2 / ((d * m : ℕ) : ℝ) := by positivity
        have h6 : C * Kc ≤ C * (Kc + 2 / ((d * m : ℕ) : ℝ) + 2 * max 0 (-Real.log g)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
        exact h6
  · rcases le_total 1 (g / Real.sqrt (1 - t)) with hx1 | hx1
    · -- `1 ≤ x ≤ L`
      have := B45_vth_mid hL hg h hdm ht0 ht1 hx1 hxL a
      refine this.trans ?_
      have : (C * Kc + 2 * C / ((d * m : ℕ) : ℝ)) =
          C * (Kc + 2 / ((d * m : ℕ) : ℝ)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hΛ hQ0
    · -- `ℓ_t = 1`, `1 - t ≥ g²`
      have hℓ : ellT L g t = 1 := B45_ellT_eq_one ht1 hL1 hx1
      rw [hℓ, one_pow, inv_one, one_pow, mul_one]
      -- `x_t ≤ 1` means `g² ≤ 1 - t`
      have hg2 : g ^ 2 ≤ 1 - t := by
        rw [div_le_one hsq] at hx1
        have := pow_le_pow_left₀ hg.le hx1 2
        rwa [Real.sq_sqrt hv.le] at this
      set T : ℝ := 1 - g ^ 2 with hT
      have hT1 : T < 1 := by rw [hT]; have : 0 < g ^ 2 := by positivity
                             linarith
      have htT : t ≤ T := by rw [hT]; linarith
      have hT0 : 0 ≤ T := ht0.trans htT
      have hvT : 0 < 1 - T := by linarith
      have h1T : 1 - T = g ^ 2 := by rw [hT]; ring
      have hxT : g / Real.sqrt (1 - T) = 1 := by
        rw [h1T, Real.sqrt_sq hg.le]; exact div_self hg.ne'
      have hmidT := B45_vth_mid hL hg h hdm hT0 hT1 hxT.ge (by rw [hxT]; exact hLr) a
      have hℓT : ellT L g T = 1 := B45_ellT_eq_one hT1 hL1 hxT.le
      rw [hℓT, one_pow, inv_one, one_pow, mul_one] at hmidT
      have hcont : ContinuousOn (fun τ => ϑ τ a) (Set.Icc t T) :=
        ((h.2.2.1 a).continuousOn).mono (fun τ hτ => ⟨ht0.trans hτ.1, lt_of_le_of_lt hτ.2 hT1⟩)
      have hdiff : ∀ τ ∈ Set.Ioc t T, DifferentiableAt ℝ (fun τ => ϑ τ a) τ := by
        intro τ hτ
        exact (h.2.2.1 a).differentiableAt (Ico_mem_nhds (by linarith [hτ.1]) (by linarith [hτ.2]))
      have hΦ : ∀ τ ∈ Set.Icc t T, HasDerivAt (fun τ => -(C * Real.log (1 - τ)))
          (C * (1 - τ)⁻¹) τ := by
        intro τ hτ
        have hτ1 : 1 - τ ≠ 0 := by linarith [hτ.2]
        have h1 : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) τ := by
          simpa using (hasDerivAt_id τ).const_sub 1
        have h2 := (h1.log hτ1).const_mul C |>.neg
        refine h2.congr_deriv ?_
        field_simp
      have hbound : ∀ τ ∈ Set.Ioc t T, ‖deriv (fun τ => ϑ τ a) τ‖ ≤ C * (1 - τ)⁻¹ := by
        intro τ hτ
        have hτ0 : 0 ≤ τ := by linarith [hτ.1]
        have hτ1 : τ < 1 := by linarith [hτ.2]
        have h4 := h.2.2.2 τ hτ0 hτ1 a
        have hℓτ : 1 ≤ ellT L g τ := one_le_ellT hLr
        have hQτ : (((ellT L g τ) ^ d)⁻¹) ^ m ≤ 1 := by
          have h1 : 1 ≤ (ellT L g τ) ^ d := one_le_pow₀ hℓτ
          exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
        refine h4.trans ?_
        have : 0 ≤ C * (1 - τ)⁻¹ := by
          have : 0 < 1 - τ := by linarith
          positivity
        calc C * (1 - τ)⁻¹ * (((ellT L g τ) ^ d)⁻¹) ^ m ≤ C * (1 - τ)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left hQτ this
          _ = C * (1 - τ)⁻¹ := mul_one _
      have hcmp := B45_cmp htT hcont hdiff hΦ hbound hmidT
      refine hcmp.trans ?_
      -- `Φ(T) - Φ(t) = C log((1-t)/g²) ≤ -2 C log g`
      have hlogt : Real.log (1 - t) ≤ 0 := Real.log_nonpos hv.le (by linarith)
      have hlogT : Real.log (1 - T) = 2 * Real.log g := by
        rw [h1T, Real.log_pow]; push_cast; ring
      have e1 : -(C * Real.log (1 - T)) - -(C * Real.log (1 - t)) =
          C * (Real.log (1 - t) - 2 * Real.log g) := by rw [hlogT]; ring
      have hmax : -Real.log g ≤ max 0 (-Real.log g) := le_max_right _ _
      calc _ ≤ C * (Kc + 2 / ((d * m : ℕ) : ℝ)) + C * (Real.log (1 - t) - 2 * Real.log g) := by
            have : (C * Kc + 2 * C / ((d * m : ℕ) : ℝ)) = C * (Kc + 2 / ((d * m : ℕ) : ℝ)) := by ring
            rw [this]
            simp only [e1]; exact le_rfl
        _ ≤ C * (Kc + 2 / ((d * m : ℕ) : ℝ) + 2 * max 0 (-Real.log g)) := by
            have : C * (Real.log (1 - t) - 2 * Real.log g) ≤ C * (2 * max 0 (-Real.log g)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC
            nlinarith

end VthSup

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

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Det45

variable {d : ℕ}

/-- **The deterministic core of `(eq:Ward_typeP)` and `(y27kasdfg)`** at one `(n, u, ω)`: from the bound
`Ξ̂ ≤ ν X` on the rank-`m+1` entries (`hY`), the far-entry bound `F` (`hF`) and the mollifier bounds
(`hϑ`, `hϑ'`), for alternating `σ` (`σ_last = ¬σ_0`), tensors of `m+2` indices:
`|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ M (W^{-d}B_{u,0})^{m+2} X` and `|ℬ₄| + |ℬ₅| ≤ η⁻¹ (2m+5) M (W^{-d}B_{u,0})^{m+2} X`,
`M = 3·4^{dm} Γ Λ ν²`, `Γ = 2/√κ`.  The `ℓ`-power left over at `d ≥ 3` is absorbed by `B45_scales`. -/
theorem B45_det (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) (ω : sz.SeqΩ)
    {m : ℕ} {Γ ν X ωf Fv Λ : ℝ} (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKtensor sz n E u ω σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖STLKtensor sz n E u ω σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 2) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a, ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (hϑ' : ∀ a, ‖deriv (fun τ => ϑ τ a) u‖ ≤
      Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a : Fin (m + 2) → Zd d (sz.L n)) :
    ‖STPsum (d := d) (STLKtensor sz n E u ω σ) (a 0) * ϑ u a‖ ≤
        (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) ∧
      ‖(STQop (d := d) ϑ u (ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE E) σ) u
              (STLKtensor sz n E u ω σ)) -
            ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE E) σ) u
              (STQop (d := d) ϑ u (STLKtensor sz n E u ω σ))) a‖ +
          ‖STPsum (d := d) (STLKtensor sz n E u ω σ) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
        (etaT E u)⁻¹ * (((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) *
          (sz.Bctl n u ^ (m + 2) * X)) := by
  have hL3 := sz.three_le_L n
  obtain ⟨hKB, hηN, hBN, hη, hηle⟩ := B45_scales hd sz n hκ hE hu0 hu1 hg hNu hΓ
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓ]; have := Real.sqrt_pos.mpr hκ; positivity
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
  have hLd1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by rw [hNe]; positivity
  have hB0 : 0 < sz.Bctl n u := lt_of_lt_of_le (inv_pos.2 hNpos) hBN
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) u := one_le_ellT hL1
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) u := by linarith
  -- the `𝒫`-bound, for every `a₁`
  set R : ℝ := ellT (sz.L n) (sz.lam n) u * ωf with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set Pi : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ *
    (((2 * R + 2) ^ d) ^ m * (ν * X * sz.Bctl n u ^ (m + 1)) +
      (((sz.L n : ℕ) : ℝ) ^ d) ^ m * Fv) with hPi
  have hP : ∀ b₁ : Zd d (sz.L n), ‖STPsum (d := d) (STLKtensor sz n E u ω σ) b₁‖ ≤ Pi := fun b₁ =>
    B45_Psum_LK_le sz n (E := E) (by linarith [abs_nonneg E]) hu0 hu1 ω σ hσ b₁ hR0 hFv0 hY
      (fun σ' a' _ hfar => hF σ' a' hfar)
  have hPi0 : 0 ≤ Pi := (norm_nonneg _).trans (hP (a 0))
  set vs : ℝ := Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) with hvs
  have hvs0 : 0 ≤ vs := by rw [hvs]; positivity
  -- the exponent count
  have hM : Pi * vs ≤ (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) :=
    B45_master_real (d := d) (m := m) (Wd := ((sz.W n : ℕ) : ℝ) ^ d) (Ld := ((sz.L n : ℕ) : ℝ) ^ d)
      (N := ((sz.size n : ℕ) : ℝ)) (η := etaT E u) (B := sz.Bctl n u)
      (ℓ := ellT (sz.L n) (sz.lam n) u) (X := X) (ν := ν) (ω := ωf) (Γ := Γ) (Λ := Λ) (ϑb := vs)
      (Pi := Pi) (Fv := Fv) (by linarith) hLd1 hNe hℓ1 hν hX hB0 hη hωf hωd hΓ0 hΛ hWd1 hKB hηN hBN
      hFv hFv0 hνN hPi0 hvs0 (by rw [hPi]) (le_of_eq hvs)
  have hZ : 0 ≤ (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) := by
    have : 0 ≤ X := by linarith
    positivity
  have hv1 : 0 < 1 - u := by linarith
  -- (1)
  have h1 : ‖STPsum (d := d) (STLKtensor sz n E u ω σ) (a 0) * ϑ u a‖ ≤ Pi * vs := by
    rw [norm_mul]
    exact mul_le_mul (hP (a 0)) (hϑ a) (norm_nonneg _) hPi0
  refine ⟨h1.trans hM, ?_⟩
  -- (2) `ℬ₄`
  have hμ : ∀ i, ‖EKsgn (mE E) σ i‖ = 1 := fun i => B45_norm_EKsgn (by linarith [abs_nonneg E]) σ i
  have hB4 := B45_B4_le (d := d) (L := sz.L n) (m := m + 1) (sz.lam n) hL3 hμ hu0 hu1 ϑ
    (STLKtensor sz n E u ω σ) hP hϑ a
  -- `ℬ₅`
  have hB5 : ‖STPsum (d := d) (STLKtensor sz n E u ω σ) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
      (1 - u)⁻¹ * (Pi * vs) := by
    rw [norm_mul]
    calc ‖STPsum (d := d) (STLKtensor sz n E u ω σ) (a 0)‖ * ‖deriv (fun τ => ϑ τ a) u‖
        ≤ Pi * (Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1))) :=
          mul_le_mul (hP (a 0)) (hϑ' a) (norm_nonneg _) hPi0
      _ = (1 - u)⁻¹ * (Pi * vs) := by rw [hvs]; ring
  have hinv : (1 - u)⁻¹ ≤ (etaT E u)⁻¹ := inv_anti₀ hη hηle
  have hMZ := hM
  have hPV0 : 0 ≤ Pi * vs := mul_nonneg hPi0 hvs0
  set M' := (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) with hM'
  have hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hB4
  have hi0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hv1.le
  calc _ ≤ 2 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (Pi * vs) + (1 - u)⁻¹ * (Pi * vs) := add_le_add hB4 hB5
    _ = (1 - u)⁻¹ * ((2 * (m : ℝ) + 5) * (Pi * vs)) := by ring
    _ ≤ (etaT E u)⁻¹ * ((2 * (m : ℝ) + 5) * M') := by
        have h2 : (2 * (m : ℝ) + 5) * (Pi * vs) ≤ (2 * (m : ℝ) + 5) * M' :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        have h3 : 0 ≤ (2 * (m : ℝ) + 5) * (Pi * vs) := by positivity
        exact mul_le_mul hinv h2 h3 (inv_nonneg.2 hη.le)
    _ = _ := by rw [hM']; ring

end Det45

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Assemble

variable {d : ℕ}

/-- **The union bound of the assembly**: if `ξ₁ ≺ ζ₁` and the far family `ξ₂ ≺ W^{-D'}` (for every
`τ_f, D'`) and, for every `τ > 0`, there are `τ₁, τ_f, D'` such that eventually the deterministic
implication "`ξ₁ ≤ N^{τ₁} ζ₁` and `ξ₂ ≤ N^{τ₁} W^{-D'}` everywhere ⟹ `ξ₃ ≤ N^τ ζ₃` everywhere" holds,
then `ξ₃ ≺ ζ₃` (the proof of `StochDomAt.of_subset_union` with the second source chosen after `τ`). -/
theorem B45_prec_assemble (sz : Sizes d) (hN : sz.SizeTendsto)
    {U₁ U₂ U₃ : ℕ → Type*} {ξ₁ ζ₁ : ∀ n, U₁ n → sz.SeqΩ → ℝ}
    {ξ₂ : ℝ → ∀ n, U₂ n → sz.SeqΩ → ℝ} {ξ₃ ζ₃ : ∀ n, U₃ n → sz.SeqΩ → ℝ}
    (h₁ : sz.Prec ξ₁ ζ₁)
    (h₂ : ∀ τf > (0 : ℝ), ∀ D' > (0 : ℝ),
      sz.Prec (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')))
    (hdet : ∀ τ > (0 : ℝ), ∃ τ₁ > (0 : ℝ), ∃ τf > (0 : ℝ), ∃ D' > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, ∀ ω : sz.SeqΩ,
        (∀ p, ξ₁ n p ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * ζ₁ n p ω) →
        (∀ q, ξ₂ τf n q ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-D')) →
        ∀ r, ξ₃ n r ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₃ n r ω) :
    sz.Prec ξ₃ ζ₃ := by
  intro τ hτ D hD
  obtain ⟨τ₁, hτ₁, τf, hτf, D', hD', hev⟩ := hdet τ hτ
  filter_upwards [hev, h₁ τ₁ hτ₁ (D + 1) (by linarith), h₂ τf hτf D' hD' τ₁ hτ₁ (D + 1) (by linarith),
    (Sizes.tendsto_size sz hN).eventually (eventually_two_mul_rpow_le D)] with n hev1 h1 h2 h3
  have hp : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : badSetAt sz.size ξ₃ ζ₃ τ n ⊆
      badSetAt sz.size ξ₁ ζ₁ τ₁ n ∪ badSetAt sz.size (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) τ₁ n := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno hω
    obtain ⟨r, hr⟩ := hω
    exact absurd (hev1 ω hno.1 hno.2 r) (not_le.2 hr)
  calc (seqP sz) (badSetAt sz.size ξ₃ ζ₃ τ n)
      ≤ (seqP sz) (badSetAt sz.size ξ₁ ζ₁ τ₁ n ∪
          badSetAt sz.size (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) τ₁ n) := measure_mono hsub
    _ ≤ (seqP sz) (badSetAt sz.size ξ₁ ζ₁ τ₁ n) +
          (seqP sz) (badSetAt sz.size (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) τ₁ n) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

end Assemble

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Aux45

variable {d : ℕ}

/-- `Ξ̂^{𝓛-𝒦}_{u,k} ≤ Y` bounds every entry: `|(𝓛-𝒦)^{(k)}_{σ,a}| ≤ Y (W^{-d}B_{u,0})^k`. -/
theorem B45_norm_le_XiLK (sz : Sizes d) (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) {k : ℕ}
    (hB : 0 < sz.Bctl n u) {Y : ℝ} (h : STXiLK sz n E u k ω ≤ Y) (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤ Y * sz.Bctl n u ^ k := by
  have hBk : 0 < sz.Bctl n u ^ k := pow_pos hB k
  unfold STXiLK STmaxLK at h
  have h1 : ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤
      Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
        (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
          ‖Lloop sz n E u p.1 p.2 ω - STKloop sz n E u p.1 p.2‖) :=
    Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E u p.1 p.2 ω - STKloop sz n E u p.1 p.2‖) (Finset.mem_univ (σ, a))
  set S := Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
        (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
          ‖Lloop sz n E u p.1 p.2 ω - STKloop sz n E u p.1 p.2‖) with hS
  have h2 : S / sz.Bctl n u ^ k ≤ Y - 1 := by linarith
  have h3 : S ≤ (Y - 1) * sz.Bctl n u ^ k := by
    rw [div_le_iff₀ hBk] at h2; exact h2
  have h4 : (Y - 1) * sz.Bctl n u ^ k ≤ Y * sz.Bctl n u ^ k := by nlinarith
  exact (h1.trans h3).trans h4

/-- Alternating `σ` on `Fin (m+2)` has `σ_last = ¬σ_0`. -/
theorem B45_alt_last {m : ℕ} {σ : Fin (m + 2) → Bool} (h : STAlternating σ) :
    σ (Fin.last (m + 1)) = !σ 0 := by
  have h1 := h (Fin.last (m + 1))
  rw [finRotate_last] at h1
  revert h1
  cases σ 0 <;> cases σ (Fin.last (m + 1)) <;> simp

/-- `W^{-D'} ≤ N^{-(k)}` for `D' = k/𝔠` when `N^𝔠 ≤ W`. -/
theorem B45_W_pow_neg_le {W N 𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hN : 1 ≤ N) (hW : N ^ 𝔠 ≤ W) (k : ℕ) :
    W ^ (-((k : ℝ) / 𝔠)) ≤ (N ^ k)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
  have hW0 : 0 < W := lt_of_lt_of_le hNc hW
  rw [Real.rpow_neg hW0.le]
  apply inv_anti₀ (by positivity)
  calc N ^ k = (N ^ 𝔠) ^ ((k : ℝ) / 𝔠) := by
        rw [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ h𝔠.ne', Real.rpow_natCast]
    _ ≤ W ^ ((k : ℝ) / 𝔠) := Real.rpow_le_rpow hNc.le hW (by positivity)

/-- The window factor: `(W^{τ_f})^{dm} ≤ N^{τ₁}` for `τ_f m ≤ τ₁`, `W^d ≤ N`, `N ≥ 1`. -/
theorem B45_window_pow_le {W N : ℝ} (hW : 1 ≤ W) (hN : 1 ≤ N) (hWN : W ^ d ≤ N) {τf τ₁ : ℝ}
    (hτf : 0 ≤ τf) (m : ℕ) (hτ : τf * m ≤ τ₁) : (W ^ τf) ^ (d * m) ≤ N ^ τ₁ := by
  have hW0 : 0 < W := by linarith
  have e1 : (W ^ τf) ^ (d * m) = W ^ (τf * ((d * m : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have e2 : (W ^ (d : ℝ)) ^ (τf * m) = W ^ ((d : ℝ) * (τf * m)) := by
    rw [← Real.rpow_mul hW0.le]
  calc (W ^ τf) ^ (d * m) = W ^ (τf * ((d * m : ℕ) : ℝ)) := e1
    _ = W ^ ((d : ℝ) * (τf * m)) := by congr 1; push_cast; ring
    _ = (W ^ (d : ℝ)) ^ (τf * m) := e2.symm
    _ ≤ N ^ (τf * m) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        rwa [Real.rpow_natCast]
    _ ≤ N ^ τ₁ := Real.rpow_le_rpow_of_exponent_le hN hτ

end Aux45

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Det45b

variable {d : ℕ}

/-- `B45_det` with the constants absorbed: if `(2m+5)·M ≤ N^τ` then
`|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ N^τ (W^{-d}B_{u,0})^{m+2} X` and
`|ℬ₄| + |ℬ₅| ≤ N^τ η⁻¹ (W^{-d}B_{u,0})^{m+2} X`. -/
theorem B45_det2 (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) (ω : sz.SeqΩ)
    {m : ℕ} {Γ ν X ωf Fv Λ τ : ℝ} (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKtensor sz n E u ω σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖STLKtensor sz n E u ω σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 2) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a, ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (hϑ' : ∀ a, ‖deriv (fun τ => ϑ τ a) u‖ ≤
      Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a : Fin (m + 2) → Zd d (sz.L n)) :
    ‖STPsum (d := d) (STLKtensor sz n E u ω σ) (a 0) * ϑ u a‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X) ∧
      ‖(STQop (d := d) ϑ u (ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE E) σ) u
              (STLKtensor sz n E u ω σ)) -
            ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE E) σ) u
              (STQop (d := d) ϑ u (STLKtensor sz n E u ω σ))) a‖ +
          ‖STPsum (d := d) (STLKtensor sz n E u ω σ) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X) := by
  obtain ⟨h1, h2⟩ := B45_det hd sz n hκ hE hu0 hu1 hg hNu ω hΓ hν hX hωf hωd hνN hFv hFv0 hΛ hY hF ϑ
    hϑ hϑ' σ hσ a
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    rw [hNe]; have := one_le_pow₀ (n := d) hL1; positivity
  have hBN : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.Bctl n u :=
    (B45_scales hd sz n hκ hE hu0 hu1 hg hNu hΓ).2.2.1
  have hB0 : 0 < sz.Bctl n u := lt_of_lt_of_le (inv_pos.2 hNpos) hBN
  have hη : 0 < etaT E u := (B45_scales hd sz n hκ hE hu0 hu1 hg hNu hΓ).2.2.2.1
  have hZ : 0 ≤ sz.Bctl n u ^ (m + 2) * X := by
    have : 0 ≤ X := by linarith
    positivity
  have hM1 : 3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2 ≤ (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) := by
    have hΓ0 : 0 ≤ Γ := by rw [hΓ]; have := Real.sqrt_pos.mpr hκ; positivity
    have h0 : 0 ≤ 3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2 := by positivity
    have : (1 : ℝ) ≤ 2 * (m : ℝ) + 5 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
    nlinarith
  constructor
  · refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (hM1.trans hMΛ) hZ
  · refine h2.trans ?_
    have h3 : ((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) * (sz.Bctl n u ^ (m + 2) * X) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X) :=
      mul_le_mul_of_nonneg_right hMΛ hZ
    calc (etaT E u)⁻¹ * (((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) *
          (sz.Bctl n u ^ (m + 2) * X))
        ≤ (etaT E u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X)) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hη.le)
      _ = _ := by ring

end Det45b

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Log45

/-- `2 max(0, -log g) ≤ N^{τ₁}/τ₁` when `g² ≥ N⁻¹` (the `log(1/g²) ≤ log N` loss of the
mollifier bound for `c < 0`, absorbed by `N^{τ₁}`). -/
theorem B45_log_le {g N τ₁ : ℝ} (hg : 0 < g) (hN : 1 ≤ N) (hgN : N⁻¹ ≤ g ^ 2) (hτ₁ : 0 < τ₁) :
    2 * max 0 (-Real.log g) ≤ N ^ τ₁ / τ₁ := by
  have hN0 : 0 < N := by linarith
  have h1 : Real.log (N⁻¹) ≤ Real.log (g ^ 2) := Real.log_le_log (by positivity) hgN
  rw [Real.log_inv, Real.log_pow] at h1
  push_cast at h1
  have h2 : -Real.log g ≤ Real.log N / 2 := by linarith
  have h3 : Real.log N ≤ N ^ τ₁ / τ₁ := Real.log_le_rpow_div hN0.le hτ₁
  have h4 : 0 ≤ Real.log N := Real.log_nonneg hN
  have h5 : 2 * max 0 (-Real.log g) ≤ Real.log N := by
    rcases le_total 0 (-Real.log g) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  linarith

end Log45

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Pins45

variable {d : ℕ}

/-- The far-entry observable `(|𝓛| + |𝓛-𝒦|)^{(k)}_{u,σ,a} · 1(ℓ_u W^{τ_f} ≤ diam_∞ a)` of `B45_far`. -/
def B45_farXi (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (k : ℕ) (τf : ℝ) (n : ℕ)
    (p : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (ω : sz.SeqΩ) : ℝ :=
  (‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
      ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) *
    (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τf ≤ (STdiamInf p.2.2 : ℝ)
      then 1 else 0)

set_option maxHeartbeats 400000 in
-- the pointwise chain of the far/near split elaborates a long `have` list: 200000 is not enough
/-- The deterministic-eventual core of `B45_pins`. -/
theorem B45_key (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n))
    {m : ℕ} (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n))
    (X : ℕ → ℝ → ℝ) (hX1 : ∀ n u, 1 ≤ X n u)
    (hXprec : Prec sz (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiLK sz n (STflowE z n) (u : ℝ) (m + 1) ω) (fun n u _ => X n (u : ℝ))) :
    ∀ τ > (0 : ℝ), ∃ τ₁ > (0 : ℝ), ∃ τf > (0 : ℝ), ∃ D' > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, ∀ ω : sz.SeqΩ,
        (∀ u : TimeIcc s t n, STXiLK sz n (STflowE z n) (u : ℝ) (m + 1) ω ≤
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * X n (u : ℝ)) →
        (∀ q : TimeIcc s t n × (Fin (m + 1) → Bool) × (Fin (m + 1) → Zd d (sz.L n)),
          B45_farXi sz (STflowE z) s t (m + 1) τf n q ω ≤
            ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-D')) →
        ∀ (u : TimeIcc s t n) (σ : Fin (m + 1 + 1) → Bool), STAlternating σ →
          ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
          ‖STPsum (d := d) (STLKtensor sz n (STflowE z n) (u : ℝ) ω σ) (a 0) * ϑ n (u : ℝ) a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (u : ℝ)) ^ (m + 1 + 1) * X n (u : ℝ)) ∧
          ‖(STQop (d := d) (ϑ n) (u : ℝ)
              (ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ) (u : ℝ)
                (STLKtensor sz n (STflowE z n) (u : ℝ) ω σ)) -
            ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) σ) (u : ℝ)
              (STQop (d := d) (ϑ n) (u : ℝ) (STLKtensor sz n (STflowE z n) (u : ℝ) ω σ))) a‖ +
          ‖STPsum (d := d) (STLKtensor sz n (STflowE z n) (u : ℝ) ω σ) (a 0) *
              deriv (fun τ => ϑ n τ a) (u : ℝ)‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (u : ℝ))⁻¹ *
                (sz.Bctl n (u : ℝ)) ^ (m + 1 + 1) * X n (u : ℝ)) := by
  have hA := hflow.1
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  obtain ⟨-, -, -, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hdm : 1 ≤ d * (m + 1) := Nat.mul_pos (by omega) (by omega)
  intro τ hτ
  obtain ⟨τ₁, hτ₁def⟩ : ∃ τ₁ : ℝ, τ₁ = min (τ / 6) (1 / 4) := ⟨_, rfl⟩
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; exact lt_min (by linarith) (by norm_num)
  have hτ₁4 : τ₁ ≤ 1 / 4 := by rw [hτ₁def]; exact min_le_right _ _
  have hτ₁6 : τ₁ ≤ τ / 6 := by rw [hτ₁def]; exact min_le_left _ _
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine ⟨τ₁, hτ₁, τ₁ / ((m : ℝ) + 1), by positivity, ((2 * m + 4 : ℕ) : ℝ) / 𝔠, by positivity, ?_⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ, Γ = 2 / Real.sqrt κ := ⟨_, rfl⟩
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ, Kc = Real.exp (|c| * (((m + 1 : ℕ) : ℝ) * d / 2)) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = C * (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 1 / τ₁) := ⟨_, rfl⟩
  obtain ⟨K₃, hK₃def⟩ : ∃ K₃ : ℝ, K₃ = (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * K₂) := ⟨_, rfl⟩
  have hK3ev : ∀ᶠ n : ℕ in atTop, K₃ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hN).eventually_ge_atTop K₃
  filter_upwards [hrange, hB, hWO, hK3ev, hN.eventually_ge_atTop 1] with n hr hbw hwo hK3 hN1'
  intro ω hyp1 hyp2 u σ hσalt a
  -- basic facts at the index `n`
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWdN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hNe]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1r)
  have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans
      (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgN : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.size n : ℕ) : ℝ))⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_anti₀ hW0 hWdN
      _ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hC : 0 ≤ C := B45_C_nonneg hL3 hlam0 (hϑ n)
  have hu0 : 0 ≤ (u : ℝ) := (hs n).trans u.2.1
  have hut : (u : ℝ) ≤ t n := u.2.2
  have hu1 : (u : ℝ) < 1 := (hut.trans (ht n)).trans_lt (lemT_lt_one (him n))
  have hEn : |STflowE z n| ≤ 2 - κ := (abs_lemE_le (him n)).trans (hflow.2 n).1
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - (u : ℝ) := by
    calc (((sz.size n : ℕ) : ℝ))⁻¹ = ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) :=
          Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      _ ≤ 1 - t n := hr
      _ ≤ 1 - (u : ℝ) := by linarith
  have hsc := B45_scales (by omega : 2 ≤ d) sz n hκ hEn hu0 hu1 hlam0 hNu hΓdef
  have hB0 : 0 < sz.Bctl n (u : ℝ) := lt_of_lt_of_le (inv_pos.2 hN0) hsc.2.2.1
  -- the constants
  have hdm0 : (0 : ℝ) < ((d * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hdm
  have hKc0 : 0 < Kc := by rw [hKcdef]; exact Real.exp_pos _
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = C * (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) +
      2 * max 0 (-Real.log (sz.lam n))) := ⟨_, rfl⟩
  have hmax0 : 0 ≤ max 0 (-Real.log (sz.lam n)) := le_max_left _ _
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  have hlog := B45_log_le hlam0 hN1' hgN hτ₁
  have hNτ₁ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁.le
  have hΛle : Λ ≤ K₂ * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by
    rw [hΛdef, hK₂def]
    have h1 : Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 2 * max 0 (-Real.log (sz.lam n)) ≤
        (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 1 / τ₁) * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by
      have h2 : 0 ≤ Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) := by positivity
      have h3 : (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ)) ≤
          (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ τ₁ :=
        le_mul_of_one_le_right h2 hNτ₁
      have h4 : ((sz.size n : ℕ) : ℝ) ^ τ₁ / τ₁ = 1 / τ₁ * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by ring
      nlinarith
    calc C * (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 2 * max 0 (-Real.log (sz.lam n)))
        ≤ C * ((Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 1 / τ₁) * ((sz.size n : ℕ) : ℝ) ^ τ₁) :=
          mul_le_mul_of_nonneg_left h1 hC
      _ = _ := by ring
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂def]; positivity
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; have := Real.sqrt_pos.mpr hκ; positivity
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃def]; positivity
  -- `(2m+5)·M ≤ N^τ`
  have hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ := by
    have hν2 : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have h3 : ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) =
        ((sz.size n : ℕ) : ℝ) ^ (3 * τ₁) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h4 : ((sz.size n : ℕ) : ℝ) ^ (3 * τ₁) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have h5 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
        ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hν0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) := (Real.rpow_pos_of_pos hN0 _).le
    calc (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2)
        ≤ (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * (K₂ * ((sz.size n : ℕ) : ℝ) ^ τ₁) *
            (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2) := by
          gcongr
      _ = K₃ * (((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁)) := by
          rw [hK₃def, hν2]; ring
      _ = K₃ * ((sz.size n : ℕ) : ℝ) ^ (3 * τ₁) := by rw [h3]
      _ ≤ K₃ * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := mul_le_mul_of_nonneg_left h4 hK₃0
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
          mul_le_mul_of_nonneg_right hK3 (Real.rpow_pos_of_pos hN0 _).le
      _ = _ := h5
  have hσ := B45_alt_last hσalt
  have hτf0 : 0 < τ₁ / ((m : ℝ) + 1) := by positivity
  have hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKtensor sz n (STflowE z n) (u : ℝ) ω σ' a'‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * X n (u : ℝ) * sz.Bctl n (u : ℝ) ^ (m + 1) :=
    fun σ' a' => B45_norm_le_XiLK sz n (STflowE z n) (u : ℝ) ω hB0 (hyp1 u) σ' a'
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) (u : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (τ₁ / ((m : ℝ) + 1)) ≤
        (STdiamInf a' : ℝ) → ‖STLKtensor sz n (STflowE z n) (u : ℝ) ω σ' a'‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-(((2 * m + 4 : ℕ) : ℝ) / 𝔠)) := by
    intro σ' a' hfar'
    have h := hyp2 (u, σ', a')
    simp only [B45_farXi, hfar', ite_true, mul_one] at h
    exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) h
  have hKc1 : 1 ≤ Kc := by
    rw [hKcdef]; exact Real.one_le_exp (by positivity)
  have hϑ1 : ∀ a, ‖ϑ n (u : ℝ) a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) (u : ℝ) ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    have := B45_vth_sup hL3 hlam0 (hϑ n) hdm hu0 hu1 a
    rw [hΛdef, hKcdef]; exact this
  have hCΛ : C ≤ Λ := by
    rw [hΛdef]
    exact le_mul_of_one_le_right hC (by
      have : 0 ≤ 2 / ((d * (m + 1) : ℕ) : ℝ) := by positivity
      linarith)
  have hϑ2 : ∀ a, ‖deriv (fun τ => ϑ n τ a) (u : ℝ)‖ ≤
      Λ * (1 - (u : ℝ))⁻¹ * (((ellT (sz.L n) (sz.lam n) (u : ℝ) ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    refine ((hϑ n).2.2.2 (u : ℝ) hu0 hu1 a).trans ?_
    have hv : 0 < 1 - (u : ℝ) := by linarith
    have hQ0 : 0 ≤ (((ellT (sz.L n) (sz.lam n) (u : ℝ) ^ d)⁻¹) ^ (m + 1)) := by
      have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := (u : ℝ)) hL1r
      positivity
    gcongr
  exact B45_det2 (by omega : 2 ≤ d) sz n hκ hEn hu0 hu1 hlam0 hNu ω hΓdef hNτ₁ (hX1 n (u : ℝ))
    (Real.one_le_rpow hW1r hτf0.le)
    (B45_window_pow_le hW1r hN1' hWdN hτf0.le m (by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm1]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith))
    (by calc ((sz.size n : ℕ) : ℝ) ^ τ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
        _ = _ := Real.rpow_one _)
    (mul_le_mul_of_nonneg_left (B45_W_pow_neg_le h𝔠 hN1' hbw (2 * m + 4)) (by positivity))
    (by positivity) hΛ0 hMΛ hY hF (ϑ n) hϑ1 hϑ2 σ hσ a


/-- **`(eq:Ward_typeP)` and `(y27kasdfg)` for tensors of `m + 2` indices** (the pins' `m ≥ 1`, `m ↦ m+1`),
both conclusions from the same hypotheses.  Along the flow `STFlow`, `0 ≤ s < t ≤ lemT z`, from the uniform
decay input `STGdecayW` (the far entries, `B45_far`), the induction bound `Ξ̂ ≺ X` and the mollifier
`STMollifierProps` (any real constants `C, c`). -/
theorem B45_pins (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) {Cd : ℝ} (hStep2 : STStep2Concl sz (STflowE z) s t Cd)
    {m : ℕ} (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n))
    (X : ℕ → ℝ → ℝ) (hX1 : ∀ n u, 1 ≤ X n u)
    (hXprec : Prec sz (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiLK sz n (STflowE z n) (u : ℝ) (m + 1) ω) (fun n u _ => X n (u : ℝ))) :
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin (m + 1 + 1) → Bool // STAlternating σ} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)))
      (fun n q ω => ‖STPsum (d := d) (STLKtensor sz n (STflowE z n) (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (m + 1 + 1) * X n (q.1 : ℝ)) ∧
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin (m + 1 + 1) → Bool // STAlternating σ} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)))
      (fun n q ω =>
        ‖(STQop (d := d) (ϑ n) (q.1 : ℝ)
            (ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) q.2.1.1) (q.1 : ℝ)
              (STLKtensor sz n (STflowE z n) (q.1 : ℝ) ω q.2.1.1)) -
          ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (STflowE z n)) q.2.1.1) (q.1 : ℝ)
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (STLKtensor sz n (STflowE z n) (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ +
        ‖STPsum (d := d) (STLKtensor sz n (STflowE z n) (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) *
            deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (etaT (STflowE z n) (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ (m + 1 + 1) *
        X n (q.1 : ℝ)) := by
  have hA := hflow.1
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  have hs' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hfar : ∀ τf > (0 : ℝ), ∀ D' > (0 : ℝ),
      Prec sz (U := fun n => TimeIcc s t n × (Fin (m + 1) → Bool) × (Fin (m + 1) → Zd d (sz.L n)))
        (B45_farXi sz (STflowE z) s t (m + 1) τf)
        (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) :=
    fun τf hτf D' hD' => B45_far hd sz hκ hflow hs hs' ht hStep2 (k := m + 1) (by omega) hτf hD'
  obtain ⟨-, -, -, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hdm : 1 ≤ d * (m + 1) := Nat.mul_pos (by omega) (by omega)
  have key := B45_key hd sz hκ hε hflow hs hst ht C c ϑ hϑ X hX1 hXprec
  -- assemble the two `≺`
  refine ⟨?_, ?_⟩
  · refine B45_prec_assemble sz hN hXprec (ξ₂ := fun τf => B45_farXi sz (STflowE z) s t (m + 1) τf) hfar
      (fun τ hτ => ?_)
    obtain ⟨τ₁, hτ₁, τf, hτf, D', hD', hev⟩ := key τ hτ
    refine ⟨τ₁, hτ₁, τf, hτf, D', hD', ?_⟩
    filter_upwards [hev] with n hn ω h1 h2 r
    exact (hn ω h1 h2 r.1 r.2.1.1 r.2.1.2 r.2.2).1
  · refine B45_prec_assemble sz hN hXprec (ξ₂ := fun τf => B45_farXi sz (STflowE z) s t (m + 1) τf) hfar
      (fun τ hτ => ?_)
    obtain ⟨τ₁, hτ₁, τf, hτf, D', hD', hev⟩ := key τ hτ
    refine ⟨τ₁, hτ₁, τf, hτf, D', hD', ?_⟩
    filter_upwards [hev] with n hn ω h1 h2 r
    exact (hn ω h1 h2 r.1 r.2.1.1 r.2.1.2 r.2.2).2

end Pins45

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`(eq:Ward_typeP)`** (`3_5:1264`, `jywiiwsoks` `3_5:1271`): the pin `STWardTypePPin`, case (i). -/
theorem stWardTypePPin_holds (d : ℕ) : STWardTypePPin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht _hR _hKb _hKw _hLK _hcon hStep2 m C c hm ϑ hϑ X hX1 hXprec
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact (B45_pins hd sz hκ hε hflow hs0 hst ht hStep2 C c ϑ hϑ X hX1 hXprec).1

/-- **`(y27kasdfg)`** (`3_5:1692`): the pin `STB45Pin`, case (i). -/
theorem stB45Pin_holds (d : ℕ) : STB45Pin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht _hR _hKb _hKw _hLK _hcon hStep2 m C c hm ϑ hϑ X hX1 hXprec
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact (B45_pins hd sz hκ hε hflow hs0 hst ht hStep2 C c ϑ hϑ X hX1 hXprec).2

end RBM.Gauss.Sizes

/-! ## Compiled nonempty instances (`d = 3`)

Data: the merged size sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the flow
`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, `s ≡ 0`, `t ≡ 1/16` (case (i),
`lam²/L² ≤ 1/16`), the merged mollifier `QopAlgebra_mollifier` (`QopAlgebra_mollifier_props`), `X ≡ 1`, and
tensors of `m + 1 = 2` (`m = 1`) and `m + 1 = 4` (`m = 3`) indices.  The hypotheses of the pins that are the
outputs of other gates stay hypotheses of the examples (`STKbound`, `STKward`, `STLK`, `STStep2Concl`, and
the induction bound `Ξ̂ ≺ X`); every deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`,
case (i), `(con_st_ind)`, `1 ≤ X`, the properties of the mollifier) is discharged. -/

namespace RBM.Gauss.B45Inst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step34Inst

theorem B45_sz0_lam_pos (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

/-- Alternating sign vectors exist at `m + 1 = 2`: `(+,-)`. -/
example : Nonempty {σ : Fin (1 + 1) → Bool // STAlternating σ} :=
  ⟨⟨![true, false], fun i => by fin_cases i <;> decide⟩⟩

/-- Alternating sign vectors exist at `m + 1 = 4`: `(+,-,+,-)`. -/
example : Nonempty {σ : Fin (3 + 1) → Bool // STAlternating σ} :=
  ⟨⟨![true, false, true, false], fun i => by fin_cases i <;> decide⟩⟩

/-- **`stWardTypePPin_holds` applied at `m = 1`** (two indices) on `(sz0, z0, 0, 1/16)` with the merged mollifier. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKbound sz0 (STflowE z0) → STKward sz0 (STflowE z0) → STLK sz0 (STflowE z0) sInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n)
          (fun n u ω => STXiLK sz0 n (STflowE z0 n) (u : ℝ) 1 ω) (fun n _ _ => 1) →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin (1 + 1) → Bool // STAlternating σ} ×
            (Fin (1 + 1) → Zd 3 (sz0.L n)))
          (fun n q ω => ‖STPsum (d := 3) (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1)
              (q.2.2 0) * QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n) (q.1 : ℝ) q.2.2‖)
          (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (1 + 1) * 1)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_WardTypeP (stWardTypePPin_holds 3) Cd hCd
  refine ⟨𝔠d, h0, h1, fun hK hKw hLK h2 hX => ?_⟩
  exact H hK hKw hLK h2 1 _ _ le_rfl (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 1 (sz0.three_le_L n) (B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

/-- **`stWardTypePPin_holds` applied at `m = 3`** (four indices). -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKbound sz0 (STflowE z0) → STKward sz0 (STflowE z0) → STLK sz0 (STflowE z0) sInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n)
          (fun n u ω => STXiLK sz0 n (STflowE z0 n) (u : ℝ) 3 ω) (fun n _ _ => 1) →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin (3 + 1) → Bool // STAlternating σ} ×
            (Fin (3 + 1) → Zd 3 (sz0.L n)))
          (fun n q ω => ‖STPsum (d := 3) (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1)
              (q.2.2 0) * QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n) (q.1 : ℝ) q.2.2‖)
          (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (3 + 1) * 1)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_WardTypeP (stWardTypePPin_holds 3) Cd hCd
  refine ⟨𝔠d, h0, h1, fun hK hKw hLK h2 hX => ?_⟩
  exact H hK hKw hLK h2 3 _ _ (by norm_num) (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

/-- **`stB45Pin_holds` applied at `m = 1`** (two indices). -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKbound sz0 (STflowE z0) → STKward sz0 (STflowE z0) → STLK sz0 (STflowE z0) sInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n)
          (fun n u ω => STXiLK sz0 n (STflowE z0 n) (u : ℝ) 1 ω) (fun n _ _ => 1) →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin (1 + 1) → Bool // STAlternating σ} ×
            (Fin (1 + 1) → Zd 3 (sz0.L n)))
          (fun n q ω =>
            ‖(STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n)) (q.1 : ℝ)
                (ThetaN 3 (sz0.L n) (sz0.lam n) (EKsgn (mE (STflowE z0 n)) q.2.1.1) (q.1 : ℝ)
                  (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1)) -
              ThetaN 3 (sz0.L n) (sz0.lam n) (EKsgn (mE (STflowE z0 n)) q.2.1.1) (q.1 : ℝ)
                (STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n)) (q.1 : ℝ)
                  (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ +
            ‖STPsum (d := 3) (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) *
                deriv (fun τ => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n) τ q.2.2) (q.1 : ℝ)‖)
          (fun n q _ => (etaT (STflowE z0 n) (q.1 : ℝ))⁻¹ * (sz0.Bctl n (q.1 : ℝ)) ^ (1 + 1) * 1)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_B45 (stB45Pin_holds 3) Cd hCd
  refine ⟨𝔠d, h0, h1, fun hK hKw hLK h2 hX => ?_⟩
  exact H hK hKw hLK h2 1 _ _ le_rfl (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 1 (sz0.three_le_L n) (B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

/-- **`stB45Pin_holds` applied at `m = 3`** (four indices). -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKbound sz0 (STflowE z0) → STKward sz0 (STflowE z0) → STLK sz0 (STflowE z0) sInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n)
          (fun n u ω => STXiLK sz0 n (STflowE z0 n) (u : ℝ) 3 ω) (fun n _ _ => 1) →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin (3 + 1) → Bool // STAlternating σ} ×
            (Fin (3 + 1) → Zd 3 (sz0.L n)))
          (fun n q ω =>
            ‖(STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) (q.1 : ℝ)
                (ThetaN 3 (sz0.L n) (sz0.lam n) (EKsgn (mE (STflowE z0 n)) q.2.1.1) (q.1 : ℝ)
                  (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1)) -
              ThetaN 3 (sz0.L n) (sz0.lam n) (EKsgn (mE (STflowE z0 n)) q.2.1.1) (q.1 : ℝ)
                (STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) (q.1 : ℝ)
                  (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ +
            ‖STPsum (d := 3) (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) *
                deriv (fun τ => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n) τ q.2.2) (q.1 : ℝ)‖)
          (fun n q _ => (etaT (STflowE z0 n) (q.1 : ℝ))⁻¹ * (sz0.Bctl n (q.1 : ℝ)) ^ (3 + 1) * 1)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_B45 (stB45Pin_holds 3) Cd hCd
  refine ⟨𝔠d, h0, h1, fun hK hKw hLK h2 hX => ?_⟩
  exact H hK hKw hLK h2 3 _ _ (by norm_num) (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

end RBM.Gauss.B45Inst
