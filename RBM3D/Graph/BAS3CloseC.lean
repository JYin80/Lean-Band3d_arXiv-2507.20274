/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAS3CloseB
import RBM3D.BA.TwistFold2B
import RBM3D.Graph.BAExp14bB
import RBM3D.BA.GreenStab

/-!
# BA-L L4d2b (T2450), part C: the fold leaf class, the 14 reductions, the closure, the packed form

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:66-121`; design
`docs/claude-team/fable/2026-10-12-s3-fold-A.md` §1, §3, §4, §5.  Parts A and B are
`Graph/BAS3Close.lean` and `Graph/BAS3CloseB.lean`.

## Contents (namespace `RBM.Graph`; private prefix `BAS3Close_`)

1. Entries of the graph data at the slice of the carrier (`S`, `S⁺`, `M` in block form).
2. The core lemma `BAS3Close_CL`: the two `M`-ties are eliminated, the node average is `twLoop2X`.
3. The chains `S M⁺ S⁺`, `S⁺ M⁺ S`, `S M⁺ S`, `S Ǧ Ǧ S`, `S⁺ M⁺ S M⁺ S⁺` and their block forms.
4. The shape lemmas: the value of each of the 14 catalogue graphs as a sum over the four core
   vertices.
5. `BAFoldLeaf`, `baFoldLeaf_congr`, the kernels of the weight `ρ` and their uniform `ℓ¹` bounds.
6. The 14 reductions and `baS3Fold_holds`, `BAS3Xprec`, `baS3Xprec_holds`, `BAS3Close`,
   `baS3Close_holds`, `BAS3Expand'`, `baS3Expand'_holds`.
7. The compiled nonempty instances (namespace `BAS3CloseInst`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


open private BAS3Close_pk from RBM3D.Graph.BAS3Close
open private GreenSchur_zim_pos from RBM3D.BA.GreenSchur
open private BAS3Close_LeafC BAS3Close_CtxExD BAS3Close_Iso BAS3Close_iso_symm
  BAS3Close_iso_trans BAS3Close_iso_val BAS3Close_iso_leaf BAS3Close_leaf_pk BAS3Close_ctxEx_pk BAS3Close_iso_cand
  BAS3Close_inv_iso BAS3Close_inv_pk BAS3Close_iso_root BAS3Close_lp_of_leaf BAS3Close_expand_none BAS3Close_out_stuck
  BAS3Close_Inv BAS3Close_rel BAS3Close_val_rel from RBM3D.Graph.BAS3Close
open private BAS3Close_RootFacts BAS3Close_tests_M BAS3Close_tests_D BAS3Close_tests_1 BAS3Close_MCM BAS3Close_vs1
  BAS3Close_vs1_mem BAS3Close_vs1_len BAS3Close_leafM_sound BAS3Close_invC_of_facts BAS3Close_CatR0 BAS3Close_eI0_0
  BAS3Close_iso_pk_perm BAS3Close_keys_eq from RBM3D.Graph.BAS3CloseB
open private BAS3Close_cf0_0 BAS3Close_cf0_1 BAS3Close_cf0_2 BAS3Close_cf0_3 BAS3Close_cf0_4 BAS3Close_cf0_5 BAS3Close_cf0_6
  BAS3Close_cf1_0 BAS3Close_cf1_1 BAS3Close_cf1_2 BAS3Close_cf1_3 BAS3Close_cf1_4 BAS3Close_cf1_5 BAS3Close_cf1_6
  from RBM3D.Graph.BAS3CloseB

open MeasureTheory Filter

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. Entries of the graph data at the slice of the carrier -/

section Entries

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ}

private abbrev BAS3Close_D (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : BALData (Idx d (sz.L n) (sz.W n)) :=
  BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) (BAExp14a_slc sz n ω)

private theorem BAS3Close_D_S (ω : sz.SeqΩ) (u v : Idx d (sz.L n) (sz.W n)) :
    (BAS3Close_D sz z n t ω).S u v = (t:ℂ) * (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) *
      if (split d (sz.L n) (sz.W n) u).1 = (split d (sz.L n) (sz.W n) v).1 then 1 else 0) :=
  BAExp14a_S_apply t u v

private theorem BAS3Close_D_Sp {κ : ℝ} (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (u v : Idx d (sz.L n) (sz.W n)) :
    (BAS3Close_D sz z n t ω).Sp u v = (t:ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      BAExp14b_om sz z n t (split d (sz.L n) (sz.W n) u).1 (split d (sz.L n) (sz.W n) v).1) := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have h := BAExp14a_W_sub_one (W := sz.W n) (sz.three_le_L n) hr ht0 ht1
  have hW1 : BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) =
      1 + lwLift d (sz.L n) (sz.W n) (BAExp14b_om sz z n t - 1) := by
    rw [← h]; abel
  change (Matrix.of (BAlwS d (sz.L n) (sz.W n) t) * BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
    ((baFMz sz z).m n)) u v = _
  rw [hW1, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [BAExp14a_S_apply]
  simp only [lwLift, Matrix.of_apply, BAExp14a_S_apply]
  rw [BAExp14b_sum_idx]
  simp only [BAExp14b_split_pt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases huv : (split d (sz.L n) (sz.W n) u).1 = (split d (sz.L n) (sz.W n) v).1
  · simp only [huv, ite_true]; field_simp; ring
  · simp only [huv, ite_false]; field_simp; ring


private theorem BAS3Close_D_M (ω : sz.SeqΩ) (u v : Idx d (sz.L n) (sz.W n)) :
    (BAS3Close_D sz z n t ω).M u v = (baFMz sz z).M n u v := rfl

private theorem BAS3Close_om_eq {κ : ℝ} (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (c c'' : Zd d (sz.L n)) :
    (BAExp14b_om sz z n t - 1) c c'' = (t : ℂ) * ∑ c', BAExp14b_MB sz z n c' c * BAExp14b_MB sz z n c c' * BAExp14b_om sz z n t c' c'' := by
  have h := (BATheta_resolvent d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) hr t ht0 ht1 true true).1
  have h2 := congrFun (congrFun h c) c''
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, smul_eq_mul] at h2
  change (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) ((baFMz sz z).m n) t true true - 1) c c'' = _
  rw [Matrix.sub_apply, Matrix.one_apply]
  simp only [BAMss_pp_apply] at h2
  linear_combination h2

private theorem BAS3Close_sum_single {α : Type*} [Fintype α] (c : α) (f : α → ℂ) (hf : ∀ b, b ≠ c → f b = 0) :
    ∑ x, f x = f c := Finset.sum_eq_single_of_mem c (Finset.mem_univ c) (fun b _ hb => hf b hb)

private theorem BAS3Close_K1 {κ : ℝ} (hm : 0 < ((baFMz sz z).m n).im)
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (u u' : Idx d (sz.L n) (sz.W n)) :
    ∑ a, ∑ b, (BAS3Close_D sz z n t ω).S u a * ((BAS3Close_D sz z n t ω).M a b * (BAS3Close_D sz z n t ω).M b a) *
        (BAS3Close_D sz z n t ω).Sp b u' =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        (BAExp14b_om sz z n t - 1) (split d (sz.L n) (sz.W n) u).1 (split d (sz.L n) (sz.W n) u').1) := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  simp only [BAExp14b_sum_idx, BAS3Close_D_S, BAS3Close_D_M, BAS3Close_D_Sp hr ht0 ht1, BAExp14b_M_pt sz z n hm,
    BAExp14b_split_pt]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  rw [BAS3Close_sum_single ((split d (sz.L n) (sz.W n) u).1)]
  · simp only [ite_true]
    rw [BAS3Close_om_eq hr ht0 ht1]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    field_simp
  · intro b hb
    simp [Ne.symm hb]


end Entries

/-! ## 2. The core lemma -/

section Core

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ}

/-- tie elimination -/
private theorem BAS3Close_sum_M (hm : 0 < ((baFMz sz z).m n).im) (u0 : Idx d (sz.L n) (sz.W n))
    (G : Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ u1, (baFMz sz z).M n u0 u1 * G u1 =
      ∑ c2, BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u0).1 c2 * G (twShift n c2 u0) := by
  obtain ⟨c0, o0, rfl⟩ : ∃ (c : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)), u0 = BAExp14b_pt c o :=
    ⟨_, _, (BAExp14b_pt_split u0).symm⟩
  rw [BAExp14b_sum_idx]
  refine Finset.sum_congr rfl fun c2 _ => ?_
  simp only [BAExp14b_M_pt sz z n hm, BAExp14b_split_pt, BAExp14b_shift_pt, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

private theorem BAS3Close_tie2 (hm : 0 < ((baFMz sz z).m n).im) (u0 u2 : Idx d (sz.L n) (sz.W n))
    (H : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ u1, ∑ u3, (baFMz sz z).M n u0 u1 * (baFMz sz z).M n u2 u3 * H u1 u3 =
      ∑ c2, ∑ c4, BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u0).1 c2 *
        BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u2).1 c4 * H (twShift n c2 u0) (twShift n c4 u2) := by
  calc ∑ u1, ∑ u3, (baFMz sz z).M n u0 u1 * (baFMz sz z).M n u2 u3 * H u1 u3
      = ∑ u1, (baFMz sz z).M n u0 u1 * ∑ u3, (baFMz sz z).M n u2 u3 * H u1 u3 := by
        refine Finset.sum_congr rfl fun u1 _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u3 _ => by ring
    _ = ∑ c2, BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u0).1 c2 *
          ∑ u3, (baFMz sz z).M n u2 u3 * H (twShift n c2 u0) u3 :=
        BAS3Close_sum_M hm u0 (fun u1 => ∑ u3, (baFMz sz z).M n u2 u3 * H u1 u3)
    _ = _ := by
        refine Finset.sum_congr rfl fun c2 _ => ?_
        rw [BAS3Close_sum_M hm u2 (fun u3 => H (twShift n c2 u0) u3), Finset.mul_sum]
        exact Finset.sum_congr rfl fun c4 _ => by ring


private theorem BAS3Close_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ a, ∑ c, ∑ b, ∑ e, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ e, ∑ b, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, f a b c e := Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := Finset.sum_congr rfl fun c _ => Finset.sum_comm

private theorem BAS3Close_blk2 (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ u0, ∑ u2, F u0 u2 = ∑ c1, ∑ c3, ∑ w ∈ twBlk n c1, ∑ w' ∈ twBlk n c3, F w w' := by
  calc ∑ u0, ∑ u2, F u0 u2 = ∑ c1, ∑ w ∈ twBlk n c1, ∑ u2, F w u2 :=
        (TwistFold2_sum_blk n (fun u0 => ∑ u2, F u0 u2)).symm
    _ = ∑ c1, ∑ w ∈ twBlk n c1, ∑ c3, ∑ w' ∈ twBlk n c3, F w w' :=
        Finset.sum_congr rfl fun c1 _ => Finset.sum_congr rfl fun w _ => (TwistFold2_sum_blk n (F w)).symm
    _ = ∑ c1, ∑ c3, ∑ w ∈ twBlk n c1, ∑ w' ∈ twBlk n c3, F w w' :=
        Finset.sum_congr rfl fun c1 _ => Finset.sum_comm

private theorem BAS3Close_core (hm : 0 < ((baFMz sz z).m n).im) (GM : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (Zb Nb : Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (x y : Idx d (sz.L n) (sz.W n)) (Tl : ℂ) :
    ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * Tl * (baFMz sz z).M n u0 u1 * (baFMz sz z).M n u2 u3 *
        Nb (split d (sz.L n) (sz.W n) u1).1 (split d (sz.L n) (sz.W n) u3).1 *
        Zb (split d (sz.L n) (sz.W n) u0).1 (split d (sz.L n) (sz.W n) u2).1 =
      ∑ c2, ∑ c4, ∑ c1, ∑ c3, BAExp14b_MB sz z n c1 c2 * BAExp14b_MB sz z n c3 c4 * Zb c1 c3 * Nb c2 c4 * Tl *
        ∑ w ∈ twBlk n c1, ∑ w' ∈ twBlk n c3, GM x w * GM (twShift n c2 w) w' * GM (twShift n c4 w') y := by
  have hbs : ∀ (c : Zd d (sz.L n)) (u : Idx d (sz.L n) (sz.W n)), (split d (sz.L n) (sz.W n) (twShift n c u)).1 = c :=
    fun c u => by rw [TwistFold2_split_shift]
  calc _ = ∑ u0, ∑ u2, ∑ u1, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * Tl * (baFMz sz z).M n u0 u1 * (baFMz sz z).M n u2 u3 *
        Nb (split d (sz.L n) (sz.W n) u1).1 (split d (sz.L n) (sz.W n) u3).1 *
        Zb (split d (sz.L n) (sz.W n) u0).1 (split d (sz.L n) (sz.W n) u2).1 :=
        Finset.sum_congr rfl fun u0 _ => Finset.sum_comm
    _ = ∑ u0, ∑ u2, ∑ c2, ∑ c4, BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u0).1 c2 *
        BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u2).1 c4 *
        (GM x u0 * GM (twShift n c2 u0) u2 * GM (twShift n c4 u2) y * Tl *
          Zb (split d (sz.L n) (sz.W n) u0).1 (split d (sz.L n) (sz.W n) u2).1 * Nb c2 c4) := by
        refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u2 _ => ?_
        have := BAS3Close_tie2 hm u0 u2 (fun u1 u3 => GM x u0 * GM u1 u2 * GM u3 y * Tl *
          Zb (split d (sz.L n) (sz.W n) u0).1 (split d (sz.L n) (sz.W n) u2).1 *
          Nb (split d (sz.L n) (sz.W n) u1).1 (split d (sz.L n) (sz.W n) u3).1)
        simp only [hbs] at this
        refine Eq.trans (Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u3 _ => ?_) this
        ring
    _ = ∑ c2, ∑ c4, ∑ u0, ∑ u2, BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u0).1 c2 *
        BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u2).1 c4 *
        (GM x u0 * GM (twShift n c2 u0) u2 * GM (twShift n c4 u2) y * Tl *
          Zb (split d (sz.L n) (sz.W n) u0).1 (split d (sz.L n) (sz.W n) u2).1 * Nb c2 c4) :=
        BAS3Close_swap22 _
    _ = _ := by
        refine Finset.sum_congr rfl fun c2 _ => Finset.sum_congr rfl fun c4 _ => ?_
        rw [BAS3Close_blk2]
        refine Finset.sum_congr rfl fun c1 _ => Finset.sum_congr rfl fun c3 _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w' hw' => ?_
        have h1 := (TwistFold2_mem_blk n).1 hw
        have h3 := (TwistFold2_mem_blk n).1 hw'
        rw [h1, h3]
        ring


private theorem BAS3Close_perm4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ b, ∑ e, ∑ a, ∑ c, f a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ b, ∑ a, ∑ c, ∑ e, f a b c e := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ e, ∑ c, f a b c e :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ b, ∑ e, ∑ a, ∑ c, f a b c e := Finset.sum_congr rfl fun b _ => Finset.sum_comm

private theorem BAS3Close_hoist2 {α β ι : Type*} [Fintype ι] (A : Finset α) (B : Finset β) (f : α → β → ι → ℂ) :
    ∑ x ∈ A, ∑ y ∈ B, ∑ c, f x y c = ∑ c, ∑ x ∈ A, ∑ y ∈ B, f x y c := by
  calc ∑ x ∈ A, ∑ y ∈ B, ∑ c, f x y c = ∑ x ∈ A, ∑ c, ∑ y ∈ B, f x y c :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ c, ∑ x ∈ A, ∑ y ∈ B, f x y c := Finset.sum_comm


private theorem BAS3Close_hoist4 {α β ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄] (A : Finset α) (B : Finset β)
    (f : α → β → ι₁ → ι₂ → ι₃ → ι₄ → ℂ) :
    ∑ x ∈ A, ∑ y ∈ B, ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, f x y c₁ c₂ c₃ c₄ = ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ∑ x ∈ A, ∑ y ∈ B, f x y c₁ c₂ c₃ c₄ := by
  rw [BAS3Close_hoist2]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [BAS3Close_hoist2]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  rw [BAS3Close_hoist2]
  refine Finset.sum_congr rfl fun c₃ _ => ?_
  rw [BAS3Close_hoist2]

private theorem BAS3Close_yin {α β γ : Type*} (s₁ : Finset α) (s₂ : Finset β) (s₃ : Finset γ) (h : α → β → γ → ℂ) :
    ∑ w ∈ s₁, ∑ w' ∈ s₂, ∑ y ∈ s₃, h w w' y = ∑ y ∈ s₃, ∑ w ∈ s₁, ∑ w' ∈ s₂, h w w' y := by
  calc ∑ w ∈ s₁, ∑ w' ∈ s₂, ∑ y ∈ s₃, h w w' y = ∑ w ∈ s₁, ∑ y ∈ s₃, ∑ w' ∈ s₂, h w w' y :=
        Finset.sum_congr rfl fun w _ => Finset.sum_comm
    _ = ∑ y ∈ s₃, ∑ w ∈ s₁, ∑ w' ∈ s₂, h w w' y := Finset.sum_comm

private theorem BAS3Close_CL (hm : 0 < ((baFMz sz z).m n).im) (σ : Bool) (Zb Nb : Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (ω : sz.SeqΩ)
    (a b : Zd d (sz.L n)) :
    ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, ∑ u0, ∑ u1, ∑ u2, ∑ u3,
        (baFMz sz z).GM n t ω x u0 * (baFMz sz z).GM n t ω u1 u2 * (baFMz sz z).GM n t ω u3 y *
          twChg ((baFMz sz z).GM n t ω) σ y x * (baFMz sz z).M n u0 u1 * (baFMz sz z).M n u2 u3 *
        Nb (split d (sz.L n) (sz.W n) u1).1 (split d (sz.L n) (sz.W n) u3).1 *
        Zb (split d (sz.L n) (sz.W n) u0).1 (split d (sz.L n) (sz.W n) u2).1 =
      twLoop2X n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
        (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
          ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
        (fun c₁ c₂ c₃ c₄ => (((sz.W n : ℕ) : ℂ) ^ d) ^ 2 * BAExp14b_MB sz z n c₁ c₂ * BAExp14b_MB sz z n c₃ c₄ *
          Zb c₁ c₃ * Nb c₂ c₄) a := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  simp only [BAS3Close_core hm]
  rw [BAS3Close_hoist4]
  unfold twLoop2X
  conv_rhs => rw [BAS3Close_perm4]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₄ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₃ _ => ?_
  beta_reduce
  have R : ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, (baFMz sz z).GM n t ω x w *
        (baFMz sz z).GM n t ω (twShift n c₂ w) w' * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
          ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω (twShift n c₄ w') y * twChg ((baFMz sz z).GM n t ω) σ y x) =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        (baFMz sz z).GM n t ω x w * (baFMz sz z).GM n t ω (twShift n c₂ w) w' *
          ((baFMz sz z).GM n t ω (twShift n c₄ w') y * twChg ((baFMz sz z).GM n t ω) σ y x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.mul_sum]
    rw [BAS3Close_yin]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine Finset.sum_congr rfl fun w _ => ?_
    refine Finset.sum_congr rfl fun w' _ => ?_
    ring
  have L : ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, BAExp14b_MB sz z n c₁ c₂ * BAExp14b_MB sz z n c₃ c₄ * Zb c₁ c₃ * Nb c₂ c₄ *
        twChg ((baFMz sz z).GM n t ω) σ y x * ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
          (baFMz sz z).GM n t ω x w * (baFMz sz z).GM n t ω (twShift n c₂ w) w' *
            (baFMz sz z).GM n t ω (twShift n c₄ w') y =
      BAExp14b_MB sz z n c₁ c₂ * BAExp14b_MB sz z n c₃ c₄ * Zb c₁ c₃ * Nb c₂ c₄ *
        ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
          (baFMz sz z).GM n t ω x w * (baFMz sz z).GM n t ω (twShift n c₂ w) w' *
            ((baFMz sz z).GM n t ω (twShift n c₄ w') y * twChg ((baFMz sz z).GM n t ω) σ y x) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun w' _ => ?_
    ring
  rw [L, R]
  field_simp

end Core

/-! ## 3. The chains and their block forms -/

section Chains

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Chain `S M⁺ S⁺` from `u` to `u'`. -/
private def BAS3Close_cK1 (D : BALData ι) (u u' : ι) : ℂ :=
  ∑ a, ∑ b, D.S u a * (D.M a b * D.M b a) * D.Sp b u'

/-- Chain `S⁺ M⁺ S` (transposed). -/
private def BAS3Close_cK1T (D : BALData ι) (u u' : ι) : ℂ :=
  ∑ a, ∑ b, D.Sp a u * (D.M b a * D.M a b) * D.S b u'

/-- Chain `S M⁺ S`. -/
private def BAS3Close_cK2 (D : BALData ι) (u u' : ι) : ℂ :=
  ∑ a, ∑ b, D.S u a * (D.M a b * D.M b a) * D.S u' b

/-- Chain `S Ǧ Ǧ S` (the closed two-cycle). -/
private def BAS3Close_cK3 (D : BALData ι) (GM : ι → ι → ℂ) (u u' : ι) : ℂ :=
  ∑ a, ∑ b, D.S u a * (GM a b * GM b a) * D.S u' b

/-- Chain `S⁺ M⁺ S M⁺ S⁺`. -/
private def BAS3Close_cK11 (D : BALData ι) (u u' : ι) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ e, D.Sp a u * (D.M b a * D.M a b) * D.S b c * (D.M c e * D.M e c) * D.Sp e u'

end Chains

section ChainBlocks

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ}

private theorem BAS3Close_om_symm {κ : ℝ} (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (c c' : Zd d (sz.L n)) : BAExp14b_om sz z n t c c' = BAExp14b_om sz z n t c' c := by
  have h := BATheta_isSymm d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) hr t ht0 ht1 true true
  have := congrFun (congrFun h c') c
  rw [Matrix.transpose_apply] at this
  exact this

private theorem BAS3Close_om_eq2 {κ : ℝ} (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (c c'' : Zd d (sz.L n)) :
    (BAExp14b_om sz z n t - 1) c c'' = (t : ℂ) * ∑ c', BAExp14b_om sz z n t c c' * (BAExp14b_MB sz z n c'' c' * BAExp14b_MB sz z n c' c'') := by
  have h := (BATheta_resolvent d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) hr t ht0 ht1 true true).2
  have h2 := congrFun (congrFun h c) c''
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, smul_eq_mul] at h2
  change (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) ((baFMz sz z).m n) t true true - 1) c c'' = _
  rw [Matrix.sub_apply, Matrix.one_apply]
  simp only [BAMss_pp_apply] at h2
  linear_combination h2

private theorem BAS3Close_H {κ : ℝ} (hm : 0 < ((baFMz sz z).m n).im)
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (u : Idx d (sz.L n) (sz.W n)) (f : Zd d (sz.L n) → ℂ) :
    ∑ a, ∑ b, (BAS3Close_D sz z n t ω).Sp a u * ((BAS3Close_D sz z n t ω).M b a * (BAS3Close_D sz z n t ω).M a b) *
        f (split d (sz.L n) (sz.W n) b).1 =
      ∑ c, (BAExp14b_om sz z n t - 1) (split d (sz.L n) (sz.W n) u).1 c * f c := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  simp only [BAExp14b_sum_idx, BAS3Close_D_Sp hr ht0 ht1, BAS3Close_D_M, BAExp14b_M_pt sz z n hm, BAExp14b_split_pt]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  simp only [BAS3Close_om_eq2 hr ht0 ht1, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ca _ => Finset.sum_congr rfl fun cb _ => ?_
  rw [BAS3Close_om_symm hr ht0 ht1 ca]
  field_simp


private theorem BAS3Close_cK1_blk {κ : ℝ} (hm : 0 < ((baFMz sz z).m n).im)
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (u u' : Idx d (sz.L n) (sz.W n)) :
    BAS3Close_cK1 (BAS3Close_D sz z n t ω) u u' = (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      (BAExp14b_om sz z n t - 1) (split d (sz.L n) (sz.W n) u).1 (split d (sz.L n) (sz.W n) u').1) :=
  BAS3Close_K1 hm hr ht0 ht1 ω u u'

private theorem BAS3Close_cK1T_blk {κ : ℝ} (hm : 0 < ((baFMz sz z).m n).im)
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (u u' : Idx d (sz.L n) (sz.W n)) :
    BAS3Close_cK1T (BAS3Close_D sz z n t ω) u u' = (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      (BAExp14b_om sz z n t - 1) (split d (sz.L n) (sz.W n) u).1 (split d (sz.L n) (sz.W n) u').1) := by
  have hH := BAS3Close_H hm hr ht0 ht1 ω u
    (fun c => (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * if c = (split d (sz.L n) (sz.W n) u').1 then 1 else 0))
  unfold BAS3Close_cK1T
  calc _ = ∑ a, ∑ b, (BAS3Close_D sz z n t ω).Sp a u * ((BAS3Close_D sz z n t ω).M b a * (BAS3Close_D sz z n t ω).M a b) *
        ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * if (split d (sz.L n) (sz.W n) b).1 = (split d (sz.L n) (sz.W n) u').1 then 1 else 0)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [BAS3Close_D_S]
    _ = _ := hH
    _ = _ := by
        simp only [mul_ite, mul_zero, mul_one]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ite_true]
        ring

private theorem BAS3Close_cK11_blk {κ : ℝ} (hm : 0 < ((baFMz sz z).m n).im)
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : sz.SeqΩ) (u u' : Idx d (sz.L n) (sz.W n)) :
    BAS3Close_cK11 (BAS3Close_D sz z n t ω) u u' = (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      ∑ c, (BAExp14b_om sz z n t - 1) (split d (sz.L n) (sz.W n) u).1 c *
        (BAExp14b_om sz z n t - 1) c (split d (sz.L n) (sz.W n) u').1) := by
  have hH := BAS3Close_H hm hr ht0 ht1 ω u
    (fun c => (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BAExp14b_om sz z n t - 1) c (split d (sz.L n) (sz.W n) u').1))
  calc BAS3Close_cK11 (BAS3Close_D sz z n t ω) u u'
      = ∑ a, ∑ b, (BAS3Close_D sz z n t ω).Sp a u * ((BAS3Close_D sz z n t ω).M b a * (BAS3Close_D sz z n t ω).M a b) *
        BAS3Close_cK1 (BAS3Close_D sz z n t ω) b u' := by
        simp only [BAS3Close_cK11, BAS3Close_cK1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun e _ => ?_
        ring
    _ = ∑ a, ∑ b, (BAS3Close_D sz z n t ω).Sp a u * ((BAS3Close_D sz z n t ω).M b a * (BAS3Close_D sz z n t ω).M a b) *
        ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BAExp14b_om sz z n t - 1) (split d (sz.L n) (sz.W n) b).1
          (split d (sz.L n) (sz.W n) u').1)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [BAS3Close_cK1_blk hm hr ht0 ht1]
    _ = _ := hH
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring


private theorem BAS3Close_cK2_blk (hm : 0 < ((baFMz sz z).m n).im) (ω : sz.SeqΩ) (u u' : Idx d (sz.L n) (sz.W n)) :
    BAS3Close_cK2 (BAS3Close_D sz z n t ω) u u' = (t : ℂ) ^ 2 * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      (BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u).1 (split d (sz.L n) (sz.W n) u').1 *
        BAExp14b_MB sz z n (split d (sz.L n) (sz.W n) u').1 (split d (sz.L n) (sz.W n) u).1)) := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  unfold BAS3Close_cK2
  simp only [BAExp14b_sum_idx, BAS3Close_D_S, BAS3Close_D_M, BAExp14b_M_pt sz z n hm, BAExp14b_split_pt]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  field_simp


/-- `X` of the fold leaf: `W^{-d} Σ_{u∈[c]} Σ_{v∈[c']} Ǧ_{uv} Ǧ_{vu}`. -/
private theorem BAS3Close_blk_sum (u : Idx d (sz.L n) (sz.W n)) (f : Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ a, (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (if (split d (sz.L n) (sz.W n) u).1 = (split d (sz.L n) (sz.W n) a).1 then 1 else 0)) * f a =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a ∈ twBlk n (split d (sz.L n) (sz.W n) u).1, f a) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [twBlk, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : (split d (sz.L n) (sz.W n) u).1 = (split d (sz.L n) (sz.W n) a).1
  · simp [h, eq_comm]; ring
  · simp [h, eq_comm]

private theorem BAS3Close_cK3_blk (ω : sz.SeqΩ) (GM : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (u u' : Idx d (sz.L n) (sz.W n)) :
    BAS3Close_cK3 (BAS3Close_D sz z n t ω) GM u u' = (t : ℂ) ^ 2 * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a ∈ twBlk n (split d (sz.L n) (sz.W n) u).1,
        ∑ b ∈ twBlk n (split d (sz.L n) (sz.W n) u').1, GM a b * GM b a)) := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  unfold BAS3Close_cK3
  calc _ = ∑ a, ∑ b, (BAS3Close_D sz z n t ω).S u' b * ((BAS3Close_D sz z n t ω).S u a * (GM a b * GM b a)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a, (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ b ∈ twBlk n (split d (sz.L n) (sz.W n) u').1,
          (BAS3Close_D sz z n t ω).S u a * (GM a b * GM b a)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [BAS3Close_D_S]
        exact BAS3Close_blk_sum u' _
    _ = (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ b ∈ twBlk n (split d (sz.L n) (sz.W n) u').1, ∑ a,
          (BAS3Close_D sz z n t ω).S u a * (GM a b * GM b a)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    _ = (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ b ∈ twBlk n (split d (sz.L n) (sz.W n) u').1,
          (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a ∈ twBlk n (split d (sz.L n) (sz.W n) u).1, GM a b * GM b a)) := by
        congr 2
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [BAS3Close_D_S]
        exact BAS3Close_blk_sum u (fun a => GM a b * GM b a)
    _ = _ := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
        ring


end ChainBlocks

/-! ## 4. The shape lemmas -/

local macro "BAS3Close_peel" : tactic => `(tactic| repeat (refine Finset.sum_congr rfl fun _ _ => ?_))


section Shapes

variable {ι : Type} [Fintype ι] [DecidableEq ι]


private theorem BAS3Close_pk_val {I : Type} [Fintype I] [DecidableEq I] (Γ : BAGraph (Fin 2) I) (D : BALData ι)
    (ℓ : Fin 2 → ι) : (BAS3Close_pk Γ).val D ℓ = Γ.val D ℓ := by
  unfold BAPGraph.val
  split_ifs with h
  · congr 1; exact (Classical.choose_spec h).symm
  · exact absurd ⟨ℓ, rfl⟩ h

private theorem BAS3Close_shape00 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf0_0 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (D.S u1 u3) * (D.S u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf0_0]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape01 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf0_1 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK1 D u1 u3) * (D.S u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf0_1, BAS3Close_cK1]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape02 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf0_2 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (D.S u1 u3) * (BAS3Close_cK1 D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf0_2, BAS3Close_cK1]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape03 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf0_3 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK3 D GM u1 u3) * (D.S u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf0_3, BAS3Close_cK3]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape04 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf0_4 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK2 D u1 u3) * (D.S u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf0_4, BAS3Close_cK2]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape05 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf0_5 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK3 D GM u1 u3) * (BAS3Close_cK1 D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf0_5, BAS3Close_cK1, BAS3Close_cK3]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape06 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf0_6 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK2 D u1 u3) * (BAS3Close_cK1 D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf0_6, BAS3Close_cK1, BAS3Close_cK2]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape10 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf1_0 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (D.S u1 u3) * (BAS3Close_cK1T D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf1_0, BAS3Close_cK1T]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape11 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf1_1 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK1 D u1 u3) * (BAS3Close_cK1T D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf1_1, BAS3Close_cK1T, BAS3Close_cK1]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape12 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf1_2 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (D.S u1 u3) * (BAS3Close_cK11 D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf1_2, BAS3Close_cK11]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape13 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf1_3 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK3 D GM u1 u3) * (BAS3Close_cK1T D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf1_3, BAS3Close_cK1T, BAS3Close_cK3]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape14 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf1_4 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK2 D u1 u3) * (BAS3Close_cK1T D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf1_4, BAS3Close_cK1T, BAS3Close_cK2]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape15 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf1_5 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK3 D GM u1 u3) * (BAS3Close_cK11 D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf1_5, BAS3Close_cK11, BAS3Close_cK3]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring

private theorem BAS3Close_shape16 (s : Bool) (D : BALData ι) (GM : ι → ι → ℂ) (hG : ∀ a b, D.G a b - D.M a b = GM a b) (x y : ι) :
    (BAS3Close_cf1_6 s).val D ![x, y] = ∑ u0, ∑ u1, ∑ u2, ∑ u3, GM x u0 * GM u1 u2 * GM u3 y * twChg GM s y x *
      D.M u0 u1 * D.M u2 u3 * (BAS3Close_cK2 D u1 u3) * (BAS3Close_cK11 D u0 u2) := by
  unfold BAGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero, BAGraph.term, LGraph.term, BAS3Close_cf1_6, BAS3Close_cK11, BAS3Close_cK2]
  cases s <;>
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SEdge.val, WEdge.val, BAMEdge.val,
    Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hG,
    twChg, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  all_goals
    BAS3Close_peel
    ring


end Shapes

/-! ## 5. The fold leaf class, the kernels of `ρ` and their bounds -/

section Data

variable {d : ℕ}


/-- Data of the flow at `0 ≤ t ≤ T₀`. -/
private theorem BAS3Close_data {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) :
    t < 1 ∧ BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) ∧
      0 < ((baFMz sz z).m n).im := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z h n
  have hzi := GreenSchur_zim_pos sz h n
  have hmz : 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im := (BAm_self d (sz.L n) (sz.lam n) (z n) hzi).1
  exact ⟨lt_of_le_of_lt ht (BAt0_lt_one hzi hmz), hr, hr.1.1⟩


/-- The uniform `ℓ¹` facts used by the bounds of `ρ`. -/
private def BAS3Close_Fact (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ) : Prop :=
  (∀ a, ∑ b, ‖BAExp14b_MB sz z n a b‖ ≤ m) ∧ (∀ b, ∑ a, ‖BAExp14b_MB sz z n a b‖ ≤ m) ∧
    (∀ a, ∑ b, ‖(BAExp14b_om sz z n t - 1) a b‖ ≤ K) ∧ (∀ b, ∑ a, ‖(BAExp14b_om sz z n t - 1) a b‖ ≤ K)

private theorem BAS3Close_sub_one_row {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (S : ℝ)
    (h : ∀ a, ∑ b, ‖A a b‖ ≤ S) (a : ι) : ∑ b, ‖(A - 1) a b‖ ≤ S + 1 := by
  calc ∑ b, ‖(A - 1) a b‖ ≤ ∑ b, (‖A a b‖ + ‖(1 : Matrix ι ι ℂ) a b‖) :=
        Finset.sum_le_sum fun b _ => by rw [Matrix.sub_apply]; exact norm_sub_le _ _
    _ = ∑ b, ‖A a b‖ + ∑ b, ‖(1 : Matrix ι ι ℂ) a b‖ := Finset.sum_add_distrib
    _ ≤ S + 1 := by
        have h1 : ∑ b, ‖(1 : Matrix ι ι ℂ) a b‖ = 1 := by
          simp only [Matrix.one_apply]
          simp [apply_ite (fun z : ℂ => ‖z‖)]
        linarith [h a]

private theorem BAS3Close_sub_one_col {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (S : ℝ)
    (h : ∀ b, ∑ a, ‖A a b‖ ≤ S) (b : ι) : ∑ a, ‖(A - 1) a b‖ ≤ S + 1 := by
  calc ∑ a, ‖(A - 1) a b‖ ≤ ∑ a, (‖A a b‖ + ‖(1 : Matrix ι ι ℂ) a b‖) :=
        Finset.sum_le_sum fun a _ => by rw [Matrix.sub_apply]; exact norm_sub_le _ _
    _ = ∑ a, ‖A a b‖ + ∑ a, ‖(1 : Matrix ι ι ℂ) a b‖ := Finset.sum_add_distrib
    _ ≤ S + 1 := by
        have h1 : ∑ a, ‖(1 : Matrix ι ι ℂ) a b‖ = 1 := by
          simp only [Matrix.one_apply]
          simp [apply_ite (fun z : ℂ => ‖z‖)]
        linarith [h b]

private theorem BAS3Close_facts (hd : 3 ≤ d) (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (𝔠 : ℝ) (h𝔡 : 0 < 𝔡) (sz : Sizes d) (z : ℕ → ℂ)
    (hf : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∃ m K : ℝ, 1 ≤ m ∧ 1 ≤ K ∧ ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n → BAS3Close_Fact sz z n t m K := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.mpr h𝔡
  obtain ⟨S, hS0, hS⟩ := BAExp14a_theta_l1 (k := k) (by omega) hΛ hκ
  refine ⟨max 1 ((BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC (k + 2 - 2) (BAct_rate (k + 2) 𝔡⁻¹ κ)), max 1 (S + 1),
    le_max_left _ _, le_max_left _ _, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hf] with n hn t ht0 ht
  obtain ⟨hg0, hgΛ⟩ := hn
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hf n ht0 ht
  have hL := sz.three_le_L n
  have hNZ : NeZero (sz.L n) := ⟨by omega⟩
  have hrow : ∀ a, ∑ b, ‖BAExp14b_MB sz z n a b‖ ≤ max 1 ((BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC (k + 2 - 2) (BAct_rate (k + 2) 𝔡⁻¹ κ)) :=
    fun a => (baM_row_l1 (by omega) hL 𝔡⁻¹ _ κ _ _ hΛ hg0 hgΛ hκ hr a).trans (le_max_right _ _)
  have hcol : ∀ b, ∑ a, ‖BAExp14b_MB sz z n a b‖ ≤ max 1 ((BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC (k + 2 - 2) (BAct_rate (k + 2) 𝔡⁻¹ κ)) :=
    fun b => (baM_col_l1 (by omega) hL 𝔡⁻¹ _ κ _ _ hΛ hg0 hgΛ hκ hr b).trans (le_max_right _ _)
  have hθrow : ∀ x, ∑ b, ‖BAExp14b_om sz z n t x b‖ ≤ S := fun x => hS (sz.L n) hL _ hg0 hgΛ _ _ hr t ht0 ht1 x
  have hθcol : ∀ b, ∑ a, ‖BAExp14b_om sz z n t a b‖ ≤ S := fun b => BAExp14a_theta_col hr ht0 ht1 hθrow b
  refine ⟨hrow, hcol, fun a => ?_, fun b => ?_⟩
  · exact (BAS3Close_sub_one_row _ S hθrow a).trans (le_max_right _ _)
  · exact (BAS3Close_sub_one_col _ S hθcol b).trans (le_max_right _ _)


/-- The kernels `Zk`, `Nk` of `ρ`, as functions of the carrier. -/
private abbrev BAS3Close_Kern : Type :=
  ∀ (d : ℕ) (sz : Sizes d) (_ : ℕ → ℂ) (n : ℕ) (_ : ℝ), Zd d (sz.L n) → Zd d (sz.L n) → ℂ

/-- The weight `ρ = t^p Z_{c₁c₃} M^{(B)}_{c₁c₂} M^{(B)}_{c₃c₄} N_{c₂c₄}`. -/
private def BAS3Close_rho (p : ℕ) (Zk Nk : BAS3Close_Kern) :
    ∀ (d : ℕ) (sz : Sizes d), (ℕ → ℂ) → ∀ n : ℕ, ℝ → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ :=
  fun d sz z n t _ _ c₁ c₂ c₃ c₄ => (t : ℂ) ^ p * Zk d sz z n t c₁ c₃ * BAExp14b_MB sz z n c₁ c₂ *
    BAExp14b_MB sz z n c₃ c₄ * Nk d sz z n t c₂ c₄

/-- The second clause of `BAFoldLeaf` for `ρ`. -/
private def BAS3Close_Bd (p : ℕ) (Zk Nk : BAS3Close_Kern) : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∃ Cρ : ℝ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
      ∀ a b : Zd d (sz.L n), (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖BAS3Close_rho p Zk Nk d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
        (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖BAS3Close_rho p Zk Nk d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ)

private theorem BAS3Close_cyc {ι : Type*} [Fintype ι] (a z nn : ι → ι → ℝ) (m zr zc ν : ℝ)
    (ha : ∀ x y, 0 ≤ a x y) (hz : ∀ x y, 0 ≤ z x y) (hm0 : 0 ≤ m) (hzc0 : 0 ≤ zc) (hν0 : 0 ≤ ν)
    (hrow : ∀ x, ∑ y, a x y ≤ m) (hcol : ∀ y, ∑ x, a x y ≤ m)
    (hzr : ∀ x, ∑ y, z x y ≤ zr) (hzc : ∀ y, ∑ x, z x y ≤ zc) (hnn : ∀ x y, nn x y ≤ ν) :
    (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, z c₁ c₃ * a c₁ c₂ * a c₃ c₄ * nn c₂ c₄ ≤ ν * (m * (zr * m))) ∧
      (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, z c₁ c₃ * a c₁ c₂ * a c₃ c₄ * nn c₂ c₄ ≤ ν * (m * (zc * m))) := by
  have key : ∀ c₁ c₂ c₃ c₄, z c₁ c₃ * a c₁ c₂ * a c₃ c₄ * nn c₂ c₄ ≤ ν * (a c₁ c₂ * (z c₁ c₃ * a c₃ c₄)) := by
    intro c₁ c₂ c₃ c₄
    have h0 : 0 ≤ a c₁ c₂ * (z c₁ c₃ * a c₃ c₄) := mul_nonneg (ha _ _) (mul_nonneg (hz _ _) (ha _ _))
    calc z c₁ c₃ * a c₁ c₂ * a c₃ c₄ * nn c₂ c₄ = (a c₁ c₂ * (z c₁ c₃ * a c₃ c₄)) * nn c₂ c₄ := by ring
      _ ≤ (a c₁ c₂ * (z c₁ c₃ * a c₃ c₄)) * ν := mul_le_mul_of_nonneg_left (hnn _ _) h0
      _ = ν * (a c₁ c₂ * (z c₁ c₃ * a c₃ c₄)) := by ring
  refine ⟨fun c₁ => ?_, fun c₄ => ?_⟩
  · calc ∑ c₂, ∑ c₃, ∑ c₄, z c₁ c₃ * a c₁ c₂ * a c₃ c₄ * nn c₂ c₄
        ≤ ∑ c₂, ∑ c₃, ∑ c₄, ν * (a c₁ c₂ * (z c₁ c₃ * a c₃ c₄)) :=
          Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ => Finset.sum_le_sum fun c₄ _ => key _ _ _ _
      _ = ν * ((∑ c₂, a c₁ c₂) * ∑ c₃, z c₁ c₃ * ∑ c₄, a c₃ c₄) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ ν * (m * (zr * m)) := by
          have hX : ∑ c₃, z c₁ c₃ * ∑ c₄, a c₃ c₄ ≤ zr * m :=
            calc ∑ c₃, z c₁ c₃ * ∑ c₄, a c₃ c₄ ≤ ∑ c₃, z c₁ c₃ * m :=
                  Finset.sum_le_sum fun c₃ _ => mul_le_mul_of_nonneg_left (hrow c₃) (hz _ _)
              _ = (∑ c₃, z c₁ c₃) * m := by rw [Finset.sum_mul]
              _ ≤ zr * m := mul_le_mul_of_nonneg_right (hzr c₁) hm0
          have hX0 : 0 ≤ ∑ c₃, z c₁ c₃ * ∑ c₄, a c₃ c₄ :=
            Finset.sum_nonneg fun c₃ _ => mul_nonneg (hz _ _) (Finset.sum_nonneg fun c₄ _ => ha _ _)
          have hA0 : 0 ≤ ∑ c₂, a c₁ c₂ := Finset.sum_nonneg fun c₂ _ => ha _ _
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hrow c₁) hX hX0 hm0) hν0
  · calc ∑ c₁, ∑ c₂, ∑ c₃, z c₁ c₃ * a c₁ c₂ * a c₃ c₄ * nn c₂ c₄
        ≤ ∑ c₁, ∑ c₂, ∑ c₃, ν * (a c₁ c₂ * (z c₁ c₃ * a c₃ c₄)) :=
          Finset.sum_le_sum fun c₁ _ => Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ => key _ _ _ _
      _ = ν * ∑ c₁, (∑ c₂, a c₁ c₂) * ∑ c₃, z c₁ c₃ * a c₃ c₄ := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ ν * ∑ c₁, m * ∑ c₃, z c₁ c₃ * a c₃ c₄ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c₁ _ => ?_) hν0
          exact mul_le_mul_of_nonneg_right (hrow c₁)
            (Finset.sum_nonneg fun c₃ _ => mul_nonneg (hz _ _) (ha _ _))
      _ = ν * (m * ∑ c₃, (∑ c₁, z c₁ c₃) * a c₃ c₄) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ ν * (m * ∑ c₃, zc * a c₃ c₄) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c₃ _ => ?_) hm0) hν0
          exact mul_le_mul_of_nonneg_right (hzc c₃) (ha _ _)
      _ = ν * (m * (zc * ∑ c₃, a c₃ c₄)) := by rw [← Finset.mul_sum]
      _ ≤ ν * (m * (zc * m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcol c₄) hzc0) hm0) hν0


private theorem BAS3Close_Bd_of (p : ℕ) (Zk Nk : BAS3Close_Kern)
    (hZ : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
      (∀ x, ∑ y, ‖Zk d sz z n t x y‖ ≤ K ^ 2) ∧ (∀ y, ∑ x, ‖Zk d sz z n t x y‖ ≤ K ^ 2))
    (hN : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
      ∀ x y, ‖Nk d sz z n t x y‖ ≤ K * m ^ 2) : BAS3Close_Bd p Zk Nk := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf
  obtain ⟨m, K, hm1, hK1, hev⟩ := BAS3Close_facts hd κ ε 𝔡 hκ 𝔠 h𝔡 sz z hf
  refine ⟨(K * m ^ 2) * (m * (K ^ 2 * m)), ?_⟩
  filter_upwards [hev] with n hn t ht0 ht a b
  have hF := hn t ht0 ht
  obtain ⟨ht1, -, -⟩ := BAS3Close_data sz hf n ht0 ht
  obtain ⟨hZr, hZc⟩ := hZ d sz z n t m K hm1 hK1 hF
  have hNn := hN d sz z n t m K hm1 hK1 hF
  obtain ⟨hmr, hmc, -, -⟩ := hF
  have hcyc := BAS3Close_cyc (fun x y => ‖BAExp14b_MB sz z n x y‖) (fun x y => ‖Zk d sz z n t x y‖)
    (fun x y => ‖Nk d sz z n t x y‖) m (K ^ 2) (K ^ 2) (K * m ^ 2) (fun _ _ => norm_nonneg _)
    (fun _ _ => norm_nonneg _) (by linarith) (by positivity) (by positivity) hmr hmc hZr hZc hNn
  have htp : ‖(t : ℂ) ^ p‖ ≤ 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact pow_le_one₀ ht0 ht1.le
  have hρ : ∀ c₁ c₂ c₃ c₄, ‖BAS3Close_rho p Zk Nk d sz z n t a b c₁ c₂ c₃ c₄‖ ≤
      ‖Zk d sz z n t c₁ c₃‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b_MB sz z n c₃ c₄‖ * ‖Nk d sz z n t c₂ c₄‖ := by
    intro c₁ c₂ c₃ c₄
    simp only [BAS3Close_rho, norm_mul]
    calc ‖(t : ℂ) ^ p‖ * ‖Zk d sz z n t c₁ c₃‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b_MB sz z n c₃ c₄‖ * ‖Nk d sz z n t c₂ c₄‖
        ≤ 1 * ‖Zk d sz z n t c₁ c₃‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b_MB sz z n c₃ c₄‖ * ‖Nk d sz z n t c₂ c₄‖ := by
          gcongr
      _ = _ := by ring
  refine ⟨fun c₁ => ?_, fun c₄ => ?_⟩
  · exact (Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ => Finset.sum_le_sum fun c₄ _ => hρ c₁ c₂ c₃ c₄).trans
      (hcyc.1 c₁)
  · exact (Finset.sum_le_sum fun c₁ _ => Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ => hρ c₁ c₂ c₃ c₄).trans
      (hcyc.2 c₄)


/-! The kernels. -/

private def BAS3Close_kD : BAS3Close_Kern := fun _ _ _ _ _ c c' => if c = c' then 1 else 0
private def BAS3Close_kK : BAS3Close_Kern := fun _ sz z n t c c' => (BAExp14b_om sz z n t - 1) c c'
private def BAS3Close_kKK : BAS3Close_Kern := fun _ sz z n t c c' =>
  ∑ c'', (BAExp14b_om sz z n t - 1) c c'' * (BAExp14b_om sz z n t - 1) c'' c'
private def BAS3Close_kB : BAS3Close_Kern := fun _ sz z n _ c c' => BAExp14b_MB sz z n c c' * BAExp14b_MB sz z n c' c
private def BAS3Close_k1 : BAS3Close_Kern := fun _ _ _ _ _ _ _ => 1

private theorem BAS3Close_le_row {ι : Type*} [Fintype ι] (f : ι → ι → ℂ) (x y : ι) : ‖f x y‖ ≤ ∑ y', ‖f x y'‖ :=
  Finset.single_le_sum (f := fun y' => ‖f x y'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)

private theorem BAS3Close_hZ_D : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
    (∀ x, ∑ y, ‖BAS3Close_kD d sz z n t x y‖ ≤ K ^ 2) ∧ (∀ y, ∑ x, ‖BAS3Close_kD d sz z n t x y‖ ≤ K ^ 2) := by
  intro d sz z n t m K hm hK _
  have h1 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK
  refine ⟨fun x => ?_, fun y => ?_⟩
  · have : ∑ y, ‖BAS3Close_kD d sz z n t x y‖ = 1 := by
      simp [BAS3Close_kD, apply_ite (fun z : ℂ => ‖z‖)]
    exact this.le.trans h1
  · have : ∑ x, ‖BAS3Close_kD d sz z n t x y‖ = 1 := by
      simp [BAS3Close_kD, apply_ite (fun z : ℂ => ‖z‖)]
    exact this.le.trans h1

private theorem BAS3Close_hZ_K : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
    (∀ x, ∑ y, ‖BAS3Close_kK d sz z n t x y‖ ≤ K ^ 2) ∧ (∀ y, ∑ x, ‖BAS3Close_kK d sz z n t x y‖ ≤ K ^ 2) := by
  intro d sz z n t m K hm hK hF
  have h1 : K ≤ K ^ 2 := by nlinarith
  exact ⟨fun x => (hF.2.2.1 x).trans h1, fun y => (hF.2.2.2 y).trans h1⟩

private theorem BAS3Close_hZ_KK : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
    (∀ x, ∑ y, ‖BAS3Close_kKK d sz z n t x y‖ ≤ K ^ 2) ∧ (∀ y, ∑ x, ‖BAS3Close_kKK d sz z n t x y‖ ≤ K ^ 2) := by
  intro d sz z n t m K hm hK hF
  obtain ⟨-, -, hr, hc⟩ := hF
  have hK0 : 0 ≤ K := by linarith
  refine ⟨fun x => ?_, fun y => ?_⟩
  · calc ∑ y, ‖BAS3Close_kKK d sz z n t x y‖
        ≤ ∑ y, ∑ c, ‖(BAExp14b_om sz z n t - 1) x c‖ * ‖(BAExp14b_om sz z n t - 1) c y‖ :=
          Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => (norm_mul _ _).le)
      _ = ∑ c, ‖(BAExp14b_om sz z n t - 1) x c‖ * ∑ y, ‖(BAExp14b_om sz z n t - 1) c y‖ := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ ∑ c, ‖(BAExp14b_om sz z n t - 1) x c‖ * K :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hr c) (norm_nonneg _)
      _ = (∑ c, ‖(BAExp14b_om sz z n t - 1) x c‖) * K := by rw [Finset.sum_mul]
      _ ≤ K * K := mul_le_mul_of_nonneg_right (hr x) hK0
      _ = K ^ 2 := by ring
  · calc ∑ x, ‖BAS3Close_kKK d sz z n t x y‖
        ≤ ∑ x, ∑ c, ‖(BAExp14b_om sz z n t - 1) x c‖ * ‖(BAExp14b_om sz z n t - 1) c y‖ :=
          Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => (norm_mul _ _).le)
      _ = ∑ c, (∑ x, ‖(BAExp14b_om sz z n t - 1) x c‖) * ‖(BAExp14b_om sz z n t - 1) c y‖ := by
          rw [Finset.sum_comm]; simp only [Finset.sum_mul]
      _ ≤ ∑ c, K * ‖(BAExp14b_om sz z n t - 1) c y‖ :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hc c) (norm_nonneg _)
      _ = K * ∑ c, ‖(BAExp14b_om sz z n t - 1) c y‖ := by rw [Finset.mul_sum]
      _ ≤ K * K := mul_le_mul_of_nonneg_left (hc y) hK0
      _ = K ^ 2 := by ring

private theorem BAS3Close_hN_D : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
    ∀ x y, ‖BAS3Close_kD d sz z n t x y‖ ≤ K * m ^ 2 := by
  intro d sz z n t m K hm hK _ x y
  have : (1 : ℝ) ≤ K * m ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hm]
  simp only [BAS3Close_kD]
  split_ifs <;> simp <;> linarith

private theorem BAS3Close_hN_K : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
    ∀ x y, ‖BAS3Close_kK d sz z n t x y‖ ≤ K * m ^ 2 := by
  intro d sz z n t m K hm hK hF x y
  have : K ≤ K * m ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hm]
  exact (BAS3Close_le_row _ x y).trans ((hF.2.2.1 x).trans this)

private theorem BAS3Close_hN_B : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
    ∀ x y, ‖BAS3Close_kB d sz z n t x y‖ ≤ K * m ^ 2 := by
  intro d sz z n t m K hm hK hF x y
  have h1 : ‖BAExp14b_MB sz z n x y‖ ≤ m := (BAS3Close_le_row _ x y).trans (hF.1 x)
  have h2 : ‖BAExp14b_MB sz z n y x‖ ≤ m := (BAS3Close_le_row _ y x).trans (hF.1 y)
  simp only [BAS3Close_kB, norm_mul]
  calc ‖BAExp14b_MB sz z n x y‖ * ‖BAExp14b_MB sz z n y x‖ ≤ m * m :=
        mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
    _ = 1 * m ^ 2 := by ring
    _ ≤ K * m ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hm]

private theorem BAS3Close_hN_1 : ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t m K : ℝ), 1 ≤ m → 1 ≤ K → BAS3Close_Fact sz z n t m K →
    ∀ x y, ‖BAS3Close_k1 d sz z n t x y‖ ≤ K * m ^ 2 := by
  intro d sz z n t m K hm hK _ x y
  have : (1 : ℝ) ≤ K * m ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hm]
  simpa [BAS3Close_k1] using this


/-- **Target 2.** -/
def BAFoldLeaf (q : BAPGraph (Fin 2)) : Prop :=
  ∃ (σ e : Bool) (ρ : ∀ (d : ℕ) (sz : Sizes d), (ℕ → ℂ) → ∀ n : ℕ, ℝ → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ),
    (∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y] =
          twLoop2X n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
            (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
              ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
            (fun c₁ c₂ c₃ c₄ => ρ d sz z n t a b c₁ c₂ c₃ c₄ *
              (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
                (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)) a) ∧
    (∀ (d : ℕ), 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
      BAFlow sz κ ε 𝔠 𝔡 z → ∃ Cρ : ℝ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
        ∀ a b : Zd d (sz.L n), (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ))

private def BAS3Close_Hq (q : BAPGraph (Fin 2)) (σ e : Bool) (qq : ℕ) (Zk Nk : BAS3Close_Kern) : Prop :=
  ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
      q.val (BAS3Close_D sz z n t ω) ![x, y] =
        ∑ u0, ∑ u1, ∑ u2, ∑ u3, (baFMz sz z).GM n t ω x u0 * (baFMz sz z).GM n t ω u1 u2 * (baFMz sz z).GM n t ω u3 y *
          twChg ((baFMz sz z).GM n t ω) σ y x * (baFMz sz z).M n u0 u1 * (baFMz sz z).M n u2 u3 *
          ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ((t : ℂ) ^ qq * Nk d sz z n t (split d (sz.L n) (sz.W n) u1).1
            (split d (sz.L n) (sz.W n) u3).1 *
            (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n (split d (sz.L n) (sz.W n) u1).1,
              ∑ v ∈ twBlk n (split d (sz.L n) (sz.W n) u3).1,
                (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)))) *
          ((t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Zk d sz z n t (split d (sz.L n) (sz.W n) u0).1
            (split d (sz.L n) (sz.W n) u2).1))

/-- The first clause of `BAFoldLeaf` for the weight `ρ = BAS3Close_rho (2 + qq) Zk Nk`, from the sum over the four core vertices. -/
private theorem BAS3Close_fold_gen_i (q : BAPGraph (Fin 2)) (σ e : Bool) (qq : ℕ) (Zk Nk : BAS3Close_Kern)
    (hq : BAS3Close_Hq q σ e qq Zk Nk) :
    ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y] =
          twLoop2X n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
            (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
              ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
            (fun c₁ c₂ c₃ c₄ => BAS3Close_rho (2 + qq) Zk Nk d sz z n t a b c₁ c₂ c₃ c₄ *
              (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
                (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)) a := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω a b
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hCL := BAS3Close_CL (t := t) hm σ (fun c c' => (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Zk d sz z n t c c'))
    (fun c c' => (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ((t : ℂ) ^ qq * Nk d sz z n t c c' *
      (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c, ∑ v ∈ twBlk n c',
        (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)))) ω a b
  refine Eq.trans ?_ (hCL.trans ?_)
  · simp only [hq d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω]
  · refine congrArg (fun f => twLoop2X n _ _ _ f a) (funext fun c₁ => funext fun c₂ => funext fun c₃ => funext fun c₄ => ?_)
    simp only [BAS3Close_rho]
    split_ifs <;> field_simp <;> ring

private theorem BAS3Close_hG {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a b : Idx d (sz.L n) (sz.W n)) :
    (BAS3Close_D sz z n t ω).G a b - (BAS3Close_D sz z n t ω).M a b = (baFMz sz z).GM n t ω a b := rfl

private theorem BAS3Close_hq00 (s : Bool) :
    BAS3Close_Hq (baS3Stuck false 0 s) s false 0 BAS3Close_kD BAS3Close_kD := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf0_0 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape00 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq01 (s : Bool) :
    BAS3Close_Hq (baS3Stuck false 1 s) s false 0 BAS3Close_kD BAS3Close_kK := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf0_1 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape01 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1_blk hm hr ht0 ht1 ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq02 (s : Bool) :
    BAS3Close_Hq (baS3Stuck false 2 s) s false 0 BAS3Close_kK BAS3Close_kD := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf0_2 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape02 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1_blk hm hr ht0 ht1 ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq03 (s : Bool) :
    BAS3Close_Hq (baS3Stuck false 3 s) s true 1 BAS3Close_kD BAS3Close_k1 := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf0_3 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape03 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK3_blk ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq04 (s : Bool) :
    BAS3Close_Hq (baS3Stuck false 4 s) s false 1 BAS3Close_kD BAS3Close_kB := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf0_4 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape04 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK2_blk hm ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq05 (s : Bool) :
    BAS3Close_Hq (baS3Stuck false 5 s) s true 1 BAS3Close_kK BAS3Close_k1 := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf0_5 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape05 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1_blk hm hr ht0 ht1 ω, BAS3Close_cK3_blk ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq06 (s : Bool) :
    BAS3Close_Hq (baS3Stuck false 6 s) s false 1 BAS3Close_kK BAS3Close_kB := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf0_6 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape06 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1_blk hm hr ht0 ht1 ω, BAS3Close_cK2_blk hm ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq10 (s : Bool) :
    BAS3Close_Hq (baS3Stuck true 0 s) s false 0 BAS3Close_kK BAS3Close_kD := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf1_0 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape10 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1T_blk hm hr ht0 ht1 ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq11 (s : Bool) :
    BAS3Close_Hq (baS3Stuck true 1 s) s false 0 BAS3Close_kK BAS3Close_kK := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf1_1 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape11 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1T_blk hm hr ht0 ht1 ω, BAS3Close_cK1_blk hm hr ht0 ht1 ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq12 (s : Bool) :
    BAS3Close_Hq (baS3Stuck true 2 s) s false 0 BAS3Close_kKK BAS3Close_kD := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf1_2 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape12 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK11_blk hm hr ht0 ht1 ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq13 (s : Bool) :
    BAS3Close_Hq (baS3Stuck true 3 s) s true 1 BAS3Close_kK BAS3Close_k1 := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf1_3 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape13 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1T_blk hm hr ht0 ht1 ω, BAS3Close_cK3_blk ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq14 (s : Bool) :
    BAS3Close_Hq (baS3Stuck true 4 s) s false 1 BAS3Close_kK BAS3Close_kB := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf1_4 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape14 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK1T_blk hm hr ht0 ht1 ω, BAS3Close_cK2_blk hm ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq15 (s : Bool) :
    BAS3Close_Hq (baS3Stuck true 5 s) s true 1 BAS3Close_kKK BAS3Close_k1 := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf1_5 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape15 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK11_blk hm hr ht0 ht1 ω, BAS3Close_cK3_blk ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

private theorem BAS3Close_hq16 (s : Bool) :
    BAS3Close_Hq (baS3Stuck true 6 s) s false 1 BAS3Close_kKK BAS3Close_kB := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω x y
  obtain ⟨ht1, hr, hm⟩ := BAS3Close_data sz hf n ht0 ht
  change (BAS3Close_pk (BAS3Close_cf1_6 s)).val _ _ = _
  rw [BAS3Close_pk_val, BAS3Close_shape16 s _ _ (BAS3Close_hG sz z n t ω) x y]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => ?_
  simp only [BAS3Close_D_S, BAS3Close_D_M, BAS3Close_cK11_blk hm hr ht0 ht1 ω, BAS3Close_cK2_blk hm ω, BAS3Close_kD, BAS3Close_kK, BAS3Close_kKK, BAS3Close_kB, BAS3Close_k1,
    pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

/-! ## The factor of #17, #47 -/

private theorem BAS3Close_norm_sub_sq (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a - b), norm_nonneg a, norm_nonneg b]

/-- The sum of `‖G‖²` over two blocks is `W^{2d}` times a `𝓛^{(2)}_{(+,-)}`. -/
private theorem BAS3Close_sqG {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ} (ω : sz.SeqΩ) (A B : Zd d (sz.L n)) :
    ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2) * ‖(baFMz sz z).L n t ![true, false] ![B, A] ω‖ =
      ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).G n t ω u v‖ ^ 2 := by
  rw [BAExp14b_L2_eq]
  have hWr : (((sz.W n : ℕ) : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have h1 : ∀ x y, twChg ((baFMz sz z).G n t ω) true x y * twChg ((baFMz sz z).G n t ω) false y x =
      ((‖(baFMz sz z).G n t ω x y‖ ^ 2 : ℝ) : ℂ) := by
    intro x y
    simp only [twChg, ite_true, Bool.false_eq_true, ite_false]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : ∑ x ∈ Iblk d (sz.L n) (sz.W n) A, ∑ y ∈ Iblk d (sz.L n) (sz.W n) B,
      twChg ((baFMz sz z).G n t ω) true x y * twChg ((baFMz sz z).G n t ω) false y x =
      ((∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).G n t ω u v‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [h1]; push_cast; rfl
  rw [h2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [norm_inv, Complex.norm_pow, Complex.norm_natCast]
  field_simp


private theorem BAS3Close_sqM {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {κ : ℝ}
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n)) (A B : Zd d (sz.L n)) :
    ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).M n u v‖ ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
  calc ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).M n u v‖ ^ 2
      ≤ ∑ u ∈ twBlk n A, ∑ v, ‖(baFMz sz z).M n u v‖ ^ 2 :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)
    _ = ∑ u ∈ twBlk n A, (1 : ℝ) := Finset.sum_congr rfl fun u _ =>
        baM_row_sq d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) ((baFMz sz z).m n) hr.1 u
    _ = ((sz.W n : ℕ) : ℝ) ^ d := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact TwistFold2_card_blk n A

private theorem BAS3Close_sqGM {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {κ : ℝ}
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n)) (t : ℝ) (ω : sz.SeqΩ)
    (Lm : ℝ) (hL : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baFMz sz z).L n t σ a ω‖ ≤ Lm)
    (A B : Zd d (sz.L n)) :
    ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).GM n t ω u v‖ ^ 2 ≤
      2 * ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2 * Lm) + 2 * ((sz.W n : ℕ) : ℝ) ^ d := by
  have hG := BAS3Close_sqG (z := z) (t := t) ω A B
  have hLm : ‖(baFMz sz z).L n t ![true, false] ![B, A] ω‖ ≤ Lm := hL _ _
  have hu : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ 2 := by positivity
  calc ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).GM n t ω u v‖ ^ 2
      ≤ ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, (2 * ‖(baFMz sz z).G n t ω u v‖ ^ 2 + 2 * ‖(baFMz sz z).M n u v‖ ^ 2) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => BAS3Close_norm_sub_sq _ _
    _ = 2 * ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).G n t ω u v‖ ^ 2 +
        2 * ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).M n u v‖ ^ 2 := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2 * Lm) + 2 * ((sz.W n : ℕ) : ℝ) ^ d := by
        rw [← hG]
        have := BAS3Close_sqM (z := z) hr A B
        gcongr


private theorem BAS3Close_Xbound {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {κ : ℝ}
    (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n)) (t : ℝ) (ω : sz.SeqΩ)
    (Lm : ℝ) (hL : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baFMz sz z).L n t σ a ω‖ ≤ Lm)
    (A B : Zd d (sz.L n)) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B,
        (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u‖ ≤ 2 * (((sz.W n : ℕ) : ℝ) ^ d * Lm) + 2 := by
  have hWr : 0 < (((sz.W n : ℕ) : ℝ) ^ d) := TwistFold2_u_pos n
  have hAB := BAS3Close_sqGM hr t ω Lm hL A B
  have hBA := BAS3Close_sqGM hr t ω Lm hL B A
  set w : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hw
  calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B,
        (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u‖
      = w⁻¹ * ‖∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u‖ := by
        rw [norm_mul]
        simp [hw]
    _ ≤ w⁻¹ * ∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, (‖(baFMz sz z).GM n t ω u v‖ ^ 2 / 2 +
          ‖(baFMz sz z).GM n t ω v u‖ ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_))) (inv_nonneg.2 hWr.le)
        rw [norm_mul]
        nlinarith [sq_nonneg (‖(baFMz sz z).GM n t ω u v‖ - ‖(baFMz sz z).GM n t ω v u‖)]
    _ = w⁻¹ * ((∑ u ∈ twBlk n A, ∑ v ∈ twBlk n B, ‖(baFMz sz z).GM n t ω u v‖ ^ 2) / 2 +
          (∑ u ∈ twBlk n B, ∑ v ∈ twBlk n A, ‖(baFMz sz z).GM n t ω u v‖ ^ 2) / 2) := by
        congr 1
        simp only [Finset.sum_add_distrib, ← Finset.sum_div]
        rw [Finset.sum_comm (s := twBlk n A) (t := twBlk n B)
          (f := fun u v => ‖(baFMz sz z).GM n t ω v u‖ ^ 2)]
    _ ≤ w⁻¹ * ((2 * (w ^ 2 * Lm) + 2 * w) / 2 + (2 * (w ^ 2 * Lm) + 2 * w) / 2) := by
        gcongr
    _ = 2 * (w * Lm) + 2 := by
        field_simp
        ring


/-- **Target 3′.** -/
def BAS3Xprec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      PrecL sz (Sizes.seqP (sz.withLam 0))
        (U := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n q ω => ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n q.2.2.1, ∑ v ∈ twBlk n q.2.2.2.2,
          (baFMz sz z).GM n (t n) ω u v * (baFMz sz z).GM n (t n) ω v u‖)
        (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n))

theorem baS3Xprec_holds : ∀ d : ℕ, BAS3Xprec d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hLmax
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (BAS3Close_data sz hflow n (ht0 n) (htT n)).1
  have hBpos : ∀ n, 0 < sz.Bctl n (t n) := fun n => STBctl_pos sz n (ht1 n)
  have hu : ∀ n, 0 < ((sz.W n : ℕ) : ℝ) ^ d := fun n => TwistFold2_u_pos n
  have h6a := twB0_ge_holds sz 𝔡 hflow.1.2.2.2.2 t ht0 (fun n => (ht1 n).le)
  set c0 : ℝ := (𝔡⁻¹ ^ 2 + 1)⁻¹ with hc0def
  have hc0 : 0 < c0 := by positivity
  set μ : Measure sz.SeqΩ := Sizes.seqP (sz.withLam 0) with hμ
  have dom2 : BAExp14a_Dom sz μ (fun n ω => TwistFold2_lmax sz z t 2 n ω / sz.Bctl n (t n) ^ (2 - 1)) (fun _ => 1) :=
    TwistFold2_dom_div (fun n => pow_pos (hBpos n) _)
      (TwistFold2_dom_lmax (μ := μ) (z := z) (t := t) (hLmax 2 (by norm_num)))
  have domY : BAExp14a_Dom sz μ (fun n ω => 2 * (TwistFold2_lmax sz z t 2 n ω / sz.Bctl n (t n) ^ (2 - 1)) + 2 * c0⁻¹)
      (fun _ => 1 + 2 * c0⁻¹) :=
    BAExp14a_Dom.add hsz (BAExp14a_Dom.const_mul hsz (c := 2) (by norm_num) (fun _ => zero_le_one) dom2)
      (BAExp14a_Dom.refl (μ := μ) hsz (g := fun _ => 2 * c0⁻¹) (fun _ => by positivity))
  have hY0 : ∀ n ω, 0 ≤ 2 * (TwistFold2_lmax sz z t 2 n ω / sz.Bctl n (t n) ^ (2 - 1)) + 2 * c0⁻¹ := fun n ω =>
    add_nonneg (mul_nonneg zero_le_two (div_nonneg (TwistFold2_lmax_nonneg z t 2 n ω) (pow_pos (hBpos n) _).le))
      (by positivity)
  have hw0 : ∀ n, 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n) := fun n => (mul_pos (hu n) (hBpos n)).le
  have dommain := BAExp14a_Dom.mul hsz (hY0) (hw0) (BAExp14a_Dom.refl (μ := μ) hsz hw0) domY
  have dom' := BAExp14a_Dom.mono hsz (K := 1 + 2 * c0⁻¹) (by positivity) hw0
    (Eventually.of_forall fun n => (mul_comm _ _).le) dommain
  have hpr := BAExp14a_Dom.index hsz (V := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) ×
    Zd d (sz.L n) × Zd d (sz.L n)) dom'
  refine BAExp14a_prec_of_le_ev ?_ hpr
  filter_upwards [h6a] with n h6n
  intro q ω
  obtain ⟨-, hr, -⟩ := BAS3Close_data sz hflow n (ht0 n) (htT n)
  have hX := BAS3Close_Xbound hr (t n) ω (TwistFold2_lmax sz z t 2 n ω)
    (fun σ a => TwistFold2_le_lmax z t 2 n ω σ a) q.2.2.1 q.2.2.2.2
  have hB := (hBpos n).ne'
  have hinv : 1 ≤ c0⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) := by
    calc (1 : ℝ) = c0⁻¹ * c0 := (inv_mul_cancel₀ hc0.ne').symm
      _ ≤ c0⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) := mul_le_mul_of_nonneg_left h6n (by positivity)
  refine hX.trans ?_
  have : ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n) *
      (2 * (TwistFold2_lmax sz z t 2 n ω / sz.Bctl n (t n) ^ (2 - 1)) + 2 * c0⁻¹) =
      2 * (((sz.W n : ℕ) : ℝ) ^ d * TwistFold2_lmax sz z t 2 n ω) + 2 * (c0⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n))) := by
    simp only [Nat.reduceSub, pow_one]
    field_simp
  rw [this]
  linarith


end Data

/-! ## 6. Targets 3, 4, 5 -/

/-! ## 7. Compiled nonempty instances (target 6) -/

end RBM.Graph

end
