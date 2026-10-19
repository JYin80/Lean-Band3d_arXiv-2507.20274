/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLTreeDeriv
import RBM3D.Loop.Unique
import RBM3D.Propagator.Prop6Hold

/-!
# Rotation and translation invariance of `𝒦`, `d ≥ 3`

`KLK_rotate`, `KLK_translate`: the cyclic and the translation symmetry of the `K`-loops `𝒦`
(`KLK`).

* Translation: the shifted family `J ↦ 𝒦(shift_c J)` is again a family of `K`-loops, hence equals
  `𝒦` by the uniqueness of the solution of `(pro_dyncalK)` (`uniqS_holds` and `retireS_holds` of
  `RBM3D/Loop/Unique.lean`; the a priori bound on the `2`-loops follows from continuity on the
  compact `[0,t] ⊆ [0,1)`).
* Rotation: the rotated family does not satisfy `(pro_dyncalK)` termwise (the equation at a
  rotated loop pairs the cuts of the original loop differently), so uniqueness is not used; one
  Grönwall step on `K ∘ rot - K` at each length `n`, by strong induction on `n`, with the
  `2`-loop bound from continuity (the same proof as `eq_on_levelS` of `RBM3D/Loop/Unique.lean`).

## Over a general kernel

The proofs of translation and rotation use `S = SB d L g` and `M = MLoop` only through
`‖S a b‖ ≤ 1`, `SB_transpose`, `SB_apply_add_right` and the invariance of `MLoop` under `rot` and
`shift`.  They are stated over `IsKLoopS` for a general kernel `S` and general initial data `M`:
the statements `RotS`, `TranslS` and their proofs `translS_holds`, `rotS_holds` (with the
uniqueness and two-loop bound `uniqS_holds`, `retireS_holds` of `RBM3D/Loop/Unique.lean`).  The
band statements `KLK_translate`, `KLK_rotate` are their instances at `S = SB d L g`,
`M = MLoop`.  The cut combinatorics (rotation of loop indices, the cuts at a rotated loop) is
`S`-free.  The hypotheses on `S` hold at `S = 1`: `kernel_one_rot_transl`.

`d` is a parameter and `3 ≤ d` is not used: no dimension-specific fact enters (the index type,
`SB`, the cuts and the translation action only).  Every helper is `private` and carries the file
stem as a prefix.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## The statements `RotS` and `TranslS`

They are proved below (`translS_holds`, `rotS_holds`) and give `KLK_translate` and
`KLK_rotate`. -/

/-- **`RotS`**: cyclic invariance of every family of `K`-loops on `[0,1)` (the form of `KLK_rotate`), for a symmetric
kernel with `‖S a b‖ ≤ 1` and rotation-invariant initial data. -/
def RotS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b, S a b = S b a) → (∀ a b, ‖S a b‖ ≤ 1) →
    (∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      M ⟨s :: σ, b :: a⟩ = M ⟨σ ++ [s], a ++ [b]⟩) →
    ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length → K t ⟨s :: σ, b :: a⟩ = K t ⟨σ ++ [s], a ++ [b]⟩

/-- **`TranslS`**: translation invariance of every family of `K`-loops on `[0,1)` (the form of `KLK_translate`), for a
translation-invariant kernel with `‖S a b‖ ≤ 1` and translation-invariant initial data. -/
def TranslS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b c : Zd d L, S (a + c) (b + c) = S a b) → (∀ a b, ‖S a b‖ ≤ 1) →
    (∀ (c : Zd d L) (I : LoopIdx (Zd d L)), M ⟨I.σ, I.a.map (· + c)⟩ = M I) →
    ∀ {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      K t ⟨I.σ, I.a.map (· + c)⟩ = K t I

/-! ## Translation: the shifted family is again a family of `K`-loops -/

section Translation

variable (d L : ℕ) [NeZero L]

/-- Shift every block label by `c`. -/
private def KLUnique_shift (c : Zd d L) (I : LoopIdx (Zd d L)) : LoopIdx (Zd d L) :=
  ⟨I.σ, I.a.map (· + c)⟩

omit [NeZero L] in
private theorem KLUnique_shift_WF {c : Zd d L} {I : LoopIdx (Zd d L)} (hI : I.WF) :
    (KLUnique_shift d L c I).WF := by
  simpa [LoopIdx.WF, KLUnique_shift] using hI

omit [NeZero L] in
private theorem KLUnique_length_shift (c : Zd d L) (I : LoopIdx (Zd d L)) :
    (KLUnique_shift d L c I).length = I.length := by
  simp [LoopIdx.length, KLUnique_shift]

omit [NeZero L] in
private theorem KLUnique_cutGlueL_shift (c : Zd d L) (I : LoopIdx (Zd d L)) (k l : ℕ)
    (b : Zd d L) :
    (KLUnique_shift d L c I).cutGlueL k l b = KLUnique_shift d L c (I.cutGlueL k l (b - c)) := by
  simp [KLUnique_shift, LoopIdx.cutGlueL, List.map_take, List.map_drop]

omit [NeZero L] in
private theorem KLUnique_cutGlueR_shift (c : Zd d L) (I : LoopIdx (Zd d L)) (k l : ℕ)
    (b : Zd d L) :
    (KLUnique_shift d L c I).cutGlueR k l b = KLUnique_shift d L c (I.cutGlueR k l (b - c)) := by
  simp [KLUnique_shift, LoopIdx.cutGlueR, List.map_take, List.map_drop]

/-- over a kernel `S` with `S (a + c) (b + c) = S a b`. -/
private theorem KLUnique_treeEqRhsS_shift (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ)
    (hSt : ∀ a b c : Zd d L, S (a + c) (b + c) = S a b) (K : LoopIdx (Zd d L) → ℂ) (c : Zd d L)
    (I : LoopIdx (Zd d L)) :
    treeEqRhsS d L W S K (KLUnique_shift d L c I)
      = treeEqRhsS d L W S (fun J => K (KLUnique_shift d L c J)) I := by
  rw [treeEqRhsS, treeEqRhsS, KLUnique_length_shift]
  congr 1
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  simp only [KLUnique_cutGlueL_shift, KLUnique_cutGlueR_shift]
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, hSt]

private theorem KLUnique_MLoop_shift (W : ℕ) (m : Bool → ℂ) (c : Zd d L) (I : LoopIdx (Zd d L)) :
    MLoop d L W m (KLUnique_shift d L c I) = MLoop d L W m I := by
  simp only [MLoop, KLUnique_length_shift]
  congr 2
  simp only [KLUnique_shift, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, add_left_inj]

/-- The translated family of an `IsKLoopS` family is an `IsKLoopS` family, for a
translation-invariant kernel `S` and translation-invariant initial data `M`, for a general family,
kernel and initial data. -/
private theorem KLUnique_isKLoopS_shift (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ)
    (hSt : ∀ a b c : Zd d L, S (a + c) (b + c) = S a b) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ)
    (hM : ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), M ⟨I.σ, I.a.map (· + c)⟩ = M I) {T : Set ℝ}
    {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoopS d L W S m M T K) (c : Zd d L) :
    IsKLoopS d L W S m M T (fun r J => K r (KLUnique_shift d L c J)) := by
  refine ⟨fun r hr J hJ h2 => ?_, fun J hJ h2 => ?_, fun r hr s a => ?_⟩
  · have := hK.1 r hr (KLUnique_shift d L c J) (KLUnique_shift_WF d L hJ)
      (by rw [KLUnique_length_shift]; exact h2)
    rwa [KLUnique_treeEqRhsS_shift d L W S hSt] at this
  · change K 0 (KLUnique_shift d L c J) = M J
    exact (hK.2.1 (KLUnique_shift d L c J) (KLUnique_shift_WF d L hJ)
      (by rw [KLUnique_length_shift]; exact h2)).trans (hM c J)
  · exact hK.2.2 r hr s (a + c)

end Translation

/-- **Translation invariance over a general kernel** (the statement `TranslS`).  For a
translation-invariant kernel `S` with `‖S a b‖ ≤ 1` and translation-invariant initial data `M`,
shifting all block labels by `c : Z_L^d` leaves every family `K` of `K`-loops on `[0,1)` unchanged:
the shifted family is again a family of `K`-loops (`KLUnique_isKLoopS_shift`), the `2`-loops of
both are bounded (`retireS_holds`), so they agree by `uniqS_holds`; the loops of length `1` are
the third clause, of length `0` the empty loop. -/
theorem translS_holds : TranslS := by
  intro d L W _ S m M hSt hS hM K hK t ht c I hI
  have hKc := KLUnique_isKLoopS_shift d L W S hSt m M hM hK c
  have hT : Set.Icc 0 t ⊆ Set.Ico 0 1 := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  obtain ⟨σ, a⟩ := I
  rcases a with _ | ⟨a₀, _ | ⟨a₁, a'⟩⟩
  · have h0 : σ = [] := List.length_eq_zero_iff.1 (hI : σ.length = 0)
    subst h0
    rfl
  · have h1 : σ.length = 1 := hI
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 h1
    exact (hK.2.2 t ht s (a₀ + c)).trans (hK.2.2 t ht s a₀).symm
  · obtain ⟨R, hR0, hR⟩ := retireS_holds d L W S m M hK t ht.2
    obtain ⟨R', hR'0, hR'⟩ := retireS_holds d L W S m M hKc t ht.2
    exact uniqS_holds d L W S m M hS hKc hK hT (R := max R R') (le_trans hR0 (le_max_left _ _))
      (fun r hr J hJ hJ2 => ⟨(hR' r hr J hJ hJ2).trans (le_max_right _ _),
        (hR r hr J hJ hJ2).trans (le_max_left _ _)⟩) t ⟨ht.1, le_rfl⟩ _ hI (by simp [LoopIdx.length])

/-- **Translation invariance of `𝒦`.** Shifting all block labels by `c : Z_L^d` leaves `𝒦`
unchanged: `translS_holds` at `S = SB d L g` (`SB_apply_add_right`), `M = MLoop`
(`KLUnique_MLoop_shift`) and the family `𝒦` (`KLK_isKLoop`). -/
theorem KLK_translate :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
        KLK d L g W E t ⟨I.σ, I.a.map (· + c)⟩ = KLK d L g W E t I := by
  intro d L W _ g E hL hW hE t ht c I hI
  exact translS_holds d L W (SB d L g) (mSigma E) (MLoop d L W (mSigma E))
    (fun a b c => SB_apply_add_right d L g a b c) (norm_SB_apply_le g hL)
    (fun c I => KLUnique_MLoop_shift d L W (mSigma E) c I) (KLK_isKLoop d L W g E hL hW hE) t ht c I hI

/-! ## Rotation: combinatorics of the cuts -/

/-- Move the first edge to the end. -/
private def KLUnique_rot {α : Type*} (x : LoopIdx α) : LoopIdx α := ⟨x.σ.rotate 1, x.a.rotate 1⟩

private theorem KLUnique_rot_mk_cons {α : Type*} (s : Bool) (ss : List Bool) (c : α)
    (cs : List α) :
    KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α) = ⟨ss ++ [s], cs ++ [c]⟩ := by
  simp [KLUnique_rot, List.rotate_cons_succ]

private theorem KLUnique_length_rot {α : Type*} (x : LoopIdx α) :
    (KLUnique_rot x).length = x.length := by
  simp [KLUnique_rot, LoopIdx.length, List.length_rotate]

private theorem KLUnique_WF_rot {α : Type*} {x : LoopIdx α} (hx : x.WF) :
    (KLUnique_rot x).WF := by
  simpa [LoopIdx.WF, KLUnique_rot, List.length_rotate] using hx

section RotCuts

variable {α : Type*} (s : Bool) (ss : List Bool) (c : α) (cs : List α) (b : α) {k l : ℕ}

private theorem KLUnique_cutGlueL_rot_of_lt (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ cs.length) :
    (KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueL k l b
      = KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueL (k + 1) (l + 1) b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [KLUnique_rot_mk_cons]
  simp only [LoopIdx.cutGlueL, Nat.add_sub_cancel, List.take_succ_cons, List.drop_succ_cons,
    List.cons_append]
  rw [KLUnique_rot_mk_cons]
  congr 1
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      List.append_assoc]
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
    simp

private theorem KLUnique_cutGlueR_rot_of_lt (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ cs.length) :
    (KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueR k l b
      = (⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueR (k + 1) (l + 1) b := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [KLUnique_rot_mk_cons]
  simp only [LoopIdx.cutGlueR, Nat.add_sub_cancel, List.drop_succ_cons]
  rw [show l + 1 - (k + 1 + 1) = l - (k + 1) by omega,
    List.drop_append_of_le_length (by omega : k ≤ ss.length),
    List.drop_append_of_le_length (by omega : k ≤ cs.length),
    List.take_append_of_le_length (by simp; omega),
    List.take_append_of_le_length (by simp; omega)]

private theorem KLUnique_cutGlueL_rot_last (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkn : k ≤ cs.length) :
    (KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueL k (cs.length + 1) b
      = KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueR 1 (k + 1) b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [KLUnique_rot_mk_cons]
  simp only [LoopIdx.cutGlueL, LoopIdx.cutGlueR, Nat.add_sub_cancel, Nat.sub_self,
    List.drop_zero, List.take_succ_cons, List.cons_append]
  rw [KLUnique_rot_mk_cons,
    List.take_append_of_le_length (by omega : k + 1 ≤ ss.length),
    List.take_append_of_le_length (by omega : k ≤ cs.length),
    List.drop_append_of_le_length (by omega : cs.length ≤ ss.length),
    List.drop_eq_nil_of_le (by omega : ss.length ≤ cs.length), List.drop_left]
  simp

private theorem KLUnique_cutGlueR_rot_last (hss : ss.length = cs.length) (hk : 1 ≤ k)
    (hkn : k ≤ cs.length) :
    (KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α)).cutGlueR k (cs.length + 1) b
      = KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx α).cutGlueL 1 (k + 1) b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [KLUnique_rot_mk_cons]
  simp only [LoopIdx.cutGlueL, LoopIdx.cutGlueR, Nat.add_sub_cancel, Nat.sub_self,
    List.take_zero, List.drop_succ_cons, List.nil_append, List.take_succ_cons, List.take_zero,
    List.singleton_append]
  rw [KLUnique_rot_mk_cons,
    List.drop_append_of_le_length (by omega : k ≤ ss.length),
    List.drop_append_of_le_length (by omega : k ≤ cs.length),
    List.take_of_length_le (by simp; omega),
    List.take_append_of_le_length (by simp),
    List.take_of_length_le (by simp)]

end RotCuts

/-! ## Rotation: the equation at a rotated loop -/

section RotEq

variable (d L : ℕ) [NeZero L] (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ)

private theorem KLUnique_treeEqRhsS_split (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    (hn : 1 ≤ I.length) :
    treeEqRhsS d L W S K I = (W : ℂ) ^ d *
      (∑ l ∈ Ioc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
          K (I.cutGlueL 1 l a) * S a b * K (I.cutGlueR 1 l b)
        + ∑ k ∈ Icc 2 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
          K (I.cutGlueL k l a) * S a b * K (I.cutGlueR k l b)) := by
  have h : Icc 1 I.length = insert 1 (Icc 2 I.length) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [treeEqRhsS, h, sum_insert (by simp)]

/-- `(pro_dyncalK)`'s right-hand side at the rotated loop of `(s :: ss, c :: cs)`, in terms of the
cuts of the original loop. -/
private theorem KLUnique_treeEqRhsS_rot (hsymm : ∀ a b, S a b = S b a) (K : LoopIdx (Zd d L) → ℂ)
    (s : Bool) (ss : List Bool) (c : Zd d L) (cs : List (Zd d L)) (hss : ss.length = cs.length) :
    treeEqRhsS d L W S K (KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L))) = (W : ℂ) ^ d *
      (∑ l ∈ Ioc 1 (cs.length + 1), ∑ a : Zd d L, ∑ b : Zd d L,
          K (KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueL 1 l a)) * S a b *
            K (KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueR 1 l b))
        + ∑ k ∈ Icc 2 (cs.length + 1), ∑ l ∈ Ioc k (cs.length + 1), ∑ a : Zd d L, ∑ b : Zd d L,
          K (KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueL k l a)) * S a b *
            K ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueR k l b)) := by
  have hrlen : (KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L))).length = cs.length + 1 := by
    rw [KLUnique_length_rot]
    simp [LoopIdx.length]
  rw [treeEqRhsS, hrlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero]
  have hsplit : ∀ k ∈ Icc 1 cs.length, ∑ l ∈ Ioc k (cs.length + 1), ∑ a : Zd d L, ∑ b : Zd d L,
      K ((KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L))).cutGlueL k l a) * S a b *
        K ((KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L))).cutGlueR k l b)
      = ∑ l ∈ Ioc k cs.length, ∑ a : Zd d L, ∑ b : Zd d L,
          K (KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueL (k + 1) (l + 1) a)) *
            S a b * K ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueR (k + 1) (l + 1) b)
        + ∑ a : Zd d L, ∑ b : Zd d L,
          K (KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueL 1 (k + 1) a)) *
            S a b *
            K (KLUnique_rot ((⟨s :: ss, c :: cs⟩ : LoopIdx (Zd d L)).cutGlueR 1 (k + 1) b)) := by
    intro k hk
    rw [mem_Icc] at hk
    rw [sum_Ioc_succ_top hk.2]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_Ioc] at hl
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [KLUnique_cutGlueL_rot_of_lt s ss c cs a hss hk.1 hl.1 hl.2,
        KLUnique_cutGlueR_rot_of_lt s ss c cs b hss hk.1 hl.1 hl.2]
    · rw [sum_comm]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [KLUnique_cutGlueL_rot_last s ss c cs b hss hk.1 hk.2,
        KLUnique_cutGlueR_rot_last s ss c cs a hss hk.1 hk.2,
        hsymm b a]
      ring
  rw [sum_congr rfl hsplit, sum_add_distrib, add_comm]
  refine congrArg _ (congrArg₂ (· + ·) ?_ ?_)
  · refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Icc, mem_Ioc] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Icc, mem_Ioc] at hx ⊢
      omega
    · intro x _
      simp
    · intro x hx
      simp only [mem_Ioc] at hx
      omega
    · intro x _
      rfl
  · refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    · intro x _
      simp
    · intro x hx
      simp only [mem_Icc] at hx
      omega
    · intro x _
      refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        simp only [mem_Ioc] at hy ⊢
        omega
      · intro y hy
        simp only [mem_Ioc] at hy ⊢
        omega
      · intro y _
        simp
      · intro y hy
        simp only [mem_Ioc] at hy
        omega
      · intro y _
        rfl

/-- The initial value of `Def_Ktza` is invariant under rotation. -/
private theorem KLUnique_MLoop_rot (m : Bool → ℂ) (I : LoopIdx (Zd d L)) :
    MLoop d L W m (KLUnique_rot I) = MLoop d L W m I := by
  simp only [MLoop, KLUnique_length_rot]
  congr 2
  · simp only [KLUnique_rot, List.map_rotate]
    exact (List.rotate_perm _ 1).prod_eq
  · simp only [KLUnique_rot, List.mem_rotate]

/-- One level of the induction for rotation: at length `n`, `K ∘ rot - K` solves a linear inequality
`‖D'‖ ≤ C ‖D‖` (Grönwall), the `2`-loops being bounded by `R`. -/
private theorem KLUnique_rot_eq_on_level (hsymm : ∀ a b, S a b = S b a) (hS : ∀ a b, ‖S a b‖ ≤ 1)
    (K : ℝ → LoopIdx (Zd d L) → ℂ)
    (T₀ R : ℝ) (n : ℕ) (hn : 2 ≤ n) (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      HasDerivAt (fun s => K s I) (treeEqRhsS d L W S (K t) I) t)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      I.length < n → K t (KLUnique_rot I) = K t I)
    (h0 : ∀ I : LoopIdx (Zd d L), I.WF → I.length = n → K 0 (KLUnique_rot I) = K 0 I) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = n →
      K t (KLUnique_rot I) = K t I := by
  let D : ℝ → LoopVec d L n → ℂ := fun t p =>
    K t (KLUnique_rot (p.toLoop d L)) - K t (p.toLoop d L)
  let D' : ℝ → LoopVec d L n → ℂ := fun t p =>
    treeEqRhsS d L W S (K t) (KLUnique_rot (p.toLoop d L)) - treeEqRhsS d L W S (K t) (p.toLoop d L)
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := fun t ht =>
    hasDerivAt_pi.2 fun p =>
      (hK t ht _ (KLUnique_WF_rot p.wf)
          (by rw [KLUnique_length_rot, p.length]; exact hn)).sub
        (hK t ht _ p.wf (p.length.symm ▸ hn))
  let C : ℝ := (W : ℝ) ^ d * ((∑ _l ∈ Ioc 1 n, ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * R)
    + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * R)
  have hC : 0 ≤ C := by
    refine mul_nonneg (pow_nonneg (Nat.cast_nonneg W) d) (add_nonneg ?_ ?_)
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => by positivity
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have hdiff : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖K t (KLUnique_rot J) - K t J‖ ≤ ‖D t‖ := by
      intro J hJ h2 hle
      rcases hle.lt_or_eq with hlt | heq
      · rw [hlow t ht' J hJ h2 hlt, sub_self, norm_zero]
        exact norm_nonneg _
      · obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop J hJ heq
        exact norm_le_pi_norm (D t) p
    have hRD : 0 ≤ R * ‖D t‖ := mul_nonneg hR0 (norm_nonneg _)
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).2 fun p => ?_
    have hI : (p.toLoop d L).WF := p.wf
    have hIn : (p.toLoop d L).length = n := p.length
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_length_pos
      (show 0 < (p.toLoop d L).a.length from by rw [← LoopIdx.length, hIn]; omega)
    obtain ⟨s, ss, hss'⟩ := List.exists_cons_of_length_pos
      (show 0 < (p.toLoop d L).σ.length from by rw [hI, ← LoopIdx.length, hIn]; omega)
    have hIeq : p.toLoop d L = ⟨s :: ss, c :: cs⟩ := LoopIdx.ext hss' hcs
    have hss : ss.length = cs.length := by
      have := hI
      rw [hIeq] at this
      simpa [LoopIdx.WF] using this
    have hn' : cs.length + 1 = n := by
      rw [← hIn, hIeq]
      simp [LoopIdx.length]
    set I : LoopIdx (Zd d L) := ⟨s :: ss, c :: cs⟩ with hIdef
    have hIWF : I.WF := hIeq ▸ hI
    have hIlen : I.length = n := hIeq ▸ hIn
    have hcut : ∀ k l, 1 ≤ k → k < l → l ≤ n → ∀ a b : Zd d L,
        (I.cutGlueL k l a).WF ∧ (I.cutGlueR k l b).WF ∧
        2 ≤ (I.cutGlueL k l a).length ∧ 2 ≤ (I.cutGlueR k l b).length ∧
        (I.cutGlueL k l a).length ≤ n ∧ (I.cutGlueR k l b).length ≤ n ∧
        ((I.cutGlueL k l a).length = n → (I.cutGlueR k l b).length = 2) ∧
        ((I.cutGlueR k l b).length = n → (I.cutGlueL k l a).length = 2) := by
      intro k l hk hkl hl a b
      have hlI : l ≤ I.length := hIlen ▸ hl
      refine ⟨LoopIdx.wf_cutGlueL I a hIWF hk hkl hlI, LoopIdx.wf_cutGlueR I b hIWF hk hkl hlI,
        LoopIdx.two_le_length_cutGlueL I a hk hkl hlI,
        LoopIdx.two_le_length_cutGlueR I b hk hkl hlI,
        hIlen ▸ LoopIdx.length_cutGlueL_le I a hk hkl hlI,
        hIlen ▸ LoopIdx.length_cutGlueR_le I b hk hkl hlI, fun h => ?_, fun h => ?_⟩
      · exact LoopIdx.length_cutGlueR_eq_two I a b hk hkl hlI (h.trans hIlen.symm)
      · exact LoopIdx.length_cutGlueL_eq_two I a b hk hkl hlI (h.trans hIlen.symm)
    have hA : ∀ l ∈ Ioc 1 n, ∀ a b : Zd d L,
        ‖K t (KLUnique_rot (I.cutGlueL 1 l a)) * S a b * K t (KLUnique_rot (I.cutGlueR 1 l b))
          - K t (I.cutGlueL 1 l a) * S a b * K t (I.cutGlueR 1 l b)‖
          ≤ 2 * (R * ‖D t‖) := by
      intro l hl a b
      rw [mem_Ioc] at hl
      obtain ⟨hWL, hWR, h2L, h2R, hLn, hRn, hLR, hRL⟩ := hcut 1 l le_rfl hl.1 hl.2 a b
      refine norm_mul_mul_sub_le (hS a b) ?_ ?_
      · rcases hLn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have hY := hR t ht' _ (KLUnique_WF_rot hWR)
            (by rw [KLUnique_length_rot]; exact hLR heq)
          rw [mul_comm R]
          exact mul_le_mul (hdiff _ hWL h2L hLn) hY (norm_nonneg _) (norm_nonneg _)
      · rcases hRn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWR h2R hlt, sub_self, norm_zero, mul_zero]
          exact hRD
        · have hX := hR t ht' _ hWL (hRL heq)
          exact mul_le_mul hX (hdiff _ hWR h2R hRn) (norm_nonneg _) hR0
    have hB : ∀ k ∈ Icc 2 n, ∀ l ∈ Ioc k n, ∀ a b : Zd d L,
        ‖K t (KLUnique_rot (I.cutGlueL k l a)) * S a b * K t (I.cutGlueR k l b)
          - K t (I.cutGlueL k l a) * S a b * K t (I.cutGlueR k l b)‖
          ≤ 2 * (R * ‖D t‖) := by
      intro k hk l hl a b
      rw [mem_Icc] at hk
      rw [mem_Ioc] at hl
      obtain ⟨hWL, hWR, h2L, h2R, hLn, hRn, hLR, hRL⟩ :=
        hcut k l (by omega) hl.1 hl.2 a b
      refine norm_mul_mul_sub_le (hS a b) ?_ ?_
      · rcases hLn.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have hY := hR t ht' _ hWR (hLR heq)
          rw [mul_comm R]
          exact mul_le_mul (hdiff _ hWL h2L hLn) hY (norm_nonneg _) (norm_nonneg _)
      · rw [sub_self, norm_zero, mul_zero]
        exact hRD
    have e : D' t p = (W : ℂ) ^ d *
        ((∑ l ∈ Ioc 1 n, ∑ a : Zd d L, ∑ b : Zd d L,
          (K t (KLUnique_rot (I.cutGlueL 1 l a)) * S a b * K t (KLUnique_rot (I.cutGlueR 1 l b))
            - K t (I.cutGlueL 1 l a) * S a b * K t (I.cutGlueR 1 l b)))
        + ∑ k ∈ Icc 2 n, ∑ l ∈ Ioc k n, ∑ a : Zd d L, ∑ b : Zd d L,
          (K t (KLUnique_rot (I.cutGlueL k l a)) * S a b * K t (I.cutGlueR k l b)
            - K t (I.cutGlueL k l a) * S a b * K t (I.cutGlueR k l b))) := by
      simp only [D']
      rw [hIeq, KLUnique_treeEqRhsS_rot d L W S hsymm (K t) s ss c cs hss,
        KLUnique_treeEqRhsS_split d L W S (K t) _ (by rw [hIlen]; omega)]
      simp only [← hIdef]
      rw [hIlen, hn']
      simp only [Finset.sum_sub_distrib]
      ring
    rw [e, norm_mul, norm_pow, Complex.norm_natCast]
    have hsum : ‖(∑ l ∈ Ioc 1 n, ∑ a : Zd d L, ∑ b : Zd d L,
          (K t (KLUnique_rot (I.cutGlueL 1 l a)) * S a b * K t (KLUnique_rot (I.cutGlueR 1 l b))
            - K t (I.cutGlueL 1 l a) * S a b * K t (I.cutGlueR 1 l b)))
        + ∑ k ∈ Icc 2 n, ∑ l ∈ Ioc k n, ∑ a : Zd d L, ∑ b : Zd d L,
          (K t (KLUnique_rot (I.cutGlueL k l a)) * S a b * K t (I.cutGlueR k l b)
            - K t (I.cutGlueL k l a) * S a b * K t (I.cutGlueR k l b))‖
        ≤ (∑ _l ∈ Ioc 1 n, ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * (R * ‖D t‖))
          + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * (R * ‖D t‖) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        exact hA l hl a b
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        exact hB k hk l hl a b
    calc (W : ℝ) ^ d * ‖_‖ ≤ (W : ℝ) ^ d *
          ((∑ _l ∈ Ioc 1 n, ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * (R * ‖D t‖))
          + ∑ k ∈ Icc 2 n, ∑ _l ∈ Ioc k n, ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * (R * ‖D t‖)) :=
          mul_le_mul_of_nonneg_left hsum (pow_nonneg (Nat.cast_nonneg W) d)
      _ = C * ‖D t‖ := by simp only [C, Finset.sum_mul, add_mul, mul_assoc]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (funext fun p => sub_eq_zero.2 (h0 _ p.wf p.length)) hbound
  intro t ht I hI hIn
  obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop I hI hIn
  exact sub_eq_zero.1 (congrFun (hzero t ht) p)

/-- `KLUnique_MLoop_rot` in the form of the hypothesis of `RotS` (at `M = MLoop d L W m`). -/
private theorem KLUnique_MLoop_rot_cons (m : Bool → ℂ) (s : Bool) (b : Zd d L) (σ : List Bool)
    (a : List (Zd d L)) (_ : σ.length = a.length) :
    MLoop d L W m ⟨s :: σ, b :: a⟩ = MLoop d L W m ⟨σ ++ [s], a ++ [b]⟩ := by
  have := KLUnique_MLoop_rot d L W m ⟨s :: σ, b :: a⟩
  rw [KLUnique_rot_mk_cons] at this
  exact this.symm

omit [NeZero L] in
/-- Rotation invariance of the initial data, from the hypothesis of the statement `RotS`: for a
well-formed loop `J` of length `≥ 1`, `M (rot J) = M J`. -/
private theorem KLUnique_M_rot (M : LoopIdx (Zd d L) → ℂ)
    (hMrot : ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      M ⟨s :: σ, b :: a⟩ = M ⟨σ ++ [s], a ++ [b]⟩)
    (J : LoopIdx (Zd d L)) (hJ : J.WF) (h : 1 ≤ J.length) : M (KLUnique_rot J) = M J := by
  obtain ⟨σ, a⟩ := J
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_length_pos (show 0 < a.length from h)
  have hl : σ.length = cs.length + 1 := hJ
  obtain ⟨s, ss, rfl⟩ := List.exists_cons_of_length_pos (show 0 < σ.length by omega)
  rw [KLUnique_rot_mk_cons]
  exact (hMrot s c ss cs (by simpa using hl)).symm

/-- Cyclic invariance of an `IsKLoopS` family with bounded `2`-loops, at lengths `≥ 2`, for a
symmetric kernel with `‖S a b‖ ≤ 1` and rotation-invariant initial data `M`. -/
private theorem KLUnique_isKLoopS_rot (hsymm : ∀ a b, S a b = S b a) (hS : ∀ a b, ‖S a b‖ ≤ 1)
    (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ)
    (hMrot : ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      M ⟨s :: σ, b :: a⟩ = M ⟨σ ++ [s], a ++ [b]⟩) {T : Set ℝ}
    {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoopS d L W S m M T K) {T₀ R : ℝ}
    (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      K t (KLUnique_rot I) = K t I := by
  have main : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      I.length = n → K t (KLUnique_rot I) = K t I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht I hI h2 hIn
      have hn : 2 ≤ n := hIn ▸ h2
      refine KLUnique_rot_eq_on_level d L W S hsymm hS K T₀ R n hn hR0 (fun s hs => hK.1 s (hT hs)) hR
        ?_ ?_ t ht I hI hIn
      · intro s hs J hJ hJ2 hJn
        exact ih _ hJn s hs J hJ hJ2 rfl
      · intro J hJ hJn
        rw [hK.2.1 _ (KLUnique_WF_rot hJ) (by rw [KLUnique_length_rot, hJn]; exact hn),
          hK.2.1 _ hJ (hJn ▸ hn), KLUnique_M_rot d L M hMrot J hJ (by omega)]
  intro t ht I hI h2
  exact main _ t ht I hI h2 rfl

end RotEq

/-- **Cyclic invariance over a general kernel** (the statement `RotS`).  Every family of `K`-loops
on `[0,1)` over a symmetric kernel `S` with `‖S a b‖ ≤ 1` and rotation-invariant initial data `M`
is invariant under moving the first edge to the end.  The length-`1` case is a syntactic equality;
for length `≥ 2` see `KLUnique_isKLoopS_rot` with the `2`-loop bound from continuity on
`[0, t] ⊆ [0, 1)` (`retireS_holds`). -/
theorem rotS_holds : RotS := by
  intro d L W _ S m M hsymm hS hMrot K hK t ht s b σ a hσa
  rcases a with _ | ⟨a₀, a'⟩
  · have : σ = [] := List.length_eq_zero_iff.1 (by simpa using hσa)
    subst this
    rfl
  · have hT : Set.Icc 0 t ⊆ Set.Ico 0 1 := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    obtain ⟨R, hR0, hR⟩ := retireS_holds d L W S m M hK t ht.2
    have hwf : (⟨s :: σ, b :: a₀ :: a'⟩ : LoopIdx (Zd d L)).WF := by
      simpa [LoopIdx.WF] using hσa
    have h2 : 2 ≤ (⟨s :: σ, b :: a₀ :: a'⟩ : LoopIdx (Zd d L)).length := by
      simp [LoopIdx.length]
    have := KLUnique_isKLoopS_rot d L W S hsymm hS m M hMrot hK hT hR0 hR t
      ⟨ht.1, le_rfl⟩ _ hwf h2
    rw [KLUnique_rot_mk_cons] at this
    exact this.symm

/-- **Cyclic invariance of `𝒦`.** `𝒦` is invariant under moving the first edge to the end:
`rotS_holds` at `S = SB d L g` (`SB_transpose`, `norm_SB_apply_le`), `M = MLoop`
(`KLUnique_MLoop_rot`) and the family `𝒦` (`KLK_isKLoop`). -/
theorem KLK_rotate :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
        KLK d L g W E t ⟨s :: σ, b :: a⟩ = KLK d L g W E t ⟨σ ++ [s], a ++ [b]⟩ := by
  intro d L W _ g E hL hW hE t ht s b σ a hσa
  exact rotS_holds d L W (SB d L g) (mSigma E) (MLoop d L W (mSigma E))
    (fun a b => (show SB d L g b a = SB d L g a b from
      congrFun (congrFun (SB_transpose d L g) a) b).symm)
    (norm_SB_apply_le g hL) (KLUnique_MLoop_rot_cons d L W (mSigma E)) (KLK_isKLoop d L W g E hL hW hE)
    t ht s b σ a hσa

section Instances

/-- The hypotheses on `S` of `RotS` and `TranslS` hold at the block Anderson kernel `S = 1`
(`S^{(B)}(0) = I`): symmetry, `‖S a b‖ ≤ 1`, translation invariance.  Nothing is assumed of `d`,
`L` beyond `NeZero L`. -/
theorem kernel_one_rot_transl {d L : ℕ} [NeZero L] :
    (∀ a b : Zd d L, (1 : Matrix (Zd d L) (Zd d L) ℂ) a b = (1 : Matrix (Zd d L) (Zd d L) ℂ) b a) ∧
    (∀ a b : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a b‖ ≤ 1) ∧
    (∀ a b c : Zd d L, (1 : Matrix (Zd d L) (Zd d L) ℂ) (a + c) (b + c)
      = (1 : Matrix (Zd d L) (Zd d L) ℂ) a b) :=
  ⟨fun a b => by simp only [Matrix.one_apply]; exact if_congr eq_comm rfl rfl,
    fun a b => by simp only [Matrix.one_apply]; split_ifs <;> simp,
    fun a b c => by simp only [Matrix.one_apply, add_left_inj]⟩

end Instances

end RBM.Loop
