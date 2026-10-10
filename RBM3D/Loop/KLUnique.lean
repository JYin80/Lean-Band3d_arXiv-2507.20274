/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLTreeDeriv
import RBM3D.Loop.TreeThree
import RBM3D.Propagator.Prop6Hold

/-!
# The `K`-loop layer, fourth and fifth rows (KL4 + KL5): uniqueness,
# rotation and translation invariance of `𝒦`, `d ≥ 3`

Ticket T2025 (design ticket T2004, rows KL4 and KL5).  Names are in `RBM.Loop`.

* **`RBM.Loop.KLK_unique`** is the pin `KLuniquePin` (`64b58eb:RBM3D/Probe/T2004Pins.lean:762-768`),
  proved: every family `K` of `K`-loops on `[0,1)` (merged `IsKLoop`) equals the tree sum `KLK` of
  KL1 (`RBM3D/Loop/KLTree.lean`) on every well-formed loop of length `≥ 1`, for `t ∈ [0,1)`.  The
  a priori bound on the `2`-loops is not an input: it follows from continuity on the compact
  `[0,t] ⊆ [0,1)` (`KLretire_twoLoopBounded`), and the merged `isKLoop_unique`
  (`RBM3D/Loop/Unique.lean:247`) does the rest for length `≥ 2`; length `1` is the third clause of
  `IsKLoop`, for `K` and (by `KLK_isKLoop`, KL3) for `KLK`.
* **`KLretire_twoLoopBounded`** (now in `RBM3D/Loop/Unique.lean`, moved there by ticket T2127)
  retires the old a priori hypothesis (deleted) of the merged `kTwoFormula_of_isKLoop`,
  `kThree_eq_of_isKLoop`, `pureLoop_two_of_isKLoop`, `pureLoop_three`; copied from the T2004 probe
  (`64b58eb:RBM3D/Probe/T2004Pins.lean:915-971`, compiled there).  `KLretire_KLoopBound` of that
  probe section needs `KLBoundAt` (KL11) and is not here.
* **`RBM.Loop.KLK_rotate`, `RBM.Loop.KLK_translate`**: the cyclic and the translation symmetry of
  `𝒦`, ports of `Kcal_rotate` and `Kcal_translate` (`RBM2D/Loop/Cyclic.lean:569, 594` at `c9a24cf`).
  Translation: the shifted family `J ↦ 𝒦(shift_c J)` is again a family of `K`-loops, hence equals
  `𝒦` by `KLK_unique`.  Rotation: the rotated family does not satisfy `(pro_dyncalK)` termwise (the
  equation at a rotated loop pairs the cuts of the original loop differently), so uniqueness is not
  used; one Grönwall step on `K ∘ rot - K` at each length `n`, by strong induction on `n`, with the
  `2`-loop bound from continuity (the same proof as `eq_on_level` of `Loop/Unique.lean`).

## Sources and changes

Everything below is a port of RBM2D at commit `c9a24cf`, read-only: `Loop/Unique.lean`:
`Unique_two_loop_bound` 254, `isPrimitive_eq_Kcal` 276; `Loop/Cyclic.lean`: `Cyclic_rot` 135,
`Cyclic_rot_mk_cons` 137, `Cyclic_length_rot` 142, `Cyclic_WF_rot` 146,
`Cyclic_cutGlueL_rot_of_lt` 153, `Cyclic_cutGlueR_rot_of_lt` 169, `Cyclic_cutGlueL_rot_last` 182,
`Cyclic_cutGlueR_rot_last` 197, `Cyclic_primRhs_split` 221, `Cyclic_primRhs_rot` 236,
`Cyclic_primInit_rot` 319, `Cyclic_rot_eq_on_level` 328, `Cyclic_isPrimitive_rot` 487,
`Cyclic_shift` 519, `Cyclic_shift_WF` 523, `Cyclic_length_shift` 528, `Cyclic_cutGlueL_shift` 533,
`Cyclic_cutGlueR_shift` 538, `Cyclic_primRhs_shift` 542, `Cyclic_primInit_shift` 555,
`Kcal_rotate` 569, `Kcal_translate` 594.

Changes: the renaming `Z2 L ↦ Zd d L`; `primRhs L W`, `primInit L W`, `IsPrimitive L W`, `mSig`,
`Kcal L W E` ↦ `treeEqRhs d L W g`, `MLoop d L W`, `IsKLoop d L W g`, `mSigma`, `KLK d L g W E`;
`SB L ↦ SB d L g`; `SB_transpose L ↦ SB_transpose d L g`; `W^2 ↦ W^d`. The binders of the theorem
statements are `(d L W : ℕ) [NeZero L] (g E : ℝ)` (as in `KLisKLoopPin` and `KLuniquePin`),
instead of RBM2D's `(L W : ℕ) [NeZero L]` ... `∀ E : ℝ`. The helpers of `Cyclic.lean` that the
merged `Loop/Unique.lean` already provides (`Cyclic_two_le_length_cutGlueL/R`,
`Cyclic_length_cutGlueL/R_le`, `Cyclic_cutGlueR/L_length_eq_two`, `Cyclic_LoopVec`,
`Cyclic_toLoop*`, `Cyclic_norm_SB_apply_le`, `Cyclic_norm_mul_mul_sub_le`,
`Cyclic_two_loop_bound`) are not re-ported: the merged `LoopIdx.two_le_length_cutGlueL/R`,
`LoopIdx.length_cutGlueL/R_le`, `LoopIdx.length_cutGlueR/L_eq_two`, `LoopIdx.wf_cutGlueL/R`,
`LoopVec`, `LoopVec.toLoop/wf/length/exists_toLoop`, `norm_SB_apply_le`, `norm_mul_mul_sub_le` and
`KLretire_twoLoopBounded` replace them. One proof step differs: in `KLUnique_treeEqRhs_rot`,
`congr 1` is replaced by `refine congrArg₂ (· + ·) ?_ ?_` (`congr 1` stops with a `whnf` heartbeat
timeout there, on the sums over `Zd d L`). The inline block `hK'` of `Kcal_translate` is the
private lemma `KLUnique_isKLoop_shift` (for a general family; the instance
`KLUniqueInst_unique_shifted` uses it).

Every helper is `private` and carries the file stem `KLUnique_`.  No hypothesis `Prop` is added,
`d` is a parameter and `3 ≤ d` is not used (no dimension-specific fact enters: the index type,
`SB`, the cuts and the translation action only).

## Over a general kernel (ticket T2366, gate BA stage K)

The proofs of translation and rotation use `S = SB d L g` and `M = MLoop` only through `‖S a b‖ ≤ 1`,
`SB_transpose`, `SB_apply_add_right` and the invariance of `MLoop` under `rot` and `shift`.  They are
restated over `IsKLoopS` for a general kernel `S` and general initial data `M`: `RotS`, `TranslS` (pins)
and `translS_holds`, `rotS_holds` (proofs, with the uniqueness and two-loop bound `uniqS_holds`,
`retireS_holds` of `Loop/Unique.lean`).  The band statements `KLK_translate`, `KLK_rotate` (and
`KLK_unique`) are their instances at `S = SB d L g`, `M = MLoop`; their statements are unchanged.  The
cut combinatorics of section 4 is `S`-free.  The hypotheses on `S` are compiled at `S = 1` and
`S = SB d L g` as `kernel_one_rot_transl`, `kernel_SB_rot_transl`.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. The generic pins (gate BA, stage K, ticket T2366)

`UniqS` and `RetireS` are in `Loop/Unique.lean` (`uniqS_holds`, `retireS_holds`); the pins below are
proved in sections 3 and 5 and re-derive `KLK_translate` and `KLK_rotate`. -/

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

/-! ## 2. The pinned theorem `KLK_unique` (section 1, `KLretire_twoLoopBounded`, is in `Loop/Unique.lean`) -/

/-- **Pin `Def_Ktza`, "unique"**: every family of `K`-loops on `[0,1)` is `KLK` (no a priori
bound on the `2`-loops: it follows from continuity on `[0,t] ⊆ [0,1)`).  The type is the body
of the pin `KLuniquePin` (`64b58eb:RBM3D/Probe/T2004Pins.lean:762-768`). -/
theorem KLK_unique :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 →
      ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoop d L W g (mSigma E) (Set.Ico 0 1) K →
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length →
          K t I = KLK d L g W E t I := by
  intro d L W _ g E hL hW hE K hK t ht I hI hI1
  have hKc := KLK_isKLoop d L W g E hL hW hE
  rcases hI1.lt_or_eq with h2 | h1
  · have hT : Set.Icc 0 t ⊆ Set.Ico 0 1 := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    obtain ⟨R, hR0, hR⟩ := KLretire_twoLoopBounded hK t ht.2
    obtain ⟨R', hR'0, hR'⟩ := KLretire_twoLoopBounded hKc t ht.2
    refine isKLoop_unique hL (mSigma E) hK hKc hT
      (R := max R R') (le_trans hR0 (le_max_left _ _)) (fun s hs J hJ hJ2 => ?_) t
      ⟨ht.1, le_rfl⟩ I hI h2
    exact ⟨(hR s hs J hJ hJ2).trans (le_max_left _ _),
      (hR' s hs J hJ hJ2).trans (le_max_right _ _)⟩
  · obtain ⟨σ, a⟩ := I
    have ha : a.length = 1 := by simpa [LoopIdx.length] using h1.symm
    have hσ : σ.length = 1 := hI.trans ha
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hσ
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
    rw [hK.2.2 t ht s x]
    exact (hKc.2.2 t ht s x).symm

/-! ## 3. Translation: the shifted family is again a family of `K`-loops -/

section Translation

variable (d L : ℕ) [NeZero L]

/-- Shift every block label by `c`.  Port of `RBM2D/Loop/Cyclic.lean:519` at `c9a24cf`
(`Cyclic_shift`). -/
private def KLUnique_shift (c : Zd d L) (I : LoopIdx (Zd d L)) : LoopIdx (Zd d L) :=
  ⟨I.σ, I.a.map (· + c)⟩

omit [NeZero L] in
/-- Port of `RBM2D/Loop/Cyclic.lean:523` at `c9a24cf` (`Cyclic_shift_WF`). -/
private theorem KLUnique_shift_WF {c : Zd d L} {I : LoopIdx (Zd d L)} (hI : I.WF) :
    (KLUnique_shift d L c I).WF := by
  simpa [LoopIdx.WF, KLUnique_shift] using hI

omit [NeZero L] in
/-- Port of `RBM2D/Loop/Cyclic.lean:528` at `c9a24cf` (`Cyclic_length_shift`). -/
private theorem KLUnique_length_shift (c : Zd d L) (I : LoopIdx (Zd d L)) :
    (KLUnique_shift d L c I).length = I.length := by
  simp [LoopIdx.length, KLUnique_shift]

omit [NeZero L] in
/-- Port of `RBM2D/Loop/Cyclic.lean:533` at `c9a24cf` (`Cyclic_cutGlueL_shift`). -/
private theorem KLUnique_cutGlueL_shift (c : Zd d L) (I : LoopIdx (Zd d L)) (k l : ℕ)
    (b : Zd d L) :
    (KLUnique_shift d L c I).cutGlueL k l b = KLUnique_shift d L c (I.cutGlueL k l (b - c)) := by
  simp [KLUnique_shift, LoopIdx.cutGlueL, List.map_take, List.map_drop]

omit [NeZero L] in
/-- Port of `RBM2D/Loop/Cyclic.lean:538` at `c9a24cf` (`Cyclic_cutGlueR_shift`). -/
private theorem KLUnique_cutGlueR_shift (c : Zd d L) (I : LoopIdx (Zd d L)) (k l : ℕ)
    (b : Zd d L) :
    (KLUnique_shift d L c I).cutGlueR k l b = KLUnique_shift d L c (I.cutGlueR k l (b - c)) := by
  simp [KLUnique_shift, LoopIdx.cutGlueR, List.map_take, List.map_drop]

/-- Port of `RBM2D/Loop/Cyclic.lean:542` at `c9a24cf` (`Cyclic_primRhs_shift`), over a kernel `S` with
`S (a + c) (b + c) = S a b`. -/
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

/-- Port of `RBM2D/Loop/Cyclic.lean:555` at `c9a24cf` (`Cyclic_primInit_shift`). -/
private theorem KLUnique_MLoop_shift (W : ℕ) (m : Bool → ℂ) (c : Zd d L) (I : LoopIdx (Zd d L)) :
    MLoop d L W m (KLUnique_shift d L c I) = MLoop d L W m I := by
  simp only [MLoop, KLUnique_length_shift]
  congr 2
  simp only [KLUnique_shift, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, add_left_inj]

/-- The translated family of an `IsKLoopS` family is an `IsKLoopS` family, for a translation-invariant kernel
`S` and translation-invariant initial data `M`: the inline block `hK'` of `Kcal_translate`
(`RBM2D/Loop/Cyclic.lean:607-616` at `c9a24cf`), stated for a general family, kernel and initial data. -/
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

/-- The translated family of a family of `K`-loops is a family of `K`-loops (`KLUnique_isKLoopS_shift` at
`S = SB d L g`, `M = MLoop`). -/
private theorem KLUnique_isKLoop_shift (W : ℕ) (g : ℝ) (m : Bool → ℂ) {T : Set ℝ}
    {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g m T K) (c : Zd d L) :
    IsKLoop d L W g m T (fun r J => K r (KLUnique_shift d L c J)) :=
  KLUnique_isKLoopS_shift d L W (SB d L g) (fun a b c => SB_apply_add_right d L g a b c) m
    (MLoop d L W m) (fun c I => KLUnique_MLoop_shift d L W m c I) hK c

end Translation

/-- **Translation invariance over a general kernel** (the pin `TranslS`).  For a translation-invariant kernel `S`
with `‖S a b‖ ≤ 1` and translation-invariant initial data `M`, shifting all block labels by `c : Z_L^d` leaves
every family `K` of `K`-loops on `[0,1)` unchanged: the shifted family is again a family of `K`-loops
(`KLUnique_isKLoopS_shift`), the `2`-loops of both are bounded (`retireS_holds`), so they agree by `uniqS_holds`;
the loops of length `1` are the third clause, of length `0` the empty loop. -/
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

/-- **Translation invariance of `𝒦`.**  Shifting all block labels by `c : Z_L^d` leaves `𝒦`
unchanged: `translS_holds` at `S = SB d L g` (`SB_apply_add_right`), `M = MLoop` (`KLUnique_MLoop_shift`) and the
family `𝒦` (`KLK_isKLoop`).  Port of `Kcal_translate` (`RBM2D/Loop/Cyclic.lean:594` at `c9a24cf`). -/
theorem KLK_translate :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
        KLK d L g W E t ⟨I.σ, I.a.map (· + c)⟩ = KLK d L g W E t I := by
  intro d L W _ g E hL hW hE t ht c I hI
  exact translS_holds d L W (SB d L g) (mSigma E) (MLoop d L W (mSigma E))
    (fun a b c => SB_apply_add_right d L g a b c) (norm_SB_apply_le g hL)
    (fun c I => KLUnique_MLoop_shift d L W (mSigma E) c I) (KLK_isKLoop d L W g E hL hW hE) t ht c I hI

/-! ## 4. Rotation: combinatorics of the cuts
(port of `RBM2D/Loop/Cyclic.lean:135-213` at `c9a24cf`) -/

/-- Move the first edge to the end.  Port of `RBM2D/Loop/Cyclic.lean:135` at `c9a24cf`
(`Cyclic_rot`). -/
private def KLUnique_rot {α : Type*} (x : LoopIdx α) : LoopIdx α := ⟨x.σ.rotate 1, x.a.rotate 1⟩

/-- Port of `RBM2D/Loop/Cyclic.lean:137` at `c9a24cf` (`Cyclic_rot_mk_cons`). -/
private theorem KLUnique_rot_mk_cons {α : Type*} (s : Bool) (ss : List Bool) (c : α)
    (cs : List α) :
    KLUnique_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α) = ⟨ss ++ [s], cs ++ [c]⟩ := by
  simp [KLUnique_rot, List.rotate_cons_succ]

/-- Port of `RBM2D/Loop/Cyclic.lean:142` at `c9a24cf` (`Cyclic_length_rot`). -/
private theorem KLUnique_length_rot {α : Type*} (x : LoopIdx α) :
    (KLUnique_rot x).length = x.length := by
  simp [KLUnique_rot, LoopIdx.length, List.length_rotate]

/-- Port of `RBM2D/Loop/Cyclic.lean:146` at `c9a24cf` (`Cyclic_WF_rot`). -/
private theorem KLUnique_WF_rot {α : Type*} {x : LoopIdx α} (hx : x.WF) :
    (KLUnique_rot x).WF := by
  simpa [LoopIdx.WF, KLUnique_rot, List.length_rotate] using hx

section RotCuts

variable {α : Type*} (s : Bool) (ss : List Bool) (c : α) (cs : List α) (b : α) {k l : ℕ}

/-- Port of `RBM2D/Loop/Cyclic.lean:153` at `c9a24cf` (`Cyclic_cutGlueL_rot_of_lt`). -/
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

/-- Port of `RBM2D/Loop/Cyclic.lean:169` at `c9a24cf` (`Cyclic_cutGlueR_rot_of_lt`). -/
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

/-- Port of `RBM2D/Loop/Cyclic.lean:182` at `c9a24cf` (`Cyclic_cutGlueL_rot_last`). -/
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

/-- Port of `RBM2D/Loop/Cyclic.lean:197` at `c9a24cf` (`Cyclic_cutGlueR_rot_last`). -/
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

/-! ## 5. Rotation: the equation at a rotated loop
(port of `RBM2D/Loop/Cyclic.lean:217-510` at `c9a24cf`) -/

section RotEq

variable (d L : ℕ) [NeZero L] (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ)

/-- Port of `RBM2D/Loop/Cyclic.lean:221` at `c9a24cf` (`Cyclic_primRhs_split`). -/
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

/-- `(pro_dyncalK)`'s right-hand side at the rotated loop of `(s :: ss, c :: cs)`, in terms of
the cuts of the original loop.  Port of `RBM2D/Loop/Cyclic.lean:236` at `c9a24cf`
(`Cyclic_primRhs_rot`). -/
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

/-- The initial value of `Def_Ktza` is invariant under rotation.  Port of
`RBM2D/Loop/Cyclic.lean:319` at `c9a24cf` (`Cyclic_primInit_rot`). -/
private theorem KLUnique_MLoop_rot (m : Bool → ℂ) (I : LoopIdx (Zd d L)) :
    MLoop d L W m (KLUnique_rot I) = MLoop d L W m I := by
  simp only [MLoop, KLUnique_length_rot]
  congr 2
  · simp only [KLUnique_rot, List.map_rotate]
    exact (List.rotate_perm _ 1).prod_eq
  · simp only [KLUnique_rot, List.mem_rotate]

/-- One level of the induction for rotation: at length `n`, `K ∘ rot - K` solves a linear
inequality `‖D'‖ ≤ C ‖D‖` (Grönwall), the `2`-loops being bounded by `R`.  Port of
`RBM2D/Loop/Cyclic.lean:328` at `c9a24cf` (`Cyclic_rot_eq_on_level`). -/
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
/-- Rotation invariance of the initial data, from the hypothesis in the form of the pin `RotS`: for a
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

/-- Cyclic invariance of an `IsKLoopS` family with bounded `2`-loops, at lengths `≥ 2`, for a symmetric kernel
with `‖S a b‖ ≤ 1` and rotation-invariant initial data `M`.  Port of `RBM2D/Loop/Cyclic.lean:487` at `c9a24cf`
(`Cyclic_isPrimitive_rot`). -/
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

/-- **Cyclic invariance over a general kernel** (the pin `RotS`).  Every family of `K`-loops on `[0,1)` over a
symmetric kernel `S` with `‖S a b‖ ≤ 1` and rotation-invariant initial data `M` is invariant under moving the
first edge to the end.  The length-`1` case is a syntactic equality; for length `≥ 2` see
`KLUnique_isKLoopS_rot` with the `2`-loop bound from continuity on `[0, t] ⊆ [0, 1)` (`retireS_holds`). -/
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

/-- **Cyclic invariance of `𝒦`.**  `𝒦` is invariant under moving the first edge to the end:
`rotS_holds` at `S = SB d L g` (`SB_transpose`, `norm_SB_apply_le`), `M = MLoop` (`KLUnique_MLoop_rot`) and the
family `𝒦` (`KLK_isKLoop`).  Port of `Kcal_rotate` (`RBM2D/Loop/Cyclic.lean:569` at `c9a24cf`). -/
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

/-! ## 6. The compiled instances: `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`

`L = 5` (`125` blocks), `W = 2` (`W^d = 8`), `m(+) = i`.  Every deterministic hypothesis of
`KLK_unique`, `KLK_rotate`, `KLK_translate` (`3 ≤ 5`, `1 ≤ 2`, `|0| < 2`, `t = 9/10 ∈ [0,1)`,
well-formedness, `1 ≤ length`) is discharged; the family hypothesis of `KLK_unique` is the merged
instance `KLTreeDerivInst_isKLoop` of `KLK_isKLoop` (`K = 𝒦`, the trivial case) or its shift by
`KLUnique_isKLoop_shift` (a family of `K`-loops different from `𝒦` as a function).  The loops have
length `1` (`KLK_unique`: third clause of `IsKLoop`), `2` and `3` (`KLK_unique`: through
`isKLoop_unique`), `3` (`KLK_unique` with the shifted family `𝒦(r, shift_{e₁} J)`), `3` and `4`
(`KLK_rotate`), `3` (`KLK_translate`, by `e₁`).  The merged theorems `kTwoFormula_of_isKLoop`,
`kThree_eq_of_isKLoop`, `pureLoop_two_of_isKLoop`, `pureLoop_three`, which no longer take the a
priori bound of the `2`-loops as a premise (it is `KLretire_twoLoopBounded`), are applied to the
family `K = 𝒦` (`‖m(±)‖ = 1` by `norm_mSigma`, `Im m(+) > 0` by `mE_im_pos`, `ThetaDecayShort` by
the proved `thetaDecayShort_holds`): `KTwoFormula` and `𝒦^{(3)} = kThree` at `t = 9/10` hold of
`𝒦` with no bound assumed, and the pure `2`- and `3`-loops of `𝒦` decay. -/

section Instances

/-- `KLK_unique` at a loop of length `1`: `K^{(1)}_{t,+,0} = m(+)` (third clause of `IsKLoop`). -/
theorem KLUniqueInst_unique_one :
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) (9 / 10) ⟨[true], [0]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ :=
  KLK_unique 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop (9 / 10)
    ⟨by norm_num, by norm_num⟩ _ rfl (by simp [LoopIdx.length])

/-- `KLK_unique` at a loop of length `2`: charges `(+,-)`, labels `(0, 1)`. -/
theorem KLUniqueInst_unique_two :
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) (9 / 10) ⟨[true, false], [0, 1]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, 1]⟩ :=
  KLK_unique 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop (9 / 10)
    ⟨by norm_num, by norm_num⟩ _ rfl (by simp [LoopIdx.length])

/-- `KLK_unique` at a loop of length `3`: charges `(+,-,+)`, labels `(0, 1, 2)`. -/
theorem KLUniqueInst_unique_three :
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩ :=
  KLK_unique 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop (9 / 10)
    ⟨by norm_num, by norm_num⟩ _ rfl (by simp [LoopIdx.length])

/-- `KLK_unique` for a family that is not syntactically `𝒦`: `K_c(r, J) = 𝒦(r, shift_c J)`, the
shift by `e₁ = (1,0,0)` of the labels, is a family of `K`-loops (the merged instance
`KLTreeDerivInst_isKLoop` through `KLUnique_isKLoop_shift`), so `K_c = 𝒦`; here at `t = 9/10` and the
loop with charges `(+,-,+)` and labels `(0,0,0), (1,2,3), (4,0,1)`. -/
theorem KLUniqueInst_unique_shifted :
    (fun r (J : LoopIdx (Zd 3 5)) =>
        KLK 3 5 (1 / 2) 2 0 r ⟨J.σ, J.a.map (· + (![1, 0, 0] : Zd 3 5))⟩) (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ :=
  KLK_unique 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (fun r (J : LoopIdx (Zd 3 5)) =>
      KLK 3 5 (1 / 2) 2 0 r ⟨J.σ, J.a.map (· + (![1, 0, 0] : Zd 3 5))⟩)
    (KLUnique_isKLoop_shift 3 5 2 (1 / 2) (mSigma 0) KLTreeDerivInst_isKLoop (![1, 0, 0] : Zd 3 5))
    (9 / 10) ⟨by norm_num, by norm_num⟩
    ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ rfl
    (by simp [LoopIdx.length])

/-- `KLK_rotate` at `n = 3`: charges `(+,-,+)`, labels `(0, 1, 2)`. -/
theorem KLUniqueInst_rotate_three :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false, true], (0 : Zd 3 5) :: [1, 2]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false, true] ++ [true], [1, 2] ++ [(0 : Zd 3 5)]⟩ :=
  KLK_rotate 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    ⟨by norm_num, by norm_num⟩ true 0 [false, true] [1, 2] rfl

/-- `KLK_rotate` at `n = 4`: charges `(+,-,+,-)`, labels `(0, 1, 2, 3)`. -/
theorem KLUniqueInst_rotate_four :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false, true, false], (0 : Zd 3 5) :: [1, 2, 3]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨[false, true, false] ++ [true], [1, 2, 3] ++ [(0 : Zd 3 5)]⟩ :=
  KLK_rotate 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    ⟨by norm_num, by norm_num⟩ true 0 [false, true, false] [1, 2, 3] rfl

/-- `KLK_translate` at `n = 3`: translation by `e₁ = (1,0,0) ∈ Z_5^3` of the loop with charges
`(+,-,+)` and labels `(0,0,0), (1,2,3), (4,0,1)`. -/
theorem KLUniqueInst_translate_three :
    KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true],
          ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5)).map (· + (![1, 0, 0] : Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ :=
  KLK_translate 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    ⟨by norm_num, by norm_num⟩ (![1, 0, 0] : Zd 3 5)
    ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ rfl

/-- `KLretire_twoLoopBounded` at the instance data: the a priori bound of the `2`-loops of `𝒦` on
every `[0,T₀]`, `T₀ < 1`, is a theorem, not an assumption. -/
theorem KLUniqueInst_retire_twoLoopBounded :
    ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ∀ I : LoopIdx (Zd 3 5), I.WF → I.length = 2 → ‖KLK 3 5 (1 / 2) 2 0 t I‖ ≤ R :=
  KLretire_twoLoopBounded (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop

/-- `kTwoFormula_of_isKLoop` at the instance data: `(Kn2sol)` for `𝒦`, with `‖m(±)‖ = 1` and no
bound on the `2`-loops assumed. -/
theorem KLUniqueInst_kTwoFormula :
    KTwoFormula 3 5 2 (1 / 2) (mSigma 0) (fun t I => KLK 3 5 (1 / 2) 2 0 t I) :=
  kTwoFormula_of_isKLoop (by norm_num) (by norm_num) (fun s => norm_mSigma (by norm_num) s)
    KLTreeDerivInst_isKLoop

/-- `kThree_eq_of_isKLoop` at the instance data, at `t = 9/10`: `𝒦^{(3)}` at charges `(+,-,+)` and
labels `(0, 1, 2)` is `kThree`. -/
theorem KLUniqueInst_kThree :
    (fun t I => KLK 3 5 (1 / 2) 2 0 t I) (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩
      = kThree 3 5 2 (1 / 2) (mSigma 0) (9 / 10) true false true 0 1 2 :=
  kThree_eq_of_isKLoop (by norm_num) (by norm_num) (fun s => norm_mSigma (by norm_num) s)
    KLTreeDerivInst_isKLoop (9 / 10) (by norm_num) (by norm_num) true false true 0 1 2

/-- `Im m(+) > 0` at `E = 0` (`m(+) = i`). -/
private theorem KLUnique_inst_im : 0 < (mSigma 0 true).im := by
  simpa [mSigma] using mE_im_pos (E := 0) (by norm_num)

/-- `pureLoop_two_of_isKLoop` at `d = k + 2 = 3` (`k = 1`), `L = 5`, `W = 2`, `g = 1/2`, `E = 0`,
`σ = +`: the pure `2`-loops of `𝒦` decay exponentially in the distance of their labels.
`ThetaDecayShort` is the proved `thetaDecayShort_holds`. -/
theorem KLUniqueInst_pureLoop_two :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (1 + 2) 5,
      ‖KLK 3 5 (1 / 2) 2 0 t ⟨[true, true], [a₁, a₂]⟩‖
        ≤ C * ‖(((2 : ℕ) : ℂ) ^ (1 + 2))⁻¹‖
          * Real.exp (-(c * (zdistD (1 + 2) 5 (a₁ - a₂) : ℝ))) :=
  pureLoop_two_of_isKLoop (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s => norm_mSigma (by norm_num) s)
    KLUnique_inst_im (thetaDecayShort_holds (1 + 2) (1 / 2) (mSigma 0 true))
    (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop

/-- `pureLoop_three` at the same data: the pure `3`-loops of `𝒦` decay exponentially in the diameter
of their labels. -/
theorem KLUniqueInst_pureLoop_three :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 →
      ∀ (a : Fin 3 → Zd (1 + 2) 5) (p q : Fin 3),
        ‖KLK 3 5 (1 / 2) 2 0 t ⟨[true, true, true], [a 0, a 1, a 2]⟩‖
          ≤ C * ‖((((2 : ℕ) : ℂ) ^ (1 + 2))⁻¹) ^ 2‖
            * Real.exp (-(c * (zdistD (1 + 2) 5 (a p - a q) : ℝ))) :=
  pureLoop_three (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s => norm_mSigma (by norm_num) s)
    KLUnique_inst_im (thetaDecayShort_holds (1 + 2) (1 / 2) (mSigma 0 true))
    (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop

/-- The hypotheses on `S` of `RotS` and `TranslS` hold at the block Anderson kernel `S = 1`
(`S^{(B)}(0) = I`, `kernelFacts_one` of the probe `t/T2360`): symmetry, `‖S a b‖ ≤ 1`, translation
invariance.  Nothing is assumed of `d`, `L` beyond `NeZero L`. -/
theorem kernel_one_rot_transl {d L : ℕ} [NeZero L] :
    (∀ a b : Zd d L, (1 : Matrix (Zd d L) (Zd d L) ℂ) a b = (1 : Matrix (Zd d L) (Zd d L) ℂ) b a) ∧
    (∀ a b : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a b‖ ≤ 1) ∧
    (∀ a b c : Zd d L, (1 : Matrix (Zd d L) (Zd d L) ℂ) (a + c) (b + c)
      = (1 : Matrix (Zd d L) (Zd d L) ℂ) a b) :=
  ⟨fun a b => by simp only [Matrix.one_apply]; exact if_congr eq_comm rfl rfl,
    fun a b => by simp only [Matrix.one_apply]; split_ifs <;> simp,
    fun a b c => by simp only [Matrix.one_apply, add_left_inj]⟩

/-- The hypotheses on `S` of `RotS` and `TranslS` hold at the band kernel `S = SB d L g` for `3 ≤ L`. -/
theorem kernel_SB_rot_transl {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) :
    (∀ a b : Zd d L, SB d L g a b = SB d L g b a) ∧ (∀ a b : Zd d L, ‖SB d L g a b‖ ≤ 1) ∧
    (∀ a b c : Zd d L, SB d L g (a + c) (b + c) = SB d L g a b) :=
  ⟨fun a b => (show SB d L g b a = SB d L g a b from
      congrFun (congrFun (SB_transpose d L g) a) b).symm,
    norm_SB_apply_le g hL, fun a b c => SB_apply_add_right d L g a b c⟩

/-- `uniqS_holds` at the instance data (`S = SB 3 5 (1/2)`, `M = MLoop`) for two different families of
`K`-loops, `K = 𝒦 ∘ shift_{e₁}` and `K' = 𝒦`, with the `2`-loop bounds of `retireS_holds`; the loop has
charges `(+,-,+)` and labels `(0,0,0), (1,2,3), (4,0,1)`, `t = 9/10`. -/
theorem KLUniqueInst_uniqS_shifted :
    (fun r (J : LoopIdx (Zd 3 5)) =>
        KLK 3 5 (1 / 2) 2 0 r ⟨J.σ, J.a.map (· + (![1, 0, 0] : Zd 3 5))⟩) (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ := by
  have hK : IsKLoopS 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0)) (Set.Ico 0 1)
      (fun t I => KLK 3 5 (1 / 2) 2 0 t I) := KLTreeDerivInst_isKLoop
  have hKc := KLUnique_isKLoopS_shift 3 5 2 (SB 3 5 (1 / 2)) (kernel_SB_rot_transl (1 / 2) (by norm_num)).2.2
    (mSigma 0) (MLoop 3 5 2 (mSigma 0)) (fun c I => KLUnique_MLoop_shift 3 5 2 (mSigma 0) c I) hK
    (![1, 0, 0] : Zd 3 5)
  obtain ⟨R, hR0, hR⟩ := retireS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0)) hK
    (9 / 10) (by norm_num)
  obtain ⟨R', hR'0, hR'⟩ := retireS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0)) hKc
    (9 / 10) (by norm_num)
  exact uniqS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
    (kernel_SB_rot_transl (1 / 2) (by norm_num)).2.1 hKc hK (T₀ := 9 / 10) (R := max R R')
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩) (le_trans hR0 (le_max_left _ _))
    (fun r hr J hJ hJ2 => ⟨(hR' r hr J hJ hJ2).trans (le_max_right _ _),
      (hR r hr J hJ hJ2).trans (le_max_left _ _)⟩) (9 / 10) ⟨by norm_num, by norm_num⟩ _ rfl
    (by simp [LoopIdx.length])

/-- `rotS_holds` at the instance data (`S = SB 3 5 (1/2)`, `M = MLoop`, `K = 𝒦`): `n = 3`, charges
`(+,-,+)`, labels `(0, 1, 2)`, `t = 9/10`.  The hypotheses on `S` are `kernel_SB_rot_transl`, the one on `M` is
`KLUnique_MLoop_rot_cons`. -/
theorem KLUniqueInst_rotS :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false, true], (0 : Zd 3 5) :: [1, 2]⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false, true] ++ [true], [1, 2] ++ [(0 : Zd 3 5)]⟩ :=
  rotS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
    (kernel_SB_rot_transl (1 / 2) (by norm_num)).1 (kernel_SB_rot_transl (1 / 2) (by norm_num)).2.1
    (KLUnique_MLoop_rot_cons 3 5 2 (mSigma 0)) (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I)
    KLTreeDerivInst_isKLoop (9 / 10) ⟨by norm_num, by norm_num⟩ true 0 [false, true] [1, 2] rfl

/-- `translS_holds` at the same data: translation by `e₁ = (1,0,0)` of the loop with charges `(+,-,+)` and labels
`(0,0,0), (1,2,3), (4,0,1)`, `t = 9/10`.  The hypothesis on `M` is `KLUnique_MLoop_shift`. -/
theorem KLUniqueInst_translS :
    KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true],
          ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5)).map (· + (![1, 0, 0] : Zd 3 5))⟩
      = KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ :=
  translS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
    (kernel_SB_rot_transl (1 / 2) (by norm_num)).2.2 (kernel_SB_rot_transl (1 / 2) (by norm_num)).2.1
    (fun c I => KLUnique_MLoop_shift 3 5 2 (mSigma 0) c I) (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I)
    KLTreeDerivInst_isKLoop (9 / 10) ⟨by norm_num, by norm_num⟩ (![1, 0, 0] : Zd 3 5)
    ⟨[true, false, true], ([![0, 0, 0], ![1, 2, 3], ![4, 0, 1]] : List (Zd 3 5))⟩ rfl

end Instances

end RBM.Loop
