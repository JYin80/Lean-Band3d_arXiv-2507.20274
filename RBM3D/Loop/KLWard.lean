/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLUnique
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The `K`-loop layer, sixth row (KL6): Ward's identity `lem_WI_K`, `(WI_calK)`, `d ≥ 3`

Ticket T2036 (design ticket T2004, row KL6).  Names are in `RBM.Loop`; every helper is `private`
and carries the file stem `KLWard_` (one public helper, `KLWard_flip`; the instances are
`KLWardInst_*`).

* **`RBM.Loop.KLK_ward`** is the pin `KLwardPin` (`64b58eb:RBM3D/Probe/T2004Pins.lean:770-779`,
  `docs/tickets/checks/T2036-check.lean`), proved: for every `n ≥ 2` and both charge orders
  `σ = (s, μ, -s)`,
  `∑_{a_n} 𝒦^{(n)}_{t,σ,a} = (2 i W^d η_t)⁻¹ (𝒦^{(n-1)}_{t,(+,μ),â} - 𝒦^{(n-1)}_{t,(-,μ),â})`,
  `η_t = (1 - t) Im m(E)`, for `𝒦 = KLK` (the tree sum of KL1).  No hypothesis is added: `3 ≤ d` is
  not used, and no unproved `Prop` enters.
* **`s = +`** (`KLWard_pos`): port of `Kcal_ward`.  The defect
  `D_t(μ, a') = ∑_x 𝒦_{t,(+,μ,-),(a',x)} - κ_t (𝒦_{t,(+,μ),a'} - 𝒦_{t,(-,μ),a'})`,
  `κ_t = (2 i W^d η_t)⁻¹`, solves `∂_t D = W^d T[D] + (1 - t)⁻¹ D`, where `T` is linear in the
  defects of the same length `N` (`KLWard_rhs_identity`: the adjacent cuts `(k, k+1)` and the last
  cut `(N, N+1)` of the loop carrying the summed label; the other factor is a `2`-loop, bounded by
  `R`), and `D_0 = 0` (`KLWard_wD_MLoop`), so `D ≡ 0` by Grönwall (`KLWard_level`), by strong
  induction on the length (`KLWard_of_isKLoop`).  Length `2` is `KLward_two` (KL1); the cyclic
  invariance used at the last cut is `KLK_rotate` (KL5); the bound on the `2`-loops on
  `[0,t] ⊆ [0,1)` is `KLretire_twoLoopBounded` (KL4, continuity); the equations are `KLK_isKLoop`
  (KL3).
* **`s = -`**: `KLK_rotate` does not give it (a rotation permutes positions and never flips a
  charge), and the induction is not redone.  The new lemma **`KLWard_flip`**,
  `𝒦_{t,-σ,a} = conj 𝒦_{t,σ,a}`, is proved by uniqueness (`KLK_unique`): the family
  `(t, I) ↦ conj 𝒦_{t, flip I}` is again a family of `K`-loops (`S^(B)` is real,
  `m(-s) = conj m(s)`, and `flip` commutes with the cuts), hence equals `𝒦`.  With
  `conj κ_t = -κ_t` this gives the case `s = -` from `s = +`.

## Sources and changes

Port of RBM2D at commit `c9a24cf` (read-only), `RBM2D/Loop/Ward.lean`: index bookkeeping
`Ward_rot … Ward_cutGlueR_pmLoop_one` 37-167, derivative identity `Ward_wStar … Ward_rhs_identity`
169-556, `κ_t`, `c_t`, initial value `Ward_kappa … Ward_wD_primInit` 558-690, Grönwall and
induction `Ward_cutMu_adjacent … Ward_of_isPrimitive` 692-922, and the proof of `Kcal_ward`
969-1000.

Changes (a mechanical renaming, then the hand edits listed here):
* `Z2 L ↦ Zd d L`, `SB L ↦ SB d L g`, `primRhs L W ↦ treeEqRhs d L W g`,
  `primInit L W (mSig E) ↦ MLoop d L W (mSigma E)`, `IsPrimitive L W (mSig E) ↦
  IsKLoop d L W g (mSigma E)`, `mSig ↦ mSigma`, `etaT ↦ Gauss.etaT`, `Gauss.spectralM ↦ mE`,
  `Gauss.spectralM_im_pos ↦ mE_im_pos`, `Gauss.norm_spectralM ↦ norm_mE`.
* `W^2 ↦ W^d` (`κ_t`, `c_t`, the Grönwall constant, `KLWard_sum_treeEqRhs_fullLoop`,
  `KLWard_rhs_identity`, `KLWard_level`); no other dimension-specific fact enters (the Grönwall
  constant is a finite sum over `Zd d L`).
* `LoopIdx.WF.cutGlueL/R ↦ LoopIdx.wf_cutGlueL/R` (the names of the merged
  `RBM3D/Loop/TreeRep.lean`); the section variables `d`, `g` are added.
* `Ward_etaT_eq` is `rfl` here, because `Gauss.etaT E t` is defined as `(1 - t) * (mE E).im`.
* `Ward_two_loop_bound` and its `LoopVec` helpers are not ported: `KLretire_twoLoopBounded`
  replaces them.  The level-`2` identity `WI_calK_two`, `Kcal_rotate`, `isPrimitive_Kcal` are
  `KLward_two`, `KLK_rotate`, `KLK_isKLoop`.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. Index bookkeeping (port of `RBM2D/Loop/Ward.lean:37-167` at `c9a24cf`) -/

section Ind

variable {α : Type*}

/-- Move the first edge to the end. -/
private def KLWard_rot (x : LoopIdx α) : LoopIdx α := ⟨x.σ.rotate 1, x.a.rotate 1⟩

private theorem KLWard_rot_mk_cons (s : Bool) (ss : List Bool) (c : α) (cs : List α) :
    KLWard_rot (⟨s :: ss, c :: cs⟩ : LoopIdx α) = ⟨ss ++ [s], cs ++ [c]⟩ := by
  simp [KLWard_rot, List.rotate_cons_succ]

private theorem KLWard_two_le_length_cutGlueL (x : LoopIdx α) (a : α) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) : 2 ≤ (x.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL x a hk hkl hl]
  omega

/-- `(+, μ, -; a', x)`: a loop with first charge `+` and last charge `-`. -/
private def KLWard_fullLoop (μ : List Bool) (a' : List α) (x : α) : LoopIdx α :=
  ⟨true :: μ ++ [false], a' ++ [x]⟩

/-- `(s, μ; a')`: the loops `σ±` on the right-hand side of `(WI_calK)`. -/
private def KLWard_pmLoop (s : Bool) (μ : List Bool) (a' : List α) : LoopIdx α := ⟨s :: μ, a'⟩

/-- The middle charges after cutting at `(k, l)`. -/
private def KLWard_cutMu (k l : ℕ) (μ : List Bool) : List Bool := μ.take (k - 1) ++ μ.drop (l - 2)

/-- The labels (without the last) after cutting at `(k, l)` and gluing with `b`. -/
private def KLWard_cutA (k l : ℕ) (b : α) (a' : List α) : List α :=
  a'.take (k - 1) ++ b :: a'.drop (l - 1)

variable (μ : List Bool) (a' : List α) (x b : α) {k l : ℕ}

private theorem KLWard_cutGlueL_fullLoop (hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) :
    (KLWard_fullLoop μ a' x).cutGlueL k l b
      = KLWard_fullLoop (KLWard_cutMu k l μ) (KLWard_cutA k l b a') x := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
  simp only [KLWard_fullLoop, LoopIdx.cutGlueL, KLWard_cutMu, KLWard_cutA, Nat.add_sub_cancel,
    List.take_succ_cons, show l + 2 - 1 = l + 1 by omega, show l + 2 - 2 = l by omega,
    List.drop_succ_cons, List.cons_append, List.append_assoc]
  congr 1
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]

private theorem KLWard_cutGlueL_pmLoop (s : Bool) (_hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) :
    (KLWard_pmLoop s μ a').cutGlueL k l b
      = KLWard_pmLoop s (KLWard_cutMu k l μ) (KLWard_cutA k l b a') := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
  simp only [KLWard_pmLoop, LoopIdx.cutGlueL, KLWard_cutMu, KLWard_cutA, Nat.add_sub_cancel,
    List.take_succ_cons, show l + 2 - 1 = l + 1 by omega, show l + 2 - 2 = l by omega,
    List.drop_succ_cons, List.cons_append]

private theorem KLWard_cutGlueR_fullLoop (s : Bool) (hμ : μ.length + 1 = a'.length)
    (hk : 2 ≤ k) (hkl : k < l) (hl : l ≤ a'.length) :
    (KLWard_fullLoop μ a' x).cutGlueR k l b = (KLWard_pmLoop s μ a').cutGlueR k l b := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [KLWard_fullLoop, KLWard_pmLoop, LoopIdx.cutGlueR, show k + 2 - 1 = k + 1 by omega,
    List.drop_succ_cons, List.cons_append]
  congr 1
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

private theorem KLWard_cutGlueR_fullLoop_one (hμ : μ.length + 1 = a'.length) (hl1 : 1 < l)
    (hl : l ≤ a'.length) :
    (KLWard_fullLoop μ a' x).cutGlueR 1 l b = (KLWard_pmLoop true μ a').cutGlueR 1 l b := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp only [KLWard_fullLoop, KLWard_pmLoop, LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero,
    Nat.add_sub_cancel, List.take_succ_cons, List.cons_append]
  congr 1
  · rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (by omega)]

private theorem KLWard_cutGlueL_fullLoop_last (hμ : μ.length + 1 = a'.length) (hk : 1 ≤ k)
    (hkn : k ≤ a'.length) :
    (KLWard_fullLoop μ a' x).cutGlueL k (a'.length + 1) b
      = KLWard_fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [b]) x := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [KLWard_fullLoop, LoopIdx.cutGlueL, Nat.add_sub_cancel, List.take_succ_cons,
    List.cons_append]
  congr 1
  · rw [List.take_append_of_le_length (by omega), ← hμ, List.drop_succ_cons, List.drop_left]
  · rw [List.take_append_of_le_length (by omega), List.drop_left]
    simp

private theorem KLWard_cutGlueR_fullLoop_last_one (hμ : μ.length + 1 = a'.length) :
    (KLWard_fullLoop μ a' x).cutGlueR 1 (a'.length + 1) b = KLWard_fullLoop μ a' b := by
  simp only [KLWard_fullLoop, LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel]
  congr 1
  · rw [List.take_of_length_le (by simp; omega)]
  · rw [List.take_append_of_le_length le_rfl, List.take_length]

/-- The right chain of the cut `(k, n)`, `k ≥ 2`, is the rotation of the left chain of
`pmLoop -` at `(1, k)`. -/
private theorem KLWard_cutGlueR_fullLoop_last (hμ : μ.length + 1 = a'.length) (hk : 2 ≤ k)
    (hkn : k ≤ a'.length) :
    (KLWard_fullLoop μ a' x).cutGlueR k (a'.length + 1) b
      = KLWard_rot ((KLWard_pmLoop false μ a').cutGlueL 1 k b) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [KLWard_fullLoop, KLWard_pmLoop, LoopIdx.cutGlueR, LoopIdx.cutGlueL,
    show k + 2 - 1 = k + 1 by omega, List.drop_succ_cons, List.cons_append, Nat.sub_self,
    List.take_zero, List.nil_append, List.take_succ_cons, List.take_zero]
  rw [KLWard_rot_mk_cons]
  congr 1
  · rw [List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega)]
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]

/-- The right chain never contains the last label `x`. -/
private theorem KLWard_cutGlueR_fullLoop_indep (y : α) (hk : 1 ≤ k) (hkl : k < l)
    (hl : l ≤ a'.length + 1) :
    (KLWard_fullLoop μ a' x).cutGlueR k l b = (KLWard_fullLoop μ a' y).cutGlueR k l b := by
  simp only [KLWard_fullLoop, LoopIdx.cutGlueR]
  congr 1
  rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega)]

/-- The right chain of `pmLoop s` at `(1, m)` is `pmLoop s` of the base of the left chain of
`fullLoop` at `(m, n)`. -/
private theorem KLWard_cutGlueR_pmLoop_one (s : Bool) (hm : 1 < l) :
    (KLWard_pmLoop s μ a').cutGlueR 1 l b
      = KLWard_pmLoop s (μ.take (l - 1)) (a'.take (l - 1) ++ [b]) := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp only [KLWard_pmLoop, LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel,
    List.take_succ_cons]

end Ind

/-! ## 2. The derivative identity (port of `RBM2D/Loop/Ward.lean:169-556` at `c9a24cf`) -/

section Step

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- `∑_x K_{(+,μ,-),(a',x)}`: the left-hand side of `(WI_calK)`. -/
private noncomputable def KLWard_wStar (K : LoopIdx (Zd d L) → ℂ) (μ : List Bool)
    (a' : List (Zd d L)) : ℂ :=
  ∑ x : Zd d L, K (KLWard_fullLoop μ a' x)

/-- The difference of the two sides of `(WI_calK)`, with `κ = (2 i W^d η_t)⁻¹`. -/
private noncomputable def KLWard_wD (K : LoopIdx (Zd d L) → ℂ) (κ : ℂ) (μ : List Bool)
    (a' : List (Zd d L)) : ℂ :=
  KLWard_wStar d L K μ a' - κ * (K (KLWard_pmLoop true μ a') - K (KLWard_pmLoop false μ a'))

/-- The `x`-summed right-hand side of `(pro_dyncalK)` at `fullLoop μ a' x`, split into the
cuts with `l ≤ N` and the cuts `(k, N + 1)`. -/
private theorem KLWard_sum_treeEqRhs_fullLoop (W : ℕ) (K : LoopIdx (Zd d L) → ℂ) (μ : List Bool)
    (a' : List (Zd d L)) :
    ∑ x : Zd d L, treeEqRhs d L W g K (KLWard_fullLoop μ a' x) = (W : ℂ) ^ d *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : Zd d L, ∑ b : Zd d L,
          (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k l a)) * SB d L g a b *
            K ((KLWard_fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : Zd d L, ∑ b : Zd d L,
          (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k (a'.length + 1) a)) * SB d L g a b *
            K ((KLWard_fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
  have hlen : ∀ x : Zd d L, (KLWard_fullLoop μ a' x).length = a'.length + 1 := fun x => by
    simp [KLWard_fullLoop, LoopIdx.length]
  have hR : ∀ x : Zd d L, ∀ k l, 1 ≤ k → k < l → l ≤ a'.length + 1 → ∀ b : Zd d L,
      (KLWard_fullLoop μ a' x).cutGlueR k l b = (KLWard_fullLoop μ a' 0).cutGlueR k l b :=
    fun x k l hk hkl hl b => KLWard_cutGlueR_fullLoop_indep μ a' x b 0 hk hkl hl
  have hsplit : ∀ x : Zd d L, treeEqRhs d L W g K (KLWard_fullLoop μ a' x) = (W : ℂ) ^ d *
      (∑ k ∈ Icc 1 a'.length, ∑ l ∈ Ioc k a'.length, ∑ a : Zd d L, ∑ b : Zd d L,
          K ((KLWard_fullLoop μ a' x).cutGlueL k l a) * SB d L g a b *
            K ((KLWard_fullLoop μ a' 0).cutGlueR k l b)
        + ∑ k ∈ Icc 1 a'.length, ∑ a : Zd d L, ∑ b : Zd d L,
          K ((KLWard_fullLoop μ a' x).cutGlueL k (a'.length + 1) a) * SB d L g a b *
            K ((KLWard_fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)) := by
    intro x
    rw [treeEqRhs, hlen, sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero,
      ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    rw [sum_Ioc_succ_top hk.2]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_Ioc] at hl
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k l hk.1 hl.1 (by omega) b]
    · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hR x k (a'.length + 1) hk.1 (by omega) le_rfl b]
  simp only [hsplit, ← Finset.mul_sum, sum_add_distrib]
  congr 2
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]

section Cuts

variable (K : LoopIdx (Zd d L) → ℂ) (κ : ℂ) (μ : List Bool) (a' : List (Zd d L))

private theorem KLWard_wStar_eq (μ' : List Bool) (a'' : List (Zd d L)) :
    KLWard_wStar d L K μ' a'' = KLWard_wD d L K κ μ' a''
      + κ * (K (KLWard_pmLoop true μ' a'') - K (KLWard_pmLoop false μ' a'')) := by
  rw [KLWard_wD]
  ring

/-- **W1**: a cut `(k, l)` with `l ≤ N`. -/
private theorem KLWard_cut_inner (hμ : μ.length + 1 = a'.length) {k l : ℕ} (hk : 1 ≤ k)
    (hkl : k < l) (hl : l ≤ a'.length) (a b : Zd d L) :
    (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k l a)) * SB d L g a b *
        K ((KLWard_fullLoop μ a' 0).cutGlueR k l b)
      - κ * (K ((KLWard_pmLoop true μ a').cutGlueL k l a) * SB d L g a b *
            K ((KLWard_pmLoop true μ a').cutGlueR k l b)
          - K ((KLWard_pmLoop false μ a').cutGlueL k l a) * SB d L g a b *
            K ((KLWard_pmLoop false μ a').cutGlueR k l b))
      = KLWard_wD d L K κ (KLWard_cutMu k l μ) (KLWard_cutA k l a a') * SB d L g a b *
          K ((KLWard_pmLoop true μ a').cutGlueR k l b)
        + κ * K ((KLWard_pmLoop false μ a').cutGlueL k l a) * SB d L g a b *
          (K ((KLWard_pmLoop false μ a').cutGlueR k l b)
            - K ((KLWard_pmLoop true μ a').cutGlueR k l b)) := by
  have hL : ∀ x, (KLWard_fullLoop μ a' x).cutGlueL k l a
      = KLWard_fullLoop (KLWard_cutMu k l μ) (KLWard_cutA k l a a') x :=
    fun x => KLWard_cutGlueL_fullLoop μ a' x a hμ hk hkl hl
  have hR : (KLWard_fullLoop μ a' 0).cutGlueR k l b = (KLWard_pmLoop true μ a').cutGlueR k l b := by
    rcases hk.lt_or_eq with hk2 | rfl
    · exact KLWard_cutGlueR_fullLoop μ a' 0 b true hμ hk2 hkl hl
    · exact KLWard_cutGlueR_fullLoop_one μ a' 0 b hμ hkl hl
  simp only [hL, hR, KLWard_cutGlueL_pmLoop μ a' a true hμ hk hkl hl,
    KLWard_cutGlueL_pmLoop μ a' a false hμ hk hkl hl]
  rw [show ∑ x : Zd d L, K (KLWard_fullLoop (KLWard_cutMu k l μ) (KLWard_cutA k l a a') x)
      = KLWard_wStar d L K (KLWard_cutMu k l μ) (KLWard_cutA k l a a') from rfl, KLWard_wStar_eq d L K κ]
  ring

omit [NeZero L] in
/-- For `k ≥ 2` the remainder of W1 vanishes: the right chain does not see the first
charge. -/
private theorem KLWard_cutGlueR_pmLoop_indep (hμ : μ.length + 1 = a'.length) {k l : ℕ}
    (hk : 2 ≤ k) (hkl : k < l) (hl : l ≤ a'.length) (b : Zd d L) :
    (KLWard_pmLoop false μ a').cutGlueR k l b = (KLWard_pmLoop true μ a').cutGlueR k l b := by
  rw [← KLWard_cutGlueR_fullLoop μ a' (0 : Zd d L) b false hμ hk hkl hl,
    KLWard_cutGlueR_fullLoop μ a' (0 : Zd d L) b true hμ hk hkl hl]

/-- **W2**: a cut `(k, N + 1)` with `2 ≤ k ≤ N`; uses cyclic invariance. -/
private theorem KLWard_cut_last (hμ : μ.length + 1 = a'.length) {k : ℕ} (hk : 2 ≤ k)
    (hkN : k ≤ a'.length)
    (hcyc : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → K (KLWard_rot J) = K J) (a b : Zd d L) :
    (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k (a'.length + 1) a)) * SB d L g a b *
        K ((KLWard_fullLoop μ a' 0).cutGlueR k (a'.length + 1) b)
      = (KLWard_wD d L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a])
          + κ * (K ((KLWard_pmLoop true μ a').cutGlueR 1 k a)
            - K ((KLWard_pmLoop false μ a').cutGlueR 1 k a))) * SB d L g a b *
          K ((KLWard_pmLoop false μ a').cutGlueL 1 k b) := by
  have hL : ∀ x, (KLWard_fullLoop μ a' x).cutGlueL k (a'.length + 1) a
      = KLWard_fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) x :=
    fun x => KLWard_cutGlueL_fullLoop_last μ a' x a hμ (by omega) hkN
  have hWF : ((KLWard_pmLoop false μ a').cutGlueL 1 k b).WF := by
    refine LoopIdx.wf_cutGlueL _ b ?_ le_rfl (by omega) ?_
    · simp [LoopIdx.WF, KLWard_pmLoop, hμ]
    · simp [LoopIdx.length, KLWard_pmLoop]; omega
  have hlen : 2 ≤ ((KLWard_pmLoop false μ a').cutGlueL 1 k b).length := by
    refine KLWard_two_le_length_cutGlueL _ b le_rfl (by omega) ?_
    simp [LoopIdx.length, KLWard_pmLoop]; omega
  simp only [hL, KLWard_cutGlueR_fullLoop_last μ a' 0 b hμ hk hkN, hcyc _ hWF hlen,
    KLWard_cutGlueR_pmLoop_one μ a' a true (by omega : 1 < k),
    KLWard_cutGlueR_pmLoop_one μ a' a false (by omega : 1 < k)]
  rw [show ∑ x : Zd d L, K (KLWard_fullLoop (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) x)
      = KLWard_wStar d L K (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) from rfl, KLWard_wStar_eq d L K κ]

/-- **W3**: the cut `(1, N + 1)`; the column sums of `S^(B)` are `1`. -/
private theorem KLWard_cut_one_last (hL : 3 ≤ L) (hμ : μ.length + 1 = a'.length) (c : ℂ)
    (h2 : ∀ a : Zd d L, KLWard_wStar d L K [] [a] = c) :
    ∑ a : Zd d L, ∑ b : Zd d L,
        (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL 1 (a'.length + 1) a)) * SB d L g a b *
          K ((KLWard_fullLoop μ a' 0).cutGlueR 1 (a'.length + 1) b)
      = c * KLWard_wStar d L K μ a' := by
  have hL1 : ∀ x a, (KLWard_fullLoop μ a' x).cutGlueL 1 (a'.length + 1) a
      = KLWard_fullLoop [] [a] x := by
    intro x a
    rw [KLWard_cutGlueL_fullLoop_last μ a' x a hμ le_rfl (by omega)]
    simp
  simp only [hL1, KLWard_cutGlueR_fullLoop_last_one μ a' 0 _ hμ]
  simp only [show ∀ a, ∑ x : Zd d L, K (KLWard_fullLoop [] [a] x) = KLWard_wStar d L K [] [a]
    from fun _ => rfl, h2]
  rw [Finset.sum_comm, KLWard_wStar, Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcol : ∑ a : Zd d L, SB d L g a b = 1 := by
    rw [← sum_SB_row d L g hL b]
    exact sum_congr rfl fun a _ => congrFun (congrFun (SB_transpose d L g) b) a
  rw [hcol, mul_one]

/-- A double sum over `1 ≤ k < l ≤ N` of a function vanishing unless `l = k + 1`. -/
private theorem KLWard_sum_Icc_Ioc_adjacent {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : ℕ → ℕ → M) (hf : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, k + 1 < l → f k l = 0) :
    ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, f k l = ∑ k ∈ Icc 1 (N - 1), f k (k + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [sum_Icc_succ_top (by omega), Ioc_self, sum_empty, add_zero, Nat.add_sub_cancel]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Icc] at hk
  rw [Finset.sum_eq_single_of_mem (k + 1) (by rw [mem_Ioc]; omega)]
  intro l hl hne
  refine hf k (by rw [mem_Icc]; omega) l hl ?_
  rw [mem_Ioc] at hl
  omega

/-- **The right-hand side of the derivative of `(WI_calK)`**, at a fixed time. -/
private theorem KLWard_rhs_identity (hL : 3 ≤ L) (W : ℕ) (c : ℂ)
    (hμ : μ.length + 1 = a'.length) (hN : 2 ≤ a'.length)
    (hcyc : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → K (KLWard_rot J) = K J)
    (h2 : ∀ a : Zd d L, KLWard_wStar d L K [] [a] = c)
    (hlow : ∀ (μ'' : List Bool) (a'' : List (Zd d L)), μ''.length + 1 = a''.length →
      a''.length < a'.length → KLWard_wD d L K κ μ'' a'' = 0) :
    ∑ x : Zd d L, treeEqRhs d L W g K (KLWard_fullLoop μ a' x)
      - κ * (treeEqRhs d L W g K (KLWard_pmLoop true μ a') - treeEqRhs d L W g K (KLWard_pmLoop false μ a'))
      = (W : ℂ) ^ d *
        (∑ k ∈ Icc 1 (a'.length - 1), ∑ a : Zd d L, ∑ b : Zd d L,
            KLWard_wD d L K κ (KLWard_cutMu k (k + 1) μ) (KLWard_cutA k (k + 1) a a') * SB d L g a b *
              K ((KLWard_pmLoop true μ a').cutGlueR k (k + 1) b)
          + ∑ a : Zd d L, ∑ b : Zd d L,
            KLWard_wD d L K κ (μ.take (a'.length - 1)) (a'.take (a'.length - 1) ++ [a])
              * SB d L g a b * K ((KLWard_pmLoop false μ a').cutGlueL 1 a'.length b)
          + c * KLWard_wStar d L K μ a') := by
  set N := a'.length with hNdef
  have hpmlen : ∀ s, (KLWard_pmLoop s μ a').length = N := fun s => by
    simp [LoopIdx.length, KLWard_pmLoop, hNdef]
  have hpm : ∀ s, treeEqRhs d L W g K (KLWard_pmLoop s μ a') = (W : ℂ) ^ d *
      ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
        K ((KLWard_pmLoop s μ a').cutGlueL k l a) * SB d L g a b *
          K ((KLWard_pmLoop s μ a').cutGlueR k l b) :=
    fun s => by rw [treeEqRhs, hpmlen]
  rw [KLWard_sum_treeEqRhs_fullLoop d L g W K μ a', hpm, hpm]
  -- (i) the cuts with `l ≤ N`
  have hA : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, ∀ a b : Zd d L,
      (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k l a)) * SB d L g a b *
          K ((KLWard_fullLoop μ a' 0).cutGlueR k l b)
        - κ * (K ((KLWard_pmLoop true μ a').cutGlueL k l a) * SB d L g a b *
              K ((KLWard_pmLoop true μ a').cutGlueR k l b)
            - K ((KLWard_pmLoop false μ a').cutGlueL k l a) * SB d L g a b *
              K ((KLWard_pmLoop false μ a').cutGlueR k l b))
        = KLWard_wD d L K κ (KLWard_cutMu k l μ) (KLWard_cutA k l a a') * SB d L g a b *
            K ((KLWard_pmLoop true μ a').cutGlueR k l b)
          + (if k = 1 then κ * K ((KLWard_pmLoop false μ a').cutGlueL 1 l a) * SB d L g a b *
              (K ((KLWard_pmLoop false μ a').cutGlueR 1 l b)
                - K ((KLWard_pmLoop true μ a').cutGlueR 1 l b)) else 0) := by
    intro k hk l hl a b
    rw [mem_Icc] at hk
    rw [mem_Ioc] at hl
    rw [KLWard_cut_inner d L g K κ μ a' hμ hk.1 hl.1 hl.2]
    split_ifs with h1
    · subst h1
      rfl
    · rw [KLWard_cutGlueR_pmLoop_indep d L μ a' hμ (by omega) hl.1 hl.2, sub_self, mul_zero]
  -- (ii) the cuts `(k, N + 1)`
  have hB : ∀ k ∈ Icc 2 N, ∀ a b : Zd d L,
      (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k (N + 1) a)) * SB d L g a b *
          K ((KLWard_fullLoop μ a' 0).cutGlueR k (N + 1) b)
        = KLWard_wD d L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB d L g a b *
            K ((KLWard_pmLoop false μ a').cutGlueL 1 k b)
          + κ * (K ((KLWard_pmLoop true μ a').cutGlueR 1 k a)
              - K ((KLWard_pmLoop false μ a').cutGlueR 1 k a))
            * SB d L g a b * K ((KLWard_pmLoop false μ a').cutGlueL 1 k b) := by
    intro k hk a b
    rw [mem_Icc] at hk
    rw [KLWard_cut_last d L g K κ μ a' hμ hk.1 hk.2 hcyc]
    ring
  have hIcc : Icc 1 N = insert 1 (Icc 2 N) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  have hIoc : Ioc 1 N = Icc 2 N := by
    ext k
    simp only [mem_Icc, mem_Ioc]
    omega
  have hcutlen : ∀ k l, 1 ≤ k → k < l → l ≤ N → ∀ a : Zd d L,
      (KLWard_cutMu k l μ).length + 1 = (KLWard_cutA k l a a').length ∧
        (KLWard_cutA k l a a').length = N + k - l + 1 := by
    intro k l hk hkl hl a
    simp only [KLWard_cutMu, KLWard_cutA, List.length_append, List.length_take, List.length_drop,
      List.length_cons]
    omega
  have hT1 : ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
      KLWard_wD d L K κ (KLWard_cutMu k l μ) (KLWard_cutA k l a a') * SB d L g a b *
        K ((KLWard_pmLoop true μ a').cutGlueR k l b)
      = ∑ k ∈ Icc 1 (N - 1), ∑ a : Zd d L, ∑ b : Zd d L,
          KLWard_wD d L K κ (KLWard_cutMu k (k + 1) μ) (KLWard_cutA k (k + 1) a a') * SB d L g a b *
            K ((KLWard_pmLoop true μ a').cutGlueR k (k + 1) b) := by
    refine KLWard_sum_Icc_Ioc_adjacent N (fun k l => ∑ a : Zd d L, ∑ b : Zd d L,
      KLWard_wD d L K κ (KLWard_cutMu k l μ) (KLWard_cutA k l a a') * SB d L g a b *
        K ((KLWard_pmLoop true μ a').cutGlueR k l b)) ?_
    intro k hk l hl hkl
    rw [mem_Icc] at hk
    rw [mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    obtain ⟨h1, h2⟩ := hcutlen k l hk.1 hl.1 hl.2 a
    rw [hlow _ _ h1 (by omega), zero_mul, zero_mul]
  have hU2 : ∑ k ∈ Icc 2 N, ∑ a : Zd d L, ∑ b : Zd d L,
      KLWard_wD d L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB d L g a b *
        K ((KLWard_pmLoop false μ a').cutGlueL 1 k b)
      = ∑ a : Zd d L, ∑ b : Zd d L,
          KLWard_wD d L K κ (μ.take (N - 1)) (a'.take (N - 1) ++ [a]) * SB d L g a b *
            K ((KLWard_pmLoop false μ a').cutGlueL 1 N b) := by
    rw [Finset.sum_eq_single_of_mem N (by rw [mem_Icc]; omega)]
    intro k hk hkN
    rw [mem_Icc] at hk
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [hlow _ _ (by simp only [List.length_take, List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_take, List.length_singleton]; omega),
      zero_mul, zero_mul]
  have hcancel : (∑ l ∈ Ioc 1 N, ∑ a : Zd d L, ∑ b : Zd d L,
        κ * K ((KLWard_pmLoop false μ a').cutGlueL 1 l a) * SB d L g a b *
          (K ((KLWard_pmLoop false μ a').cutGlueR 1 l b)
            - K ((KLWard_pmLoop true μ a').cutGlueR 1 l b)))
      + ∑ k ∈ Icc 2 N, ∑ a : Zd d L, ∑ b : Zd d L,
        κ * (K ((KLWard_pmLoop true μ a').cutGlueR 1 k a)
            - K ((KLWard_pmLoop false μ a').cutGlueR 1 k a))
          * SB d L g a b * K ((KLWard_pmLoop false μ a').cutGlueL 1 k b) = 0 := by
    rw [hIoc, ← sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Finset.sum_comm (s := (univ : Finset (Zd d L))) (t := (univ : Finset (Zd d L)))
      (f := fun a b => κ * (K ((KLWard_pmLoop true μ a').cutGlueR 1 k a)
        - K ((KLWard_pmLoop false μ a').cutGlueR 1 k a)) * SB d L g a b *
          K ((KLWard_pmLoop false μ a').cutGlueL 1 k b)), ← sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [show SB d L g b a = SB d L g a b from congrFun (congrFun (SB_transpose d L g) a) b]
    ring
  simp only [← hNdef]
  -- the Ward-bracket part
  have eA : (∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
        (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k l a)) * SB d L g a b *
          K ((KLWard_fullLoop μ a' 0).cutGlueR k l b))
      - κ * ((∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
          K ((KLWard_pmLoop true μ a').cutGlueL k l a) * SB d L g a b *
            K ((KLWard_pmLoop true μ a').cutGlueR k l b))
        - ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
          K ((KLWard_pmLoop false μ a').cutGlueL k l a) * SB d L g a b *
            K ((KLWard_pmLoop false μ a').cutGlueR k l b))
      = (∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
          KLWard_wD d L K κ (KLWard_cutMu k l μ) (KLWard_cutA k l a a') * SB d L g a b *
            K ((KLWard_pmLoop true μ a').cutGlueR k l b))
        + ∑ l ∈ Ioc 1 N, ∑ a : Zd d L, ∑ b : Zd d L,
          κ * K ((KLWard_pmLoop false μ a').cutGlueL 1 l a) * SB d L g a b *
            (K ((KLWard_pmLoop false μ a').cutGlueR 1 l b)
              - K ((KLWard_pmLoop true μ a').cutGlueR 1 l b)) := by
    have e1 : ∀ k ∈ Icc 1 N, ∀ l ∈ Ioc k N, ∀ a : Zd d L,
        ∑ b : Zd d L, ((∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k l a)) * SB d L g a b *
            K ((KLWard_fullLoop μ a' 0).cutGlueR k l b)
          - κ * (K ((KLWard_pmLoop true μ a').cutGlueL k l a) * SB d L g a b *
                K ((KLWard_pmLoop true μ a').cutGlueR k l b)
              - K ((KLWard_pmLoop false μ a').cutGlueL k l a) * SB d L g a b *
                K ((KLWard_pmLoop false μ a').cutGlueR k l b)))
        = ∑ b : Zd d L, (KLWard_wD d L K κ (KLWard_cutMu k l μ) (KLWard_cutA k l a a') * SB d L g a b *
              K ((KLWard_pmLoop true μ a').cutGlueR k l b)
            + (if k = 1 then κ * K ((KLWard_pmLoop false μ a').cutGlueL 1 l a) * SB d L g a b *
                (K ((KLWard_pmLoop false μ a').cutGlueR 1 l b)
                  - K ((KLWard_pmLoop true μ a').cutGlueR 1 l b)) else 0)) :=
      fun k hk l hl a => sum_congr rfl fun b _ => hA k hk l hl a b
    calc _ = ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
          ((∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k l a)) * SB d L g a b *
              K ((KLWard_fullLoop μ a' 0).cutGlueR k l b)
            - κ * (K ((KLWard_pmLoop true μ a').cutGlueL k l a) * SB d L g a b *
                  K ((KLWard_pmLoop true μ a').cutGlueR k l b)
                - K ((KLWard_pmLoop false μ a').cutGlueL k l a) * SB d L g a b *
                  K ((KLWard_pmLoop false μ a').cutGlueR k l b))) := by
          simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = ∑ k ∈ Icc 1 N, ∑ l ∈ Ioc k N, ∑ a : Zd d L, ∑ b : Zd d L,
          (KLWard_wD d L K κ (KLWard_cutMu k l μ) (KLWard_cutA k l a a') * SB d L g a b *
              K ((KLWard_pmLoop true μ a').cutGlueR k l b)
            + (if k = 1 then κ * K ((KLWard_pmLoop false μ a').cutGlueL 1 l a) * SB d L g a b *
                (K ((KLWard_pmLoop false μ a').cutGlueR 1 l b)
                  - K ((KLWard_pmLoop true μ a').cutGlueR 1 l b)) else 0)) :=
          sum_congr rfl fun k hk => sum_congr rfl fun l hl => sum_congr rfl fun a _ =>
            e1 k hk l hl a
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          congr 1
          rw [hIcc, sum_insert (by simp)]
          simp only [ite_true]
          rw [Finset.sum_eq_zero (s := Icc 2 N) fun k hk => ?_, add_zero]
          rw [mem_Icc] at hk
          simp only [show k ≠ 1 by omega, ite_false, Finset.sum_const_zero]
  -- the cuts `(k, N + 1)`
  have eB : (∑ k ∈ Icc 1 N, ∑ a : Zd d L, ∑ b : Zd d L,
        (∑ x : Zd d L, K ((KLWard_fullLoop μ a' x).cutGlueL k (N + 1) a)) * SB d L g a b *
          K ((KLWard_fullLoop μ a' 0).cutGlueR k (N + 1) b))
      = c * KLWard_wStar d L K μ a'
        + (∑ k ∈ Icc 2 N, ∑ a : Zd d L, ∑ b : Zd d L,
            KLWard_wD d L K κ (μ.take (k - 1)) (a'.take (k - 1) ++ [a]) * SB d L g a b *
              K ((KLWard_pmLoop false μ a').cutGlueL 1 k b))
        + ∑ k ∈ Icc 2 N, ∑ a : Zd d L, ∑ b : Zd d L,
            κ * (K ((KLWard_pmLoop true μ a').cutGlueR 1 k a)
                - K ((KLWard_pmLoop false μ a').cutGlueR 1 k a))
              * SB d L g a b * K ((KLWard_pmLoop false μ a').cutGlueL 1 k b) := by
    rw [hIcc, sum_insert (by simp), hNdef, KLWard_cut_one_last d L g K μ a' hL hμ c h2, ← hNdef,
      add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun b _ => hB k hk a b
  rw [show ∀ A B P P' : ℂ, (W : ℂ) ^ d * (A + B) - κ * ((W : ℂ) ^ d * P - (W : ℂ) ^ d * P')
      = (W : ℂ) ^ d * ((A - κ * (P - P')) + B) from fun A B P P' => by ring, eA, eB, hT1, hU2]
  rw [show ∀ T1 T2 cw U2 U3 : ℂ, T1 + T2 + (cw + U2 + U3) = T1 + U2 + cw + (T2 + U3)
      from fun T1 T2 cw U2 U3 => by ring, hcancel, add_zero]

end Cuts

end Step

/-! ## 3. `κ_t`, `c_t` and the initial value (port of `RBM2D/Loop/Ward.lean:558-690` at `c9a24cf`) -/

section Kappa

variable (d : ℕ) {E : ℝ}

/-- `κ_t = (2 i W^d η_t)⁻¹`, the coefficient of `(WI_calK)`. -/
private noncomputable def KLWard_kappa (W : ℕ) (E t : ℝ) : ℂ :=
  (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹

/-- `c_t = (W^d (1 − t))⁻¹`, the common value of the two sides at `n = 2`. -/
private noncomputable def KLWard_c (W : ℕ) (t : ℝ) : ℂ := ((W : ℂ) ^ d * (1 - t))⁻¹

/-- `η_t = (1 − t) Im m^{(E)}` (`(eta)`). -/
private theorem KLWard_etaT_eq (E t : ℝ) : Gauss.etaT E t = (1 - t) * (mE E).im := rfl

private theorem KLWard_mSigma_mul (hE : |E| ≤ 2) : mSigma E true * mSigma E false = 1 := by
  simp only [mSigma, ↓reduceIte, Bool.false_eq_true]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE hE]
  simp

/-- `κ_t (m − m̄) = c_t`. -/
private theorem KLWard_kappa_mul (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) :
    KLWard_kappa d W E t * (mSigma E true - mSigma E false) = KLWard_c d W t := by
  have him : ((mE E).im : ℂ) ≠ 0 := by
    exact_mod_cast (mE_im_pos hE).ne'
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  simp only [KLWard_kappa, KLWard_c, mSigma, ↓reduceIte, Bool.false_eq_true, Complex.sub_conj,
    KLWard_etaT_eq]
  push_cast
  field_simp

/-- `∂_t κ_t = κ_t / (1 − t)`. -/
private theorem KLWard_hasDerivAt_kappa (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2) {t : ℝ}
    (ht1 : t < 1) : HasDerivAt (KLWard_kappa d W E) (KLWard_kappa d W E t / (1 - t)) t := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hIm : ((mE E).im : ℂ) ≠ 0 := by
    exact_mod_cast (mE_im_pos hE).ne'
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  have hg : HasDerivAt (fun s : ℝ => 2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E s : ℂ))
      (-(2 * Complex.I * (W : ℂ) ^ d * (mE E).im)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (Gauss.etaT E s : ℂ)) (-((mE E).im : ℂ)) t := by
      have := (((hasDerivAt_id t).const_sub 1).mul_const (mE E).im).ofReal_comp
      simpa [KLWard_etaT_eq] using this
    exact (h1.const_mul (2 * Complex.I * (W : ℂ) ^ d)).congr_deriv (by ring)
  have hne : 2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ) ≠ 0 := by
    rw [KLWard_etaT_eq]
    push_cast
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (pow_ne_zero d hW0)) (mul_ne_zero ht hIm)
  refine (hg.inv hne).congr_deriv ?_
  simp only [KLWard_kappa, KLWard_etaT_eq]
  push_cast
  field_simp

end Kappa

section Init

variable (d L : ℕ) [NeZero L]

/-- Summing the "all labels equal" indicator over the last label. -/
private theorem KLWard_sum_allEq_append (a' : List (Zd d L)) (ha : a' ≠ []) :
    ∑ x : Zd d L, (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then (1 : ℂ) else 0)
      = if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0 := by
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil ha
  have hh : h ∈ h :: t := List.mem_cons_self
  by_cases hall : ∀ y ∈ h :: t, ∀ z ∈ h :: t, y = z
  · rw [ite_eq_left hall]
    have key : ∀ x : Zd d L,
        (∀ y ∈ h :: t ++ [x], ∀ z ∈ h :: t ++ [x], y = z) ↔ x = h := by
      intro x
      constructor
      · intro hx
        exact hx x (List.mem_append_right _ (List.mem_singleton_self x)) h
          (List.mem_append_left _ hh)
      · intro hxh
        have hin : ∀ w ∈ h :: t ++ [x], w ∈ h :: t := by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact hw
          · rw [List.mem_singleton.mp hw, hxh]
            exact hh
        exact fun y hy z hz => hall y (hin y hy) z (hin z hz)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [ite_eq_right hall]
    refine Finset.sum_eq_zero fun x _ => ite_eq_right fun hx => hall fun y hy z hz =>
      hx y (List.mem_append_left _ hy) z (List.mem_append_left _ hz)

/-- **The initial value.**  At `t = 0`, `(WI_calK)` holds for the initial value `MLoop`. -/
private theorem KLWard_wD_MLoop (W : ℕ) (hW : W ≠ 0) {E : ℝ} (hE : |E| < 2) (μ : List Bool)
    (a' : List (Zd d L)) (hμ : μ.length + 1 = a'.length) :
    KLWard_wD d L (MLoop d L W (mSigma E)) (KLWard_kappa d W E 0) μ a' = 0 := by
  have ha : a' ≠ [] := by
    intro h
    rw [h] at hμ
    simp at hμ
  obtain ⟨N, hN⟩ : ∃ N, a'.length = N + 1 := ⟨a'.length - 1, by omega⟩
  have hfull : ∀ x : Zd d L, MLoop d L W (mSigma E) (KLWard_fullLoop μ a' x)
      = ((W : ℂ) ^ d)⁻¹ ^ (N + 1) * (mSigma E true * (μ.map (mSigma E)).prod * mSigma E false) *
        (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then 1 else 0) := by
    intro x
    simp only [MLoop, KLWard_fullLoop, LoopIdx.length, List.length_append,
      List.length_singleton, hN, Nat.add_sub_cancel, List.map_cons, List.map_append,
      List.map_nil, List.prod_cons, List.prod_append, List.prod_nil, mul_one, mul_assoc]
    rfl
  have hpm : ∀ s, MLoop d L W (mSigma E) (KLWard_pmLoop s μ a')
      = ((W : ℂ) ^ d)⁻¹ ^ N * (mSigma E s * (μ.map (mSigma E)).prod) *
        (if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0) := by
    intro s
    simp only [MLoop, KLWard_pmLoop, LoopIdx.length, hN, Nat.add_sub_cancel, List.map_cons,
      List.prod_cons]
    rfl
  have hk := KLWard_kappa_mul d W hW hE (t := 0) (by norm_num)
  have hc0 : KLWard_c d W 0 = ((W : ℂ) ^ d)⁻¹ := by simp [KLWard_c]
  have hmm : mSigma E true * mSigma E false = 1 := KLWard_mSigma_mul hE.le
  simp only [KLWard_wD, KLWard_wStar, hfull, hpm, ← Finset.mul_sum, KLWard_sum_allEq_append d L a' ha]
  set P := (μ.map (mSigma E)).prod
  set I := (if ∀ y ∈ a', ∀ z ∈ a', y = z then (1 : ℂ) else 0)
  calc ((W : ℂ) ^ d)⁻¹ ^ (N + 1) * (mSigma E true * P * mSigma E false) * I
        - KLWard_kappa d W E 0 * (((W : ℂ) ^ d)⁻¹ ^ N * (mSigma E true * P) * I
          - ((W : ℂ) ^ d)⁻¹ ^ N * (mSigma E false * P) * I)
      = ((W : ℂ) ^ d)⁻¹ ^ N * P * I * (((W : ℂ) ^ d)⁻¹ * (mSigma E true * mSigma E false)
          - KLWard_kappa d W E 0 * (mSigma E true - mSigma E false)) := by ring
    _ = 0 := by rw [hmm, hk, hc0, mul_one, sub_self, mul_zero]

end Init

/-! ## 4. Grönwall and induction on the length (port of `RBM2D/Loop/Ward.lean:692-922` at `c9a24cf`) -/

section Level

variable (d L : ℕ) [NeZero L] (g : ℝ) {E : ℝ}

private theorem KLWard_cutMu_adjacent (μ : List Bool) (k : ℕ) : KLWard_cutMu k (k + 1) μ = μ := by
  simp only [KLWard_cutMu, show k + 1 - 2 = k - 1 by omega, List.take_append_drop]

omit [NeZero L] in
private theorem KLWard_length_cutA_adjacent (a' : List (Zd d L)) (a : Zd d L) {k : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ a'.length) : (KLWard_cutA k (k + 1) a a').length = a'.length := by
  simp only [KLWard_cutA, List.length_append, List.length_take, List.length_cons,
    List.length_drop, Nat.add_sub_cancel]
  omega

private theorem KLWard_norm_SB_apply_le (hL : 3 ≤ L) (a b : Zd d L) : ‖SB d L g a b‖ ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => ‖SB d L g a b‖₊) (fun _ _ => by positivity)
    (Finset.mem_univ b)
  rw [sum_nnnorm_SB_row d L g hL a] at h
  exact_mod_cast h

/-- The index set of the level-`N` Ward defects: middle charges and labels. -/
private abbrev KLWard_Vec (N : ℕ) := List.Vector Bool (N - 1) × List.Vector (Zd d L) N

/-- **One level of the induction** (loops of length `N + 1 ≥ 3`). -/
private theorem KLWard_level (hL : 3 ≤ L) (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2)
    (K : ℝ → LoopIdx (Zd d L) → ℂ) (T₀ R : ℝ) (N : ℕ) (hN : 2 ≤ N) (hT₀ : T₀ < 1)
    (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => K s J) (treeEqRhs d L W g (K t) J) t)
    (hcyc : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      K t (KLWard_rot J) = K t J)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Zd d L), J.WF → J.length = 2 → ‖K t J‖ ≤ R)
    (h2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : Zd d L, KLWard_wStar d L (K t) [] [a] = KLWard_c d W t)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Zd d L)),
      μ.length + 1 = a'.length → a'.length < N → KLWard_wD d L (K t) (KLWard_kappa d W E t) μ a' = 0)
    (h0 : ∀ (μ : List Bool) (a' : List (Zd d L)), μ.length + 1 = a'.length → a'.length = N →
      KLWard_wD d L (K 0) (KLWard_kappa d W E 0) μ a' = 0) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Zd d L)), μ.length + 1 = a'.length →
      a'.length = N → KLWard_wD d L (K t) (KLWard_kappa d W E t) μ a' = 0 := by
  let κ := KLWard_kappa d W E
  let D : ℝ → KLWard_Vec d L N → ℂ := fun t p => KLWard_wD d L (K t) (κ t) p.1.1 p.2.1
  have hp : ∀ p : KLWard_Vec d L N, p.1.1.length + 1 = p.2.1.length := fun p => by
    rw [p.1.2, p.2.2]
    omega
  have hpN : ∀ p : KLWard_Vec d L N, p.2.1.length = N := fun p => p.2.2
  let T : ℝ → KLWard_Vec d L N → ℂ := fun t p =>
    (∑ k ∈ Icc 1 (N - 1), ∑ a : Zd d L, ∑ b : Zd d L,
        KLWard_wD d L (K t) (κ t) (KLWard_cutMu k (k + 1) p.1.1) (KLWard_cutA k (k + 1) a p.2.1)
          * SB d L g a b * K t ((KLWard_pmLoop true p.1.1 p.2.1).cutGlueR k (k + 1) b))
      + ∑ a : Zd d L, ∑ b : Zd d L,
        KLWard_wD d L (K t) (κ t) (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a]) * SB d L g a b *
          K t ((KLWard_pmLoop false p.1.1 p.2.1).cutGlueL 1 N b)
  let D' : ℝ → KLWard_Vec d L N → ℂ := fun t p =>
    (W : ℂ) ^ d * T t p + (1 - (t : ℂ))⁻¹ * D t p
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hfullWF : ∀ (μ : List Bool) (a' : List (Zd d L)) (x : Zd d L),
      μ.length + 1 = a'.length →
        (KLWard_fullLoop μ a' x).WF ∧ (KLWard_fullLoop μ a' x).length = a'.length + 1 :=
    fun μ a' x h => ⟨by simp [LoopIdx.WF, KLWard_fullLoop]; omega,
      by simp [LoopIdx.length, KLWard_fullLoop]⟩
  have hpmWF : ∀ (s : Bool) (μ : List Bool) (a' : List (Zd d L)),
      μ.length + 1 = a'.length →
        (KLWard_pmLoop s μ a').WF ∧ (KLWard_pmLoop s μ a').length = a'.length :=
    fun s μ a' h => ⟨by simp [LoopIdx.WF, KLWard_pmLoop]; omega,
      by simp [LoopIdx.length, KLWard_pmLoop]⟩
  -- the derivative
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
    refine hasDerivAt_pi.2 fun p => ?_
    obtain ⟨hWFp, hlp⟩ := hpmWF true p.1.1 p.2.1 (hp p)
    obtain ⟨hWFm, hlm⟩ := hpmWF false p.1.1 p.2.1 (hp p)
    have hsum : HasDerivAt (fun s => ∑ x : Zd d L, K s (KLWard_fullLoop p.1.1 p.2.1 x))
        (∑ x : Zd d L, treeEqRhs d L W g (K t) (KLWard_fullLoop p.1.1 p.2.1 x)) t :=
      HasDerivAt.fun_sum fun x _ => hK t ht _ (hfullWF _ _ x (hp p)).1
        (by rw [(hfullWF _ _ x (hp p)).2, hpN]; omega)
    have hplus := hK t ht _ hWFp (by rw [hlp, hpN]; omega)
    have hminus := hK t ht _ hWFm (by rw [hlm, hpN]; omega)
    have hprod := (KLWard_hasDerivAt_kappa d W hW hE ht1).mul (hplus.sub hminus)
    refine (hsum.sub hprod).congr_deriv ?_
    have hid := KLWard_rhs_identity d L g (K t) (κ t) p.1.1 p.2.1 hL W (KLWard_c d W t) (hp p)
      (by rw [hpN]; exact hN) (hcyc t ht) (h2 t ht)
      (fun μ'' a'' h1 h2' => hlow t ht μ'' a'' h1 (by rw [hpN] at h2'; exact h2'))
    have hWc : (W : ℂ) ^ d * KLWard_c d W t = (1 - (t : ℂ))⁻¹ := by
      rw [KLWard_c, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hW0), one_mul]
    have ht' : (1 : ℂ) - t ≠ 0 := by
      rw [sub_ne_zero, ne_comm]
      exact_mod_cast ht1.ne
    simp only [D', T, D, KLWard_wD, κ, hpN, Pi.sub_apply] at hid ⊢
    linear_combination hid + KLWard_wStar d L (K t) p.1.1 p.2.1 * hWc
  -- components of `D t`
  have hcomp : ∀ t (μ : List Bool) (a' : List (Zd d L)), μ.length = N - 1 → a'.length = N →
      ‖KLWard_wD d L (K t) (κ t) μ a'‖ ≤ ‖D t‖ :=
    fun t μ a' h1 h2 => norm_le_pi_norm (D t) (⟨μ, h1⟩, ⟨a', h2⟩)
  -- the bound
  set C : ℝ := (W : ℝ) ^ d * ((∑ _k ∈ Icc 1 (N - 1), ∑ _a : Zd d L, ∑ _b : Zd d L, R)
    + ∑ _a : Zd d L, ∑ _b : Zd d L, R) + (1 - T₀)⁻¹ with hC
  have hT₀' : 0 < 1 - T₀ := by linarith
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (norm_nonneg _))).2 fun p => ?_
    have hμN : p.1.1.length = N - 1 := p.1.2
    obtain ⟨hWFp, hlp⟩ := hpmWF true p.1.1 p.2.1 (hp p)
    obtain ⟨hWFm, hlm⟩ := hpmWF false p.1.1 p.2.1 (hp p)
    have hT1 : ∀ k ∈ Icc 1 (N - 1), ∀ a b : Zd d L,
        ‖KLWard_wD d L (K t) (κ t) (KLWard_cutMu k (k + 1) p.1.1) (KLWard_cutA k (k + 1) a p.2.1)
          * SB d L g a b * K t ((KLWard_pmLoop true p.1.1 p.2.1).cutGlueR k (k + 1) b)‖
          ≤ R * ‖D t‖ := by
      intro k hk a b
      rw [mem_Icc] at hk
      have hlpN : k + 1 ≤ (KLWard_pmLoop true p.1.1 p.2.1).length := by rw [hlp, hpN]; omega
      have hWR := LoopIdx.wf_cutGlueR _ b hWFp hk.1 (Nat.lt_succ_self k) hlpN
      have hlen := LoopIdx.length_cutGlueR (KLWard_pmLoop true p.1.1 p.2.1) b hk.1
        (Nat.lt_succ_self k) hlpN
      have hK2 := hR t ht' _ hWR (by rw [hlen]; omega)
      have hD1 := hcomp t (KLWard_cutMu k (k + 1) p.1.1) (KLWard_cutA k (k + 1) a p.2.1)
        (by rw [KLWard_cutMu_adjacent]; exact hμN)
        (by rw [KLWard_length_cutA_adjacent d L p.2.1 a hk.1 (by rw [hpN]; omega), hpN])
      rw [norm_mul, norm_mul]
      calc _ ≤ ‖D t‖ * 1 * R := by
            gcongr
            exact KLWard_norm_SB_apply_le d L g hL a b
        _ = R * ‖D t‖ := by ring
    have hT2 : ∀ a b : Zd d L,
        ‖KLWard_wD d L (K t) (κ t) (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a]) * SB d L g a b *
          K t ((KLWard_pmLoop false p.1.1 p.2.1).cutGlueL 1 N b)‖ ≤ R * ‖D t‖ := by
      intro a b
      have hlmN : N ≤ (KLWard_pmLoop false p.1.1 p.2.1).length := by rw [hlm, hpN]
      have hWL := LoopIdx.wf_cutGlueL _ b hWFm le_rfl (by omega) hlmN
      have hlen := LoopIdx.length_cutGlueL (KLWard_pmLoop false p.1.1 p.2.1) b le_rfl
        (by omega) hlmN
      have hK2 := hR t ht' _ hWL (by rw [hlen, hlm, hpN]; omega)
      have hD1 := hcomp t (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a])
        (by rw [List.length_take, hμN]; omega)
        (by rw [List.length_append, List.length_take, hpN, List.length_singleton]; omega)
      rw [norm_mul, norm_mul]
      calc _ ≤ ‖D t‖ * 1 * R := by
            gcongr
            exact KLWard_norm_SB_apply_le d L g hL a b
        _ = R * ‖D t‖ := by ring
    have hinv : ‖(1 - (t : ℂ))⁻¹‖ ≤ (1 - T₀)⁻¹ := by
      rw [norm_inv, show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg h1t.le]
      exact inv_anti₀ hT₀' (by linarith [ht.2])
    calc ‖D' t p‖ ≤ ‖(W : ℂ) ^ d * T t p‖ + ‖(1 - (t : ℂ))⁻¹ * D t p‖ := norm_add_le _ _
      _ ≤ (W : ℝ) ^ d * ((∑ _k ∈ Icc 1 (N - 1), ∑ _a : Zd d L, ∑ _b : Zd d L, R * ‖D t‖)
            + ∑ _a : Zd d L, ∑ _b : Zd d L, R * ‖D t‖) + (1 - T₀)⁻¹ * ‖D t‖ := by
          gcongr
          · rw [norm_mul, norm_pow, Complex.norm_natCast]
            gcongr
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
              exact hT1 k hk a b
            · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
              exact hT2 a b
          · rw [norm_mul]
            exact mul_le_mul hinv (norm_le_pi_norm (D t) p) (norm_nonneg _) (by positivity)
      _ = C * ‖D t‖ := by
          simp only [hC, add_mul, Finset.sum_mul, mul_assoc]
  have hD0 : D 0 = 0 := funext fun p => h0 _ _ (hp p) (hpN p)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt) hD0 hbound
  intro t ht μ a' hμ ha'
  have hμ' : μ.length = N - 1 := by omega
  exact congrFun (hzero t ht) (⟨μ, hμ'⟩, ⟨a', ha'⟩)

/-- **`(WI_calK)` at every length** for a family of `K`-loops with bounded `2`-loops, cyclic
invariance and the level-`2` identity (the level-`2` identity and the cyclic invariance are
hypotheses `hlev2`, `hcyc`). -/
private theorem KLWard_of_isKLoop (hL : 3 ≤ L) (W : ℕ) (hW : W ≠ 0) (hE : |E| < 2)
    {T : Set ℝ} {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g (mSigma E) T K) {T₀ R : ℝ}
    (hT₀ : T₀ < 1) (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    (hcyc : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      K t (KLWard_rot J) = K t J)
    (hlev2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : Zd d L, KLWard_wD d L (K t) (KLWard_kappa d W E t) [] [a] = 0) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Zd d L)), μ.length + 1 = a'.length →
      KLWard_wD d L (K t) (KLWard_kappa d W E t) μ a' = 0 := by
  have h2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : Zd d L, KLWard_wStar d L (K t) [] [a] = KLWard_c d W t := by
    intro t ht a
    have h := hlev2 t ht a
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
    simp only [KLWard_wD, sub_eq_zero] at h
    rw [h]
    simp only [KLWard_pmLoop]
    rw [hK.2.2 t (hT ht) true a, hK.2.2 t (hT ht) false a, KLWard_kappa_mul d W hW hE ht1]
  -- the initial value
  have h0 : ∀ (μ : List Bool) (a' : List (Zd d L)), μ.length + 1 = a'.length → 2 ≤ a'.length →
      KLWard_wD d L (K 0) (KLWard_kappa d W E 0) μ a' = 0 := by
    intro μ a' hμ h2'
    rw [← KLWard_wD_MLoop d L W hW hE μ a' hμ]
    simp only [KLWard_wD, KLWard_wStar]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => hK.2.1 _ ?_ ?_
      · simp [LoopIdx.WF, KLWard_fullLoop]; omega
      · simp [LoopIdx.length, KLWard_fullLoop]; omega
    · rw [hK.2.1 _ (by simp [LoopIdx.WF, KLWard_pmLoop]; omega)
          (by simp [LoopIdx.length, KLWard_pmLoop]; omega),
        hK.2.1 _ (by simp [LoopIdx.WF, KLWard_pmLoop]; omega)
          (by simp [LoopIdx.length, KLWard_pmLoop]; omega)]
  -- induction on the length
  have main : ∀ N : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (Zd d L)),
      μ.length + 1 = a'.length → a'.length = N →
        KLWard_wD d L (K t) (KLWard_kappa d W E t) μ a' = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro t ht μ a' hμ hN
      rcases Nat.lt_or_ge N 2 with hN2 | hN2
      · have hμ0 : μ = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain ⟨a, ha⟩ : ∃ a, a' = [a] := List.length_eq_one_iff.mp (by omega)
        rw [hμ0, ha]
        exact hlev2 t ht a
      · refine KLWard_level d L g hL W hW hE K T₀ R N hN2 hT₀ hR0 (fun s hs => hK.1 s (hT hs))
          hcyc hR h2 ?_ ?_ t ht μ a' hμ hN
        · intro s hs μ'' a'' h1 hlt
          exact ih _ hlt s hs μ'' a'' h1 rfl
        · intro μ'' a'' h1 hN'
          exact h0 μ'' a'' h1 (by omega)
  intro t ht μ a' hμ
  exact main _ t ht μ a' hμ rfl

end Level

/-! ## 5. Flipping all charges: `𝒦_{t,-σ,a} = conj 𝒦_{t,σ,a}`

New (no RBM2D source: RBM2D proves `(WI_calK)` for `σ = (+, …, -)` only and flips only the layer
`Alayer`, `RBM2D/Loop/SumZeroWard.lean:1369-1395` at `c9a24cf`).  The proof is by uniqueness of the
family of `K`-loops (`KLK_unique`). -/

section Flip

/-- All charges of a loop index flipped: `σ ↦ -σ`. -/
private def KLWard_flipIdx {α : Type*} (I : LoopIdx α) : LoopIdx α := ⟨I.σ.map not, I.a⟩

/-- `flip` is an involution. -/
private theorem KLWard_flipIdx_involutive {α : Type*} (I : LoopIdx α) :
    KLWard_flipIdx (KLWard_flipIdx I) = I := by
  obtain ⟨σ, a⟩ := I
  simp [KLWard_flipIdx, List.map_map, Function.comp_def]

/-- `flip` preserves well-formedness. -/
private theorem KLWard_flipIdx_WF {α : Type*} {I : LoopIdx α} (hI : I.WF) : (KLWard_flipIdx I).WF := by
  simpa [KLWard_flipIdx, LoopIdx.WF] using hI

/-- `flip` preserves the length. -/
private theorem KLWard_flipIdx_length {α : Type*} (I : LoopIdx α) :
    (KLWard_flipIdx I).length = I.length := rfl

/-- `flip` commutes with the left cut-and-glue operator (it acts on the charges only). -/
private theorem KLWard_flipIdx_cutGlueL {α : Type*} (I : LoopIdx α) (k l : ℕ) (b : α) :
    (KLWard_flipIdx I).cutGlueL k l b = KLWard_flipIdx (I.cutGlueL k l b) := by
  simp [KLWard_flipIdx, LoopIdx.cutGlueL, List.map_append, List.map_take, List.map_drop]

/-- `flip` commutes with the right cut-and-glue operator. -/
private theorem KLWard_flipIdx_cutGlueR {α : Type*} (I : LoopIdx α) (k l : ℕ) (b : α) :
    (KLWard_flipIdx I).cutGlueR k l b = KLWard_flipIdx (I.cutGlueR k l b) := by
  simp [KLWard_flipIdx, LoopIdx.cutGlueR, List.map_take, List.map_drop]

variable (d L : ℕ) [NeZero L] (g : ℝ)

omit [NeZero L] in
/-- `S^(B)` is real. -/
private theorem KLWard_conj_SB (a b : Zd d L) :
    (starRingEnd ℂ) (SB d L g a b) = SB d L g a b := by
  rw [SB_apply, sbKernel_eq_ofReal, Complex.conj_ofReal]

/-- The right-hand side of `(pro_dyncalK)` of the family `conj ∘ K ∘ flip` is the conjugate of the
right-hand side of `K` at the flipped loop. -/
private theorem KLWard_treeEqRhs_flip (W : ℕ) (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    treeEqRhs d L W g (fun J => (starRingEnd ℂ) (K (KLWard_flipIdx J))) I
      = (starRingEnd ℂ) (treeEqRhs d L W g K (KLWard_flipIdx I)) := by
  unfold treeEqRhs
  rw [map_mul, map_pow, Complex.conj_natCast]
  congr 1
  simp only [map_sum, map_mul, KLWard_conj_SB, KLWard_flipIdx_cutGlueL, KLWard_flipIdx_cutGlueR,
    KLWard_flipIdx_length]

/-- `conj m(-s) = m(s)`. -/
private theorem KLWard_conj_mSigma_not (E : ℝ) (s : Bool) :
    (starRingEnd ℂ) (mSigma E (!s)) = mSigma E s := by
  cases s <;> simp [mSigma]

/-- The initial value `(eq:initial_K)` at the flipped loop, conjugated, is the initial value for the
charge function `s ↦ conj m(-s)`. -/
private theorem KLWard_conj_MLoop_flip (W : ℕ) (m : Bool → ℂ) (I : LoopIdx (Zd d L)) :
    (starRingEnd ℂ) (MLoop d L W m (KLWard_flipIdx I))
      = MLoop d L W (fun s => (starRingEnd ℂ) (m (!s))) I := by
  have hc : MLoop d L W m (KLWard_flipIdx I) = ((W : ℂ) ^ d)⁻¹ ^ (I.length - 1) *
      ((I.σ.map not).map m).prod * (if ∀ x ∈ I.a, ∀ y ∈ I.a, x = y then 1 else 0) := rfl
  rw [hc]
  simp only [MLoop, map_mul, map_pow, map_inv₀, Complex.conj_natCast, map_list_prod,
    List.map_map]
  congr 1
  split_ifs <;> simp

/-- The family `(t, I) ↦ conj 𝒦_{t, flip I}` is a family of `K`-loops on `[0,1)`: the equations
`(pro_dyncalK)` (the right-hand side is conjugated, `S^(B)` is real, `flip` commutes with the cuts),
the initial value `(eq:initial_K)` and `K^{(1)} = m` (`conj m(-s) = m(s)`). -/
private theorem KLWard_isKLoop_flip (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) :
    IsKLoop d L W g (mSigma E) (Set.Ico 0 1)
      (fun t I => (starRingEnd ℂ) (KLK d L g W E t (KLWard_flipIdx I))) := by
  have hKc := KLK_isKLoop d L W g E hL hW hE
  refine ⟨fun t ht I hI h2 => ?_, fun I hI h2 => ?_, fun t ht s a => ?_⟩
  · have h := (hKc.1 t ht (KLWard_flipIdx I) (KLWard_flipIdx_WF hI) h2).star
    rw [KLWard_treeEqRhs_flip]
    exact h
  · change (starRingEnd ℂ) (KLK d L g W E 0 (KLWard_flipIdx I)) = MLoop d L W (mSigma E) I
    rw [show KLK d L g W E 0 (KLWard_flipIdx I) = MLoop d L W (mSigma E) (KLWard_flipIdx I) from
      hKc.2.1 _ (KLWard_flipIdx_WF hI) h2, KLWard_conj_MLoop_flip]
    congr 1
    funext s
    exact KLWard_conj_mSigma_not E s
  · change (starRingEnd ℂ) (KLK d L g W E t ⟨[!s], [a]⟩) = mSigma E s
    rw [KLK_one, KLWard_conj_mSigma_not]

/-- **Flipping all charges conjugates `𝒦`**: `𝒦_{t,-σ,a} = conj 𝒦_{t,σ,a}` for every well-formed
loop of length `≥ 1`.  By `KLK_unique`: `(t, I) ↦ conj 𝒦_{t, flip I}` is a family of `K`-loops. -/
theorem KLWard_flip :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∀ (σ : List Bool) (a : List (Zd d L)), σ.length = a.length → 1 ≤ a.length →
        KLK d L g W E t ⟨σ.map not, a⟩ = (starRingEnd ℂ) (KLK d L g W E t ⟨σ, a⟩) := by
  intro d L W _ g E hL hW hE t ht σ a hσa h1
  have h := KLK_unique d L W g E hL hW hE _ (KLWard_isKLoop_flip d L g hL W hW hE) t ht
    (KLWard_flipIdx ⟨σ, a⟩) (KLWard_flipIdx_WF hσa) h1
  rw [KLWard_flipIdx_involutive] at h
  exact h.symm

end Flip

/-! ## 6. The pinned theorem -/

section Main

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- `(WI_calK)` for `σ₁ = +`, `σₙ = −`: port of `Kcal_ward` (`RBM2D/Loop/Ward.lean:969-1000` at
`c9a24cf`). -/
private theorem KLWard_pos (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (μ : List Bool) (a : List (Zd d L))
    (ha : a.length = μ.length + 1) :
    ∑ x : Zd d L, KLK d L g W E t ⟨true :: μ ++ [false], a ++ [x]⟩
      = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
          (KLK d L g W E t ⟨true :: μ, a⟩ - KLK d L g W E t ⟨false :: μ, a⟩) := by
  have hW0 : W ≠ 0 := by omega
  have hKc := KLK_isKLoop d L W g E hL hW hE
  have hT : Set.Icc 0 t ⊆ Set.Ico 0 1 := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  obtain ⟨R, hR0, hR⟩ := KLretire_twoLoopBounded hKc t ht.2
  have hcyc : ∀ r ∈ Set.Icc 0 t, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      KLK d L g W E r (KLWard_rot J) = KLK d L g W E r J := by
    intro r hr J hJ hJ2
    obtain ⟨σJ, aJ⟩ := J
    rcases aJ with _ | ⟨b, aJ⟩
    · simp [LoopIdx.length] at hJ2
    rcases σJ with _ | ⟨s, σJ⟩
    · simp [LoopIdx.WF] at hJ
    rw [KLWard_rot_mk_cons]
    exact (KLK_rotate d L W g E hL hW hE r (hT hr) s b σJ aJ
      (by simpa [LoopIdx.WF] using hJ)).symm
  have hlev2 : ∀ r ∈ Set.Icc 0 t, ∀ a₁ : Zd d L,
      KLWard_wD d L (KLK d L g W E r) (KLWard_kappa d W E r) [] [a₁] = 0 := by
    intro r hr a₁
    have h : ∑ x : Zd d L, KLK d L g W E r ⟨true :: [] ++ [false], [a₁] ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E r : ℂ))⁻¹ *
            (KLK d L g W E r ⟨true :: [], [a₁]⟩ - KLK d L g W E r ⟨false :: [], [a₁]⟩) :=
      KLward_two d L g hL W hW hE (hT hr) true a₁
    simp only [KLWard_wD, KLWard_wStar, KLWard_fullLoop, KLWard_pmLoop, KLWard_kappa]
    exact sub_eq_zero.2 h
  have h := KLWard_of_isKLoop d L g hL W hW0 hE hKc ht.2 hT hR0 hR hcyc hlev2 t
    ⟨ht.1, le_rfl⟩ μ a ha.symm
  simp only [KLWard_wD, KLWard_wStar, KLWard_fullLoop, KLWard_pmLoop, KLWard_kappa,
    sub_eq_zero] at h
  exact h

/-- `κ_t` is purely imaginary: `conj κ_t = -κ_t`. -/
private theorem KLWard_conj_kappa (W : ℕ) (E t : ℝ) :
    (starRingEnd ℂ) (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹
      = -(2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ := by
  have h1 : (starRingEnd ℂ) (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))
      = -(2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ)) := by
    simp only [map_mul, map_pow, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast, map_ofNat]
    ring
  rw [map_inv₀, h1, inv_neg]

/-- **`lem_WI_K`, `(WI_calK)`**, both charge orders (pin `KLwardPin`,
`64b58eb:RBM3D/Probe/T2004Pins.lean:770-779`; the type is the body of the pin): for
`σ = (s, μ, -s)`, `n = |μ| + 2 ≥ 2`,
`∑_{a_n} 𝒦^{(n)}_{t,σ,a} = (2 i W^d η_t)⁻¹ (𝒦^{(n-1)}_{t,(+,μ),â} - 𝒦^{(n-1)}_{t,(-,μ),â})`,
`η_t = (1 - t) Im m(E)`.  For `s = +` this is the port of `Kcal_ward`; for `s = -` it follows by
complex conjugation (`KLWard_flip`). -/
theorem KLK_ward :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
        ∑ x : Zd d L, KLK d L g W E t ⟨s :: μ ++ [!s], a ++ [x]⟩
          = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
              (KLK d L g W E t ⟨true :: μ, a⟩ - KLK d L g W E t ⟨false :: μ, a⟩) := by
  intro d L W _ g E hL hW hE t ht0 ht1 s μ a ha
  have ht : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht0, ht1⟩
  cases s with
  | true => exact KLWard_pos d L g hL W hW hE ht μ a ha
  | false =>
    set μ' : List Bool := μ.map not with hμ'
    have hlen' : a.length = μ'.length + 1 := by rw [hμ', List.length_map]; exact ha
    have hpos := KLWard_pos d L g hL W hW hE ht μ' a hlen'
    have hμμ : μ'.map not = μ := by simp [hμ', List.map_map, Function.comp_def]
    have f1 : ∀ x : Zd d L, KLK d L g W E t ⟨false :: μ ++ [!false], a ++ [x]⟩
        = (starRingEnd ℂ) (KLK d L g W E t ⟨true :: μ' ++ [false], a ++ [x]⟩) := by
      intro x
      have h := KLWard_flip d L W g E hL hW hE t ht (true :: μ' ++ [false]) (a ++ [x])
        (by simp; omega) (by simp)
      rwa [show (true :: μ' ++ [false]).map not = false :: μ ++ [!false] by simp [hμμ]] at h
    have f2 : KLK d L g W E t ⟨true :: μ, a⟩
        = (starRingEnd ℂ) (KLK d L g W E t ⟨false :: μ', a⟩) := by
      have h := KLWard_flip d L W g E hL hW hE t ht (false :: μ') a (by simp; omega) (by omega)
      rwa [show (false :: μ').map not = true :: μ by simp [hμμ]] at h
    have f3 : KLK d L g W E t ⟨false :: μ, a⟩
        = (starRingEnd ℂ) (KLK d L g W E t ⟨true :: μ', a⟩) := by
      have h := KLWard_flip d L W g E hL hW hE t ht (true :: μ') a (by simp; omega) (by omega)
      rwa [show (true :: μ').map not = false :: μ by simp [hμμ]] at h
    calc ∑ x : Zd d L, KLK d L g W E t ⟨false :: μ ++ [!false], a ++ [x]⟩
        = ∑ x : Zd d L, (starRingEnd ℂ) (KLK d L g W E t ⟨true :: μ' ++ [false], a ++ [x]⟩) :=
          Finset.sum_congr rfl fun x _ => f1 x
      _ = (starRingEnd ℂ) (∑ x : Zd d L, KLK d L g W E t ⟨true :: μ' ++ [false], a ++ [x]⟩) :=
          (map_sum _ _ _).symm
      _ = (starRingEnd ℂ) ((2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
            (KLK d L g W E t ⟨true :: μ', a⟩ - KLK d L g W E t ⟨false :: μ', a⟩)) := by
          rw [hpos]
      _ = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
            (KLK d L g W E t ⟨true :: μ, a⟩ - KLK d L g W E t ⟨false :: μ, a⟩) := by
          rw [map_mul, map_sub, KLWard_conj_kappa d W E t, ← f3, ← f2]
          ring

end Main

/-! ## 7. The compiled instances: `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`

`L = 5` (`125` blocks), `W = 2` (`W^d = 8`, `N = (WL)^3 = 1000`), `m(+) = i`, `η_t = 1/10`.  Every
deterministic hypothesis of `KLK_ward` and `KLWard_flip` (`3 ≤ 5`, `1 ≤ 2`, `|0| < 2`,
`0 ≤ 9/10 < 1`, `a.length = μ.length + 1`, well-formedness, `1 ≤ length`) is discharged; the
loops have distinct labels.  `KLWardInst_ward_true`, `KLWardInst_ward_false` are the data of the
probe `KLinst_ward` (`64b58eb:RBM3D/Probe/T2004Pins.lean:1026-1034`): `s = ±`, `μ = [-]`, `a = (0, 1)`,
`n = 3`. -/

section Instances

/-- `KLK_ward` at `s = +`, `μ = [-]`, `a = (0, 1)` (`n = 3`): `∑_x 𝒦_{(+,-,-),(0,1,x)}`. -/
theorem KLWardInst_ward_true :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false] ++ [!true], [0, 1] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false], [0, 1]⟩
            - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false], [0, 1]⟩) := by
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) true [false] [0, 1] rfl

/-- `KLK_ward` at `s = -`, `μ = [-]`, `a = (0, 1)` (`n = 3`): `∑_x 𝒦_{(-,-,+),(0,1,x)}`. -/
theorem KLWardInst_ward_false :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false] ++ [!false], [0, 1] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false], [0, 1]⟩
            - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false], [0, 1]⟩) := by
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) false [false] [0, 1] rfl

/-- `KLK_ward` at `n = 2` (`μ = []`), `s = -`, `a = (0)`: `∑_x 𝒦_{(-,+),(0,x)}`. -/
theorem KLWardInst_ward_two_false :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [] ++ [!false], [0] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [], [0]⟩
            - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [], [0]⟩) := by
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) false [] [0] rfl

/-- `KLK_ward` at `n = 4` (`μ = [+, -]`), `s = -`, `a = (0, 1, 2)`: `∑_x 𝒦_{(-,+,-,+),(0,1,2,x)}`. -/
theorem KLWardInst_ward_four_false :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10)
        ⟨false :: [true, false] ++ [!false], [0, 1, 2] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [true, false], [0, 1, 2]⟩
            - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [true, false], [0, 1, 2]⟩) := by
  simpa using KLK_ward 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) false [true, false] [0, 1, 2] rfl

/-- `KLWard_flip` at `n = 3`: `𝒦_{(-,+,-),(0,1,2)} = conj 𝒦_{(+,-,+),(0,1,2)}`. -/
theorem KLWardInst_flip :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false, true, false], [0, 1, 2]⟩
      = (starRingEnd ℂ) (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩) := by
  simpa using KLWard_flip 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (9 / 10)
    ⟨by norm_num, by norm_num⟩ [true, false, true] [0, 1, 2] rfl (by simp)

end Instances

end RBM.Loop
