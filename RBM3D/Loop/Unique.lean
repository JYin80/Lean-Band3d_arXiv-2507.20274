/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.Primitive
import RBM3D.Loop.KLTreeDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Fintype.Vector

/-!
# Uniqueness for the convolution tree equations

`\Cref{Def_Ktza}` calls `K` *the* family of `K`-loops.  This file proves the uniqueness
half of that: two families solving `(pro_dyncalK)` with the same initial values agree.
Existence is the tree formula `(eq_Ktree)` and is not proved here.

## The structure of `(pro_dyncalK)`

Every term at a loop of length `n` is a product of the values at two shorter chains, of
lengths `k + n - l + 1` and `l - k + 1`.  Both lie in `[2, n]` and they add up to `n + 2`
(`RBM.Loop.LoopIdx.length_cutGlueL_add_length_cutGlueR`).  Hence:

* if one chain has the full length `n`, the other has length `2`
  (`length_cutGlueR_eq_two`, `length_cutGlueL_eq_two`);
* so for `n ≥ 3`, once the lengths `< n` are fixed, the equation at length `n` is
  **linear** in the length-`n` unknowns, with coefficients given by the `2`-loops;
* for `n = 2` both chains have length `2` and the equation is quadratic (Riccati).

## The argument

One Grönwall argument covers both cases.  Fix `n` and assume the two families agree on all
loops of length `< n`.  Let `D` be their difference at length `n`.  Each term differs by
`(X - X') s Y + X' s (Y - Y')`; a difference `X - X'` vanishes unless its chain has length
`n`, and then the other factor is a `2`-loop.  So a bound `R` on the `2`-loops gives
`‖D'‖ ≤ C ‖D‖`, and `D(0) = 0` forces `D = 0`
(`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`).  Strong induction on `n`
finishes.  At `n = 2` the hypothesis on shorter loops is vacuous and the same estimate is
the Lipschitz bound for the Riccati right-hand side.

`d` never enters the argument: it only sits in the label type `Zd d L` and in the prefactor
`W^d` of `(pro_dyncalK)`.

## Main results

* `RBM.Loop.eq_on_levelS`     : one step of the induction, over a kernel `S` with `‖S a b‖ ≤ 1`
* `RBM.Loop.uniqS_holds`      : **two `IsKLoopS` families (any kernel `S` with `‖S a b‖ ≤ 1`,
  any initial data `M`) on `[0, T₀]` whose `2`-loops are bounded agree on every loop**
  (the pin `UniqS`)
* `RBM.Loop.retireS_holds`    : the a priori bound of the `2`-loops on `[0, T₀]`, `T₀ < 1`, over any
  `S`, `M` (the pin `RetireS`)
* `RBM.Loop.eq_on_level`, `RBM.Loop.isKLoop_unique`, `RBM.Loop.KLretire_twoLoopBounded` : the band
  statements (`S = SB d L g`, `M = MLoop`), now wrappers of the three above
* `RBM.Loop.eq_kTwo_of_isKLoop` : with `(Kn2sol)`'s explicit solution as the comparison
  family, this **discharges `RBM.Loop.KTwoFormula`** -- see `Loop/Primitive.lean`
-/

set_option linter.style.longLine false

namespace RBM.Loop

namespace LoopIdx

variable {α : Type*} (x : LoopIdx α) (a b : α) {k l : ℕ}

/-- Every chain produced by a cut has length at least `2`. -/
theorem two_le_length_cutGlueL (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    2 ≤ (x.cutGlueL k l b).length := by
  rw [length_cutGlueL x b hk hkl hl]; omega

theorem two_le_length_cutGlueR (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    2 ≤ (x.cutGlueR k l b).length := by
  rw [length_cutGlueR x b hk hkl hl]; omega

/-- **Structure of `(pro_dyncalK)`.**  If the left chain has the full length `n`, the right
chain is a `2`-loop. -/
theorem length_cutGlueR_eq_two (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueL k l a).length = x.length) : (x.cutGlueR k l b).length = 2 := by
  rw [length_cutGlueL x a hk hkl hl] at h
  rw [length_cutGlueR x b hk hkl hl]
  omega

/-- **Structure of `(pro_dyncalK)`.**  If the right chain has the full length `n`, the left
chain is a `2`-loop. -/
theorem length_cutGlueL_eq_two (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length)
    (h : (x.cutGlueR k l b).length = x.length) : (x.cutGlueL k l a).length = 2 := by
  rw [length_cutGlueR x b hk hkl hl] at h
  rw [length_cutGlueL x a hk hkl hl]
  omega

end LoopIdx

/-! ### The generic pins (gate BA, stage K, ticket T2366) -/

/-- **`UniqS`** (verbatim: probe `t/T2360:RBM3D/Probe/T2360Pins.lean:232`): uniqueness of `K`-loops over `IsKLoopS`; the
only fact about `S` is `‖S a b‖ ≤ 1`. -/
def UniqS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ),
    (∀ a b, ‖S a b‖ ≤ 1) → ∀ {T : Set ℝ} {K K' : ℝ → LoopIdx (Zd d L) → ℂ},
      IsKLoopS d L W S m M T K → IsKLoopS d L W S m M T K' → ∀ {T₀ R : ℝ}, Set.Icc 0 T₀ ⊆ T → 0 ≤ R →
      (∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) →
      ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I

/-- **`RetireS`**: `KLretire_twoLoopBounded` over `IsKLoopS` (continuity on `[0, T₀] ⊆ [0,1)`; no fact about `S`). -/
def RetireS : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}, IsKLoopS d L W S m M (Set.Ico 0 1) K →
    ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R

open Finset
open scoped Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ)

/-- Loops of length `n`, as a finite type. -/
abbrev LoopVec (n : ℕ) := List.Vector Bool n × List.Vector (Zd d L) n

/-- The loop with given charges and labels. -/
def LoopVec.toLoop {n : ℕ} (p : LoopVec d L n) : LoopIdx (Zd d L) := ⟨p.1.1, p.2.1⟩

variable {d L}

omit [NeZero L] in
theorem LoopVec.wf {n : ℕ} (p : LoopVec d L n) : (p.toLoop d L).WF := by
  change p.1.1.length = p.2.1.length
  rw [p.1.2, p.2.2]

omit [NeZero L] in
theorem LoopVec.length {n : ℕ} (p : LoopVec d L n) : (p.toLoop d L).length = n := p.2.2

omit [NeZero L] in
theorem LoopVec.exists_toLoop {n : ℕ} (J : LoopIdx (Zd d L)) (hJ : J.WF) (hJn : J.length = n) :
    ∃ p : LoopVec d L n, p.toLoop d L = J :=
  ⟨(⟨J.σ, hJ.trans hJn⟩, ⟨J.a, hJn⟩), rfl⟩

theorem norm_SB_apply_le (hL : 3 ≤ L) (a b : Zd d L) : ‖SB d L g a b‖ ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => ‖SB d L g a b‖₊) (fun _ _ => by positivity)
    (Finset.mem_univ b)
  rw [sum_nnnorm_SB_row d L g hL a] at h
  exact_mod_cast h

/-- The difference of one term: `X s Y - X' s Y' = (X - X') s Y + X' s (Y - Y')`. -/
theorem norm_mul_mul_sub_le {X X' Y Y' s : ℂ} {R D : ℝ} (hs : ‖s‖ ≤ 1)
    (h1 : ‖X - X'‖ * ‖Y‖ ≤ R * D) (h2 : ‖X'‖ * ‖Y - Y'‖ ≤ R * D) :
    ‖X * s * Y - X' * s * Y'‖ ≤ 2 * (R * D) := by
  have e : X * s * Y - X' * s * Y' = (X - X') * s * Y + X' * s * (Y - Y') := by ring
  have e1 : ‖(X - X') * s * Y‖ ≤ R * D := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg (X - X')) (norm_nonneg Y))
    nlinarith
  have e2 : ‖X' * s * (Y - Y')‖ ≤ R * D := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg X') (norm_nonneg (Y - Y')))
    nlinarith
  rw [e]
  linarith [norm_add_le ((X - X') * s * Y) (X' * s * (Y - Y'))]

variable (d L)

/-- **One step of the induction, over a general kernel.**  Two functions satisfying `(pro_dyncalK)` with
the kernel `S` (`‖S a b‖ ≤ 1`) at length `n` on `[0, T₀]`, whose `2`-loops are bounded by `R`, which agree on all
loops of length `< n` and at `t = 0` at length `n`, agree at length `n`. -/
theorem eq_on_levelS (S : Matrix (Zd d L) (Zd d L) ℂ) (hS : ∀ a b, ‖S a b‖ ≤ 1)
    (K K' : ℝ → LoopIdx (Zd d L) → ℂ) (T₀ R : ℝ)
    (n : ℕ) (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = n →
      HasDerivAt (fun s => K s I) (treeEqRhsS d L W S (K t) I) t)
    (hK' : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = n →
      HasDerivAt (fun s => K' s I) (treeEqRhsS d L W S (K' t) I) t)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      I.length < n → K t I = K' t I)
    (h0 : ∀ I : LoopIdx (Zd d L), I.WF → I.length = n → K 0 I = K' 0 I) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = n → K t I = K' t I := by
  let D : ℝ → LoopVec d L n → ℂ := fun t p => K t (p.toLoop d L) - K' t (p.toLoop d L)
  let D' : ℝ → LoopVec d L n → ℂ := fun t p =>
    treeEqRhsS d L W S (K t) (p.toLoop d L) - treeEqRhsS d L W S (K' t) (p.toLoop d L)
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := fun t ht =>
    hasDerivAt_pi.2 fun p =>
      (hK t ht _ p.wf p.length).sub (hK' t ht _ p.wf p.length)
  let C : ℝ := (W : ℝ) ^ d * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n,
    ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * R
  have hC : 0 ≤ C := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
      fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have hdiff : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ‖K t J - K' t J‖ ≤ ‖D t‖ := by
      intro J hJ h2 hle
      rcases hle.lt_or_eq with hlt | heq
      · rw [hlow t ht' J hJ h2 hlt, sub_self, norm_zero]
        exact norm_nonneg _
      · obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop J hJ heq
        exact norm_le_pi_norm (D t) p
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).2 fun p => ?_
    set I := p.toLoop d L with hIdef
    have hI : I.WF := p.wf
    have hIn : I.length = n := p.length
    have hterm : ∀ k ∈ Icc 1 n, ∀ l ∈ Ioc k n, ∀ a b : Zd d L,
        ‖K t (I.cutGlueL k l a) * S a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * S a b * K' t (I.cutGlueR k l b)‖
          ≤ 2 * (R * ‖D t‖) := by
      intro k hk l hl a b
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Ioc] at hl
      have hk1 : 1 ≤ k := hk.1
      have hkl : k < l := hl.1
      have hlI : l ≤ I.length := hIn ▸ hl.2
      have hWL : (I.cutGlueL k l a).WF := LoopIdx.wf_cutGlueL I a hI hk1 hkl hlI
      have hWR : (I.cutGlueR k l b).WF := LoopIdx.wf_cutGlueR I b hI hk1 hkl hlI
      have h2L := LoopIdx.two_le_length_cutGlueL I a hk1 hkl hlI
      have h2R := LoopIdx.two_le_length_cutGlueR I b hk1 hkl hlI
      have hLle : (I.cutGlueL k l a).length ≤ n :=
        hIn ▸ LoopIdx.length_cutGlueL_le I a hk1 hkl hlI
      have hRle : (I.cutGlueR k l b).length ≤ n :=
        hIn ▸ LoopIdx.length_cutGlueR_le I b hk1 hkl hlI
      have hRD : 0 ≤ R * ‖D t‖ := mul_nonneg hR0 (norm_nonneg _)
      refine norm_mul_mul_sub_le (hS a b) ?_ ?_
      · rcases hLle.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWL h2L hlt, sub_self, norm_zero, zero_mul]
          exact hRD
        · have h2 := LoopIdx.length_cutGlueR_eq_two I a b hk1 hkl hlI (heq.trans hIn.symm)
          have hY := (hR t ht' _ hWR h2).1
          have hX := hdiff _ hWL h2L hLle
          rw [mul_comm R]
          exact mul_le_mul hX hY (norm_nonneg _) (norm_nonneg _)
      · rcases hRle.lt_or_eq with hlt | heq
        · rw [hlow t ht' _ hWR h2R hlt, sub_self, norm_zero, mul_zero]
          exact hRD
        · have h2 := LoopIdx.length_cutGlueL_eq_two I a b hk1 hkl hlI (heq.trans hIn.symm)
          have hX := (hR t ht' _ hWL h2).2
          have hY := hdiff _ hWR h2R hRle
          exact mul_le_mul hX hY (norm_nonneg _) hR0
    have e : D' t p = ((W : ℂ) ^ d) * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n,
        ∑ a : Zd d L, ∑ b : Zd d L,
        (K t (I.cutGlueL k l a) * S a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * S a b * K' t (I.cutGlueR k l b)) := by
      simp only [D', treeEqRhsS, ← hIdef, hIn, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [e, norm_mul, norm_pow, Complex.norm_natCast]
    have hsum : ‖∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ a : Zd d L, ∑ b : Zd d L,
        (K t (I.cutGlueL k l a) * S a b * K t (I.cutGlueR k l b)
          - K' t (I.cutGlueL k l a) * S a b * K' t (I.cutGlueR k l b))‖
        ≤ ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : Zd d L, ∑ _b : Zd d L, 2 * (R * ‖D t‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact hterm k hk l hl a b
    calc (W : ℝ) ^ d * ‖_‖
        ≤ (W : ℝ) ^ d * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, ∑ _a : Zd d L, ∑ _b : Zd d L,
          2 * (R * ‖D t‖) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = C * ‖D t‖ := by
        simp only [C, Finset.sum_mul, mul_assoc]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (funext fun p => sub_eq_zero.2 (h0 _ p.wf p.length)) hbound
  intro t ht I hI hIn
  obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop I hI hIn
  exact sub_eq_zero.1 (congrFun (hzero t ht) p)

/-- **One step of the induction** (`S = S^{(B)}`).  Two functions satisfying `(pro_dyncalK)` at length `n`
on `[0, T₀]`, whose `2`-loops are bounded by `R`, which agree on all loops of length `< n`
and at `t = 0` at length `n`, agree at length `n`.  The wrapper of `eq_on_levelS` at `S = SB d L g`. -/
theorem eq_on_level (hL : 3 ≤ L) (K K' : ℝ → LoopIdx (Zd d L) → ℂ) (T₀ R : ℝ)
    (n : ℕ) (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = n →
      HasDerivAt (fun s => K s I) (treeEqRhs d L W g (K t) I) t)
    (hK' : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = n →
      HasDerivAt (fun s => K' s I) (treeEqRhs d L W g (K' t) I) t)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      I.length < n → K t I = K' t I)
    (h0 : ∀ I : LoopIdx (Zd d L), I.WF → I.length = n → K 0 I = K' 0 I) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = n → K t I = K' t I :=
  eq_on_levelS d L W (SB d L g) (norm_SB_apply_le g hL) K K' T₀ R n hR0 hK hK' hR hlow h0

variable {d L W g}

/-- **Uniqueness for `\Cref{Def_Ktza}`, over a general kernel** (the pin `UniqS`).  Two `IsKLoopS` families
on `[0, T₀]` (same `W`, `S`, `m`, `M`) whose `2`-loops stay bounded agree on every loop of length `≥ 2`.
The bound is needed only on `2`-loops: by the structure lemma they are the only coefficients of the linear
equations at higher length.  The only fact about `S` is `‖S a b‖ ≤ 1`. -/
theorem uniqS_holds : UniqS := by
  intro d L W _ S m M hS T K K' hK hK' T₀ R hT hR0 hR
  have main : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      I.length = n → K t I = K' t I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht I hI h2 hIn
      have hn : 2 ≤ n := hIn ▸ h2
      refine eq_on_levelS d L W S hS K K' T₀ R n hR0
        (fun s hs J hJ hJn => hK.1 s (hT hs) J hJ (hJn ▸ hn))
        (fun s hs J hJ hJn => hK'.1 s (hT hs) J hJ (hJn ▸ hn)) hR ?_ ?_ t ht I hI hIn
      · intro s hs J hJ hJ2 hJn
        exact ih _ hJn s hs J hJ hJ2 rfl
      · intro J hJ hJn
        rw [hK.2.1 J hJ (hJn ▸ hn), hK'.2.1 J hJ (hJn ▸ hn)]
  exact fun t ht I hI h2 => main _ t ht I hI h2 rfl

/-- **Uniqueness for `\Cref{Def_Ktza}`.**  Two families of `K`-loops on `[0, T₀]` (same `W`,
`g`, `m`) whose `2`-loops stay bounded agree on every loop of length `≥ 2`.  The bound is
needed only on `2`-loops: by the structure lemma they are the only coefficients of the
linear equations at higher length.  `uniqS_holds` at `S = SB d L g`, `M = MLoop`. -/
theorem isKLoop_unique (hL : 3 ≤ L) (m : Bool → ℂ) {T : Set ℝ}
    {K K' : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g m T K)
    (hK' : IsKLoop d L W g m T K') {T₀ R : ℝ} (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 →
      ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I :=
  uniqS_holds d L W (SB d L g) m (MLoop d L W m) (norm_SB_apply_le g hL) hK hK' hT hR0 hR

/-! ### Discharging `(Kn2sol)`

`RBM.Loop.KTwoFormula` -- the shape of the `2`-loops -- is not an input: uniqueness at
length `2` plus the explicit solution of `Loop/Primitive.lean` prove it, given an a priori
bound on the `2`-loops of the family at hand.  That bound is the only thing still asked
for, and it is of the kind the paper establishes along the way rather than borrows.
-/

omit [NeZero L] in
/-- A well-formed loop of length `2` is `⟨[σ₁, σ₂], [a₁, a₂]⟩`. -/
theorem exists_eq_of_length_two {I : LoopIdx (Zd d L)} (hI : I.WF) (h2 : I.length = 2) :
    ∃ (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L), I = ⟨[σ₁, σ₂], [a₁, a₂]⟩ := by
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 2 := h2
  have hσ : σ.length = 2 := hI.trans ha
  obtain ⟨a₁, a₂, rfl⟩ := List.length_eq_two.mp ha
  obtain ⟨σ₁, σ₂, rfl⟩ := List.length_eq_two.mp hσ
  exact ⟨σ₁, σ₂, a₁, a₂, rfl⟩

/-- **The a priori bound on the `2`-loops is a theorem** for every family of `K`-loops on `[0,1)`
over a general kernel `S` and general initial data `M` (the pin `RetireS`): each coordinate `s ↦ K s I`
has a derivative, hence is continuous on the compact `[0,T₀] ⊆ [0,1)`, and there are finitely many
`2`-loops (port of `RBM2D/Loop/Unique.lean:250-268`, c9a24cf; moved here from `Loop/KLUnique.lean` by
ticket T2127).  No fact about `S`, `m` or `M` is used.  The conclusion is the unfolded bound: for every
`T₀ < 1` there is `R ≥ 0` with `‖K t I‖ ≤ R` for all `t ∈ [0,T₀]` and all well-formed loops of
length `2`. -/
theorem retireS_holds : RetireS := by
  intro d L W _ S m M K hK T₀ hT₀
  let f : ℝ → LoopVec d L 2 → ℂ := fun s p => K s (p.toLoop d L)
  have hf : ContinuousOn f (Set.Icc 0 T₀) := by
    refine continuousOn_pi.2 fun p s hs => ?_
    have := hK.1 s ⟨hs.1, lt_of_le_of_lt hs.2 hT₀⟩ (p.toLoop d L) p.wf (by rw [p.length])
    exact this.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨max C 0, le_max_right _ _, fun t ht I hI hI2 => ?_⟩
  obtain ⟨p, rfl⟩ := LoopVec.exists_toLoop I hI hI2
  exact ((norm_le_pi_norm (f t) p).trans (hC t ht)).trans (le_max_left _ _)

/-- **The a priori bound on the `2`-loops is a theorem** for every family of `K`-loops on `[0,1)`
(`retireS_holds` at `S = SB d L g`, `M = MLoop`): for every `T₀ < 1` there is `R ≥ 0` with
`‖K t I‖ ≤ R` for all `t ∈ [0,T₀]` and all well-formed loops of length `2`. -/
theorem KLretire_twoLoopBounded {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoop d L W g m (Set.Ico 0 1) K) :
    ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R :=
  retireS_holds d L W (SB d L g) m (MLoop d L W m) hK

/-- **`(Kn2sol)` is a theorem about every family of `K`-loops, not a hypothesis.**

If `K` is a family of `K`-loops on `[0,1)`, then `RBM.Loop.KTwoFormula` holds of it: its `2`-loops
*are* `W^{-d}m(σ₁)m(σ₂)Θ_{t m(σ₁)m(σ₂)}`.  The a priori bound of its `2`-loops on each `[0,T₀]`,
`T₀ < 1`, is `KLretire_twoLoopBounded`.

The proof compares `K` with `RBM.Loop.kTwoLoop` at length `2` only (`eq_on_level` with
`n = 2`, where the hypothesis on shorter loops is vacuous): both solve the same Riccati
equation and both take the `M`-loop value at `t = 0`. -/
theorem kTwoFormula_of_isKLoop (hL : 3 ≤ L) (hW : (W : ℂ) ^ d ≠ 0) {m : Bool → ℂ}
    (hm : ∀ s, ‖m s‖ = 1) {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoop d L W g m (Set.Ico 0 1) K) :
    KTwoFormula d L W g m K := by
  intro t ht0 ht1 σ₁ σ₂ a₁ a₂
  obtain ⟨R, hR0, hRK⟩ := KLretire_twoLoopBounded hK t ht1
  set R' : ℝ := max R (‖((W : ℂ) ^ d)⁻¹‖ * (1 - t)⁻¹) with hR'
  have hR'0 : 0 ≤ R' := le_trans hR0 (le_max_left _ _)
  have hsub : ∀ s ∈ Set.Icc (0 : ℝ) t, s ∈ Set.Ico (0 : ℝ) 1 := fun s hs =>
    ⟨hs.1, lt_of_le_of_lt hs.2 ht1⟩
  have hS : ‖SB d L g‖ = 1 := norm_SB d L g hL
  -- the comparison family: the explicit solution
  have hderiv' : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 →
      HasDerivAt (fun u => kTwoLoop d L W g m u I)
        (treeEqRhs d L W g (kTwoLoop d L W g m s) I) s := by
    intro s hs I hI h2
    obtain ⟨τ₁, τ₂, b₁, b₂, rfl⟩ := exists_eq_of_length_two hI h2
    exact hasDerivAt_kTwoLoop hS hW m τ₁ τ₂
      (norm_mul_lt_one (hm τ₁) (hm τ₂) hs.1 (lt_of_le_of_lt hs.2 ht1)) b₁ b₂
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 →
      ‖K s I‖ ≤ R' ∧ ‖kTwoLoop d L W g m s I‖ ≤ R' := by
    intro s hs I hI h2
    refine ⟨le_trans (hRK s hs I hI h2) (le_max_left _ _), ?_⟩
    obtain ⟨τ₁, τ₂, b₁, b₂, rfl⟩ := exists_eq_of_length_two hI h2
    have hs1 : s < 1 := lt_of_le_of_lt hs.2 ht1
    have hmono : (1 - s)⁻¹ ≤ (1 - t)⁻¹ := by
      have h1 : (0 : ℝ) < 1 - t := by linarith
      have h2' : (0 : ℝ) < 1 - s := by linarith
      exact inv_anti₀ h1 (by linarith [hs.2])
    refine le_trans ?_ (le_max_right R _)
    refine le_trans (norm_kTwo_le hL (hm τ₁) (hm τ₂) hs.1 hs1 b₁ b₂) ?_
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  have key := eq_on_level d L W g hL K (kTwoLoop d L W g m) t R' 2 hR'0
    (fun s hs I hI h2 => hK.1 s (hsub s hs) I hI (by omega))
    hderiv' hbound
    (fun s _ I _ h2 hlt => absurd hlt (by omega))
    (fun I hI h2 => by
      obtain ⟨τ₁, τ₂, b₁, b₂, rfl⟩ := exists_eq_of_length_two hI h2
      rw [hK.2.1 _ hI (by omega), kTwoLoop_zero])
  have := key t ⟨ht0, le_refl t⟩ ⟨[σ₁, σ₂], [a₁, a₂]⟩ rfl rfl
  rw [this]
  rfl

/-- **`res_pureKes` at `n = 2` for an arbitrary family of `K`-loops.**  Combining the two
previous results with `pureLoop_two`: no assumption about the shape of the `2`-loops is
left (and none about their size), only `ThetaDecayShort`, which the paper genuinely borrows. -/
theorem pureLoop_two_of_isKLoop {k : ℕ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hL : 3 ≤ L)
    (hW : (W : ℂ) ^ (k + 2) ≠ 0) {m : Bool → ℂ} (hm : ∀ s, ‖m s‖ = 1) {σ : Bool}
    (hmi : 0 < (m σ).im) (hshort : ThetaDecayShort (k + 2) g (m σ))
    {K : ℝ → LoopIdx (Zd (k + 2) L) → ℂ} (hK : IsKLoop (k + 2) L W g m (Set.Ico 0 1) K) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (k + 2) L,
      ‖K t ⟨[σ, σ], [a₁, a₂]⟩‖
        ≤ C * ‖((W : ℂ) ^ (k + 2))⁻¹‖
          * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ))) :=
  pureLoop_two hd hg hL (hm σ) hmi hshort (kTwoFormula_of_isKLoop hL hW hm hK)

/-! ### Instances (T2366): `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`

Kernel `S = S^{(B)} = SB 3 5 (1/2)` (`125` blocks, `‖S a b‖ ≤ 1` from `3 ≤ 5`), initial data `M = MLoop`,
`m = mSigma 0` (`m(+) = i`), family `K = 𝒦` (the merged instance `KLTreeDerivInst_isKLoop` of
`KLK_isKLoop`).  Every deterministic hypothesis of `retireS_holds` and `uniqS_holds` is discharged. -/

/-- `retireS_holds` at the instance data: the bound of the `2`-loops of `𝒦` on `[0, 9/10]`. -/
theorem UniqueInst_retireS :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) (9 / 10), ∀ I : LoopIdx (Zd 3 5), I.WF → I.length = 2 →
      ‖KLK 3 5 (1 / 2) 2 0 t I‖ ≤ R :=
  retireS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
    (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) KLTreeDerivInst_isKLoop (9 / 10) (by norm_num)

/-- `uniqS_holds` at the instance data, with the bound `R` of `UniqueInst_retireS` (two copies of the family
`𝒦`; the family `𝒦 ∘ shift_{e₁}`, different as a function, is `KLUniqueInst_uniqS_shifted`). -/
theorem UniqueInst_uniqS :
    ∀ t ∈ Set.Icc (0 : ℝ) (9 / 10), ∀ I : LoopIdx (Zd 3 5), I.WF → 2 ≤ I.length →
      KLK 3 5 (1 / 2) 2 0 t I = KLK 3 5 (1 / 2) 2 0 t I := by
  obtain ⟨R, hR0, hR⟩ := UniqueInst_retireS
  exact uniqS_holds 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoop 3 5 2 (mSigma 0))
    (norm_SB_apply_le (1 / 2) (by norm_num))
    (K := fun t I => KLK 3 5 (1 / 2) 2 0 t I) (K' := fun t I => KLK 3 5 (1 / 2) 2 0 t I)
    KLTreeDerivInst_isKLoop KLTreeDerivInst_isKLoop (T₀ := 9 / 10) (R := R)
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩) hR0
    (fun t ht I hI h2 => ⟨hR t ht I hI h2, hR t ht I hI h2⟩)

end RBM.Loop
