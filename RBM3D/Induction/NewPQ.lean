/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.KLWard

set_option linter.style.longLine false

/-!
# S3-03 (ticket T2086): `lem: newPQ`, the Ward expansions `(yurenAL)`, `(yurenAK)` of the zero-mode operator

Proves the pin `RBM.Gauss.Sizes.STNewPQ` (`RBM3D/Induction/Step34Pins.lean:330`) as
`stNewPQ_holds`.  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`),
`lem: newPQ` `3_5:1482-1507`, the proof `3_5:1866-1886`, Ward's identities `(WI_calL)`, `(WI_calK)`
(`paper/tex/1_2_Intro_model_result.tex:1036-1042`).  No RBM2D source (portmap: "new (paper lines)").

* §1 the operators: `Q^(i)`, `P^(i)` commute, `Q^(insert i A) = Q^(i) Q^(A)`, linearity, and the
  reindexing of `Q^(A)` along an injection of index sets.
* §2 loops: cyclic invariance of `𝓛` (trace cyclicity) and the Ward identity for `𝓛` at the last
  index for **both** charge orders `σ₁ = ±`, `σ_n = ∓` (the merged `sum_gloop_ward_last_div` has
  `σ₁ = +`; the other order is its image under `z ↦ z̄`); for `𝒦` the merged `KLK_rotate`, `KLK_ward`.
* §3 the Ward step at an interior index `i` (`σ_i ≠ σ_{i+1}`, cyclic): rotate `i` to the last
  position by `ρ^(i+1)`, `ρ = finRotate`, apply the last-index Ward identity, keep the labels of the
  rotated loop (`ι = ρ^(i+1) ∘ castSucc`, the paper's `ι_i` up to a cyclic relabelling).
* §4 the induction on `m` and on `#(I_diff(σ) \ A)`, one Ward step per index; the data
  `(k_α, ξ_α, σ_α, ι_α, A_α)` are a `List` of records independent of `L`, `W`, the sample and `E`, `τ`.
* §5 `stNewPQ_holds`; §6 a compiled instance at `d = 3` (`sz0`).
-/

noncomputable section

open Finset Function Matrix

namespace RBM

/-! ## 1. The operators `P^(i)`, `Q^(i)`, `Q^(A)` -/

section Operators

variable {d L : ℕ} [NeZero L] {N : ℕ}

private theorem npq_avgOp_sub (i : Fin N) (f g : (Fin N → Zd d L) → ℂ) (a : Fin N → Zd d L) :
    avgOp d L i (fun b => f b - g b) a = avgOp d L i f a - avgOp d L i g a := by
  simp only [avgOp, Finset.sum_sub_distrib, mul_sub]

private theorem npq_avgOp_mul (i : Fin N) (c : ℂ) (f : (Fin N → Zd d L) → ℂ)
    (a : Fin N → Zd d L) :
    avgOp d L i (fun b => c * f b) a = c * avgOp d L i f a := by
  simp only [avgOp, ← Finset.mul_sum]
  ring

private theorem npq_avgOp_comm (i j : Fin N) (hij : i ≠ j) (f : (Fin N → Zd d L) → ℂ)
    (a : Fin N → Zd d L) :
    avgOp d L i (avgOp d L j f) a = avgOp d L j (avgOp d L i f) a := by
  simp only [avgOp, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_))
  rw [Function.update_comm hij.symm]

private theorem npq_zmo_comm (i j : Fin N) (f : (Fin N → Zd d L) → ℂ) :
    zeroModeOp d L i (zeroModeOp d L j f) = zeroModeOp d L j (zeroModeOp d L i f) := by
  by_cases hij : i = j
  · subst hij; rfl
  funext a
  have h1 : avgOp d L i (zeroModeOp d L j f) a
      = avgOp d L i f a - avgOp d L i (avgOp d L j f) a := npq_avgOp_sub i f _ a
  have h2 : avgOp d L j (zeroModeOp d L i f) a
      = avgOp d L j f a - avgOp d L j (avgOp d L i f) a := npq_avgOp_sub j f _ a
  simp only [zeroModeOp]
  rw [h1, h2, npq_avgOp_comm i j hij]
  ring

private theorem npq_avg_zmo (i j : Fin N) (hij : i ≠ j) (f : (Fin N → Zd d L) → ℂ) :
    avgOp d L i (zeroModeOp d L j f) = zeroModeOp d L j (avgOp d L i f) := by
  funext a
  rw [show zeroModeOp d L j f = fun b => f b - avgOp d L j f b from rfl]
  simp only [zeroModeOp]
  rw [npq_avgOp_sub, npq_avgOp_comm i j hij]

private theorem npq_zms_empty (f : (Fin N → Zd d L) → ℂ) : zeroModeSet d L ∅ f = f := by
  simp [zeroModeSet]

private theorem npq_zms_insert {j : Fin N} {A : Finset (Fin N)} (hj : j ∉ A)
    (f : (Fin N → Zd d L) → ℂ) :
    zeroModeSet d L (insert j A) f = zeroModeOp d L j (zeroModeSet d L A f) := by
  have : LeftCommutative (fun (i : Fin N) (g : (Fin N → Zd d L) → ℂ) => zeroModeOp d L i g) :=
    ⟨fun i j g => npq_zmo_comm i j g⟩
  unfold zeroModeSet
  rw [(Finset.toList_insert hj).foldr_eq, List.foldr_cons]

private theorem npq_avg_zms (i : Fin N) (A : Finset (Fin N)) (hi : i ∉ A)
    (f : (Fin N → Zd d L) → ℂ) :
    avgOp d L i (zeroModeSet d L A f) = zeroModeSet d L A (avgOp d L i f) := by
  induction A using Finset.induction_on with
  | empty => simp only [npq_zms_empty]
  | insert j A hj ih =>
    have hij : i ≠ j := fun h => hi (h ▸ mem_insert_self _ _)
    have hiA : i ∉ A := fun h => hi (mem_insert_of_mem h)
    rw [npq_zms_insert hj, npq_zms_insert hj, npq_avg_zmo i j hij, ih hiA]

/-- `Q^(A) = Q^(insert i A) + P^(i) Q^(A)` for `i ∉ A`. -/
private theorem npq_split (i : Fin N) (A : Finset (Fin N)) (hi : i ∉ A)
    (f : (Fin N → Zd d L) → ℂ) (a : Fin N → Zd d L) :
    zeroModeSet d L A f a
      = zeroModeSet d L (insert i A) f a + avgOp d L i (zeroModeSet d L A f) a := by
  rw [npq_zms_insert hi]
  simp only [zeroModeOp]
  ring

private theorem npq_zmo_lin (i : Fin N) (c : ℂ) (u v : (Fin N → Zd d L) → ℂ) :
    zeroModeOp d L i (fun b => c * (u b - v b))
      = fun b => c * (zeroModeOp d L i u b - zeroModeOp d L i v b) := by
  funext a
  simp only [zeroModeOp]
  rw [npq_avgOp_mul, npq_avgOp_sub]
  ring

private theorem npq_zms_lin (A : Finset (Fin N)) (c : ℂ) (u v : (Fin N → Zd d L) → ℂ) :
    zeroModeSet d L A (fun b => c * (u b - v b))
      = fun b => c * (zeroModeSet d L A u b - zeroModeSet d L A v b) := by
  induction A using Finset.induction_on with
  | empty => simp only [npq_zms_empty]
  | insert j A hj ih =>
    rw [npq_zms_insert hj, npq_zms_insert hj, npq_zms_insert hj, ih, npq_zmo_lin]

/-- Reindexing of `Q^(A)` along an injection `ι` of index sets: if `A ⊆ range ι`, then
`Q^(A)(G ∘ (· ∘ ι)) = (Q^(ι⁻¹ A) G) ∘ (· ∘ ι)`. -/
private theorem npq_zms_comp {p q : ℕ} (e : Fin p → Fin q) (he : Function.Injective e)
    (A : Finset (Fin q)) (hA : ∀ j ∈ A, j ∈ Set.range e) (G : (Fin p → Zd d L) → ℂ)
    (a : Fin q → Zd d L) :
    zeroModeSet d L A (fun a' => G (a' ∘ e)) a
      = zeroModeSet d L (Finset.univ.filter fun j => e j ∈ A) G (a ∘ e) := by
  induction A using Finset.induction_on generalizing a with
  | empty => simp [npq_zms_empty]
  | insert j A hj ih =>
    obtain ⟨j', rfl⟩ := hA j (mem_insert_self _ _)
    have hA' : ∀ x ∈ A, x ∈ Set.range e := fun x hx => hA x (mem_insert_of_mem hx)
    have hj' : j' ∉ (Finset.univ.filter fun x => e x ∈ A) := by
      simpa using hj
    have hfilt : (Finset.univ.filter fun x => e x ∈ insert (e j') A)
        = insert j' (Finset.univ.filter fun x => e x ∈ A) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      rw [he.eq_iff]
    rw [hfilt, npq_zms_insert hj, npq_zms_insert hj']
    have ih' : zeroModeSet d L A (fun a' => G (a' ∘ e))
        = fun a' => zeroModeSet d L (Finset.univ.filter fun x => e x ∈ A) G (a' ∘ e) :=
      funext fun a' => ih hA' a'
    rw [ih']
    simp only [zeroModeOp, avgOp]
    congr 2
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Function.update_comp_eq_of_injective a he j' x]

end Operators

/-! ## 2. Loops: cyclic invariance and the Ward identity at the last index, `𝓛` and `𝒦` -/

section Loops

open RBM.Gauss RBM.Loop

variable {d L W : ℕ} [NeZero L]

private theorem npq_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
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

/-- Cyclic invariance of `𝓛`: moving the first edge to the end (trace cyclicity). -/
private theorem npq_loopL_rotate (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s : Bool)
    (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    loopL d L W H z ⟨s :: σ, b :: a⟩ = loopL d L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [npq_loopL_eq_prod, npq_loopL_eq_prod]
  simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
  rw [List.zip_append h]
  simp only [List.map_append, List.prod_append, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

private theorem npq_Gres_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ)
    (s : Bool) : Gres H ((starRingEnd ℂ) z) (!s) = Gres H z s := by
  cases s <;> simp [Gres]

/-- `𝓛_{z̄, (¬σ), a} = 𝓛_{z, σ, a}`. -/
private theorem npq_loopL_conj (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (σ : List Bool)
    (a : List (Zd d L)) :
    loopL d L W H ((starRingEnd ℂ) z) ⟨σ.map not, a⟩ = loopL d L W H z ⟨σ, a⟩ := by
  rw [npq_loopL_eq_prod, npq_loopL_eq_prod]
  congr 2
  simp only [List.zip_map_left, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp [npq_Gres_conj]

/-- **`(WI_calL)` at the last index, both charge orders** (`σ₁ = s`, `σ_n = ¬s`):
`∑_x 𝓛^{(n)}_{(s, μ, ¬s),(a, x)} = (2 i W^d Im z)⁻¹ (𝓛^{(n-1),+}_{(μ),a} - 𝓛^{(n-1),-}_{(μ),a})`.
For `s = +` this is the merged `sum_gloop_ward_last_div` (D105); for `s = -` it is that identity at
`z̄` (`Im z̄ = -Im z`, charges flipped by `npq_loopL_conj`). -/
private theorem npq_loopL_ward [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
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
      have := npq_loopL_conj H z (false :: μ ++ [!false]) (x0 :: a' ++ [x])
      simpa [List.map_append] using this.symm
    have hB : loopL d L W H z ⟨true :: μ, x0 :: a'⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨false :: μ.map not, x0 :: a'⟩ := by
      have := npq_loopL_conj H z (true :: μ) (x0 :: a')
      simpa using this.symm
    have hC : loopL d L W H z ⟨false :: μ, x0 :: a'⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨true :: μ.map not, x0 :: a'⟩ := by
      have := npq_loopL_conj H z (false :: μ) (x0 :: a')
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

/-- The list-level facts about a loop functional that the Ward step uses: cyclic invariance and the
Ward identity at the last index (both charge orders); `κ = (2 i W^d η)⁻¹`. -/
private structure NPQFam (d L : ℕ) [NeZero L] (κ : ℂ) (T' : LoopIdx (Zd d L) → ℂ) : Prop where
  rot : ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
    T' ⟨s :: σ, b :: a⟩ = T' ⟨σ ++ [s], a ++ [b]⟩
  ward : ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
    ∑ x : Zd d L, T' ⟨s :: μ ++ [!s], a ++ [x]⟩
      = κ * (T' ⟨true :: μ, a⟩ - T' ⟨false :: μ, a⟩)

end Loops

/-! ## 3. The Ward step at an interior index

`ρ = finRotate (n+2)` is the cyclic shift `j ↦ j + 1`.  `npqRot n i = ρ^(i+1)` sends the last position
to `i` and `0` to `i + 1` (`ρ i`).  Rotating the loop by `ρ^(i+1)` puts the edge `i` last and the edge
`i+1` first, which is the situation of `npq_loopL_ward` (and of `KLK_ward`). -/

section WardStep

variable {d L : ℕ} [NeZero L]

/-- The rotation `ρ^(i+1)`: it sends the last position to `i` and `0` to `ρ i`. -/
private def npqRot (n : ℕ) (i : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (finRotate (n + 2)) ^ (i.val + 1)

private theorem npq_pow_rot_zero (n : ℕ) :
    ∀ (k : ℕ) (hk : k < n + 2), ((finRotate (n + 2)) ^ k) 0 = ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

private theorem npqRot_last (n : ℕ) (i : Fin (n + 2)) : npqRot n i (Fin.last (n + 1)) = i := by
  unfold npqRot
  rw [pow_succ, Equiv.Perm.mul_apply, finRotate_last, npq_pow_rot_zero n i.val i.isLt]

private theorem npqRot_zero (n : ℕ) (i : Fin (n + 2)) : npqRot n i 0 = finRotate (n + 2) i := by
  unfold npqRot
  rw [pow_succ', Equiv.Perm.mul_apply, npq_pow_rot_zero n i.val i.isLt]

/-- The `(n+1)`-loop after one Ward step at `i`: the charge `σ_{i+1}` is replaced by `s`, the charge
`σ_i` is dropped, the positions are listed from `i + 1` cyclically. -/
private def npqSg {n : ℕ} (σ : Fin (n + 2) → Bool) (i : Fin (n + 2)) (s : Bool) :
    Fin (n + 1) → Bool :=
  Fin.cons (α := fun _ => Bool) s (fun j : Fin n => σ (npqRot n i j.succ.castSucc))

/-- The labels of that loop: `a ∘ ι` with `ι = ρ^(i+1) ∘ castSucc`. -/
private def npqIota (n : ℕ) (i : Fin (n + 2)) : Fin (n + 1) → Fin (n + 2) :=
  fun j => npqRot n i j.castSucc

private theorem npqIota_injective (n : ℕ) (i : Fin (n + 2)) : Function.Injective (npqIota n i) :=
  (npqRot n i).injective.comp (Fin.castSucc_injective _)

private theorem npqIota_range (n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i) :
    j ∈ Set.range (npqIota n i) := by
  have h1 : (npqRot n i).symm j ≠ Fin.last (n + 1) := by
    intro h
    apply hj
    rw [← npqRot_last n i, ← h, Equiv.apply_symm_apply]
  obtain ⟨j', hj'⟩ := Fin.exists_castSucc_eq.mpr h1
  exact ⟨j', by simp only [npqIota, hj', Equiv.apply_symm_apply]⟩

/-- The Ward expansion of the average over the index `i`: the hypothesis `NPQWard` is what the loops
`𝓛`, `𝒦` satisfy (`npq_ward_of_fam`); `c = L^{-d} (2 i W^d η)⁻¹`. -/
private def NPQWard (d L : ℕ) [NeZero L] (c : ℂ)
    (T : ∀ k : ℕ, (Fin k → Bool) → (Fin k → Zd d L) → ℂ) : Prop :=
  ∀ (n : ℕ) (σ : Fin (n + 2) → Bool) (i : Fin (n + 2)), σ i ≠ σ (finRotate (n + 2) i) →
    ∀ a : Fin (n + 2) → Zd d L,
      avgOp d L i (T (n + 2) σ) a
        = c * (T (n + 1) (npqSg σ i true) (a ∘ npqIota n i)
            - T (n + 1) (npqSg σ i false) (a ∘ npqIota n i))

section FamLemmas

open RBM.Loop

variable {κ : ℂ} {T' : LoopIdx (Zd d L) → ℂ}

private theorem npq_rot_one (hT : NPQFam d L κ T') {n : ℕ} (σ : Fin (n + 1) → Bool)
    (a : Fin (n + 1) → Zd d L) :
    T' ⟨List.ofFn σ, List.ofFn a⟩
      = T' ⟨List.ofFn (σ ∘ finRotate (n + 1)), List.ofFn (a ∘ finRotate (n + 1))⟩ := by
  have key : ∀ {α : Type} (f : Fin (n + 1) → α),
      List.ofFn (f ∘ finRotate (n + 1)) = List.ofFn (fun j : Fin n => f j.succ) ++ [f 0] := by
    intro α f
    rw [List.ofFn_succ']
    simp [finRotate_apply, Fin.coeSucc_eq_succ, Fin.last_add_one, List.concat_eq_append]
  have key' : ∀ (f : Fin (n + 1) → Zd d L),
      List.ofFn (f ∘ finRotate (n + 1)) = List.ofFn (fun j : Fin n => f j.succ) ++ [f 0] := by
    intro f
    rw [List.ofFn_succ']
    simp [finRotate_apply, Fin.coeSucc_eq_succ, Fin.last_add_one, List.concat_eq_append]
  rw [key σ, key' a, List.ofFn_succ (f := σ), List.ofFn_succ (f := a)]
  exact hT.rot _ _ _ _ (by simp)

private theorem npq_rot_pow (hT : NPQFam d L κ T') {n : ℕ} (k : ℕ) (σ : Fin (n + 1) → Bool)
    (a : Fin (n + 1) → Zd d L) :
    T' ⟨List.ofFn σ, List.ofFn a⟩
      = T' ⟨List.ofFn (σ ∘ ⇑((finRotate (n + 1)) ^ k)),
            List.ofFn (a ∘ ⇑((finRotate (n + 1)) ^ k))⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, npq_rot_one hT (σ ∘ ⇑((finRotate (n + 1)) ^ k)) (a ∘ ⇑((finRotate (n + 1)) ^ k))]
    have hp : ⇑((finRotate (n + 1)) ^ (k + 1))
        = ⇑((finRotate (n + 1)) ^ k) ∘ ⇑(finRotate (n + 1)) := by
      rw [pow_succ]; rfl
    rw [hp]
    rfl

/-- `(WI)` at the last position on `Fin`-indexed loops. -/
private theorem npq_ward_last (hT : NPQFam d L κ T') (n : ℕ) (σ : Fin (n + 2) → Bool)
    (hne : σ (Fin.last (n + 1)) ≠ σ 0) (a : Fin (n + 2) → Zd d L) :
    ∑ x : Zd d L, T' ⟨List.ofFn σ, List.ofFn (Function.update a (Fin.last (n + 1)) x)⟩
      = κ * (T' ⟨List.ofFn (Fin.cons (α := fun _ => Bool) true
                  (fun j : Fin n => σ j.succ.castSucc) : Fin (n + 1) → Bool),
                List.ofFn (fun j : Fin (n + 1) => a j.castSucc)⟩
            - T' ⟨List.ofFn (Fin.cons (α := fun _ => Bool) false
                  (fun j : Fin n => σ j.succ.castSucc) : Fin (n + 1) → Bool),
                List.ofFn (fun j : Fin (n + 1) => a j.castSucc)⟩) := by
  have hlast : σ (Fin.last (n + 1)) = !σ 0 := Bool.eq_not_iff.mpr hne
  have hσ : List.ofFn σ
      = σ 0 :: (List.ofFn (fun j : Fin n => σ j.succ.castSucc)) ++ [!σ 0] := by
    rw [List.ofFn_succ, List.ofFn_succ' (f := fun j : Fin (n + 1) => σ j.succ)]
    simp only [Fin.succ_castSucc, Fin.succ_last, hlast, List.concat_eq_append, List.cons_append]
  have ha : ∀ x : Zd d L,
      List.ofFn (Function.update a (Fin.last (n + 1)) x)
        = List.ofFn (fun j : Fin (n + 1) => a j.castSucc) ++ [x] := by
    intro x
    rw [List.ofFn_succ']
    simp [Function.update_of_ne, (Fin.castSucc_lt_last _).ne, List.concat_eq_append]
  simp_rw [ha]
  rw [hσ]
  have hw := hT.ward (σ 0) (List.ofFn (fun j : Fin n => σ j.succ.castSucc))
    (List.ofFn (fun j : Fin (n + 1) => a j.castSucc)) (by simp)
  rw [hw]
  simp only [List.ofFn_succ (f := (Fin.cons (α := fun _ => Bool) _ _ : Fin (n + 1) → Bool)),
    Fin.cons_zero, Fin.cons_succ]

/-- **The Ward step at an interior index** for a loop functional with the list-level facts of
`NPQFam`: `P^(i) 𝓛^{(n+2)}_σ = c (𝓛^{(n+1),+} - 𝓛^{(n+1),-})` when `σ_i ≠ σ_{i+1}`. -/
private theorem npq_ward_of_fam (hT : NPQFam d L κ T') (c : ℂ)
    (hc : ((L : ℂ) ^ d)⁻¹ * κ = c) :
    NPQWard d L c (fun _ σ a => T' ⟨List.ofFn σ, List.ofFn a⟩) := by
  intro n σ i hne a
  have hlast : npqRot n i (Fin.last (n + 1)) = i := npqRot_last n i
  have h0 : npqRot n i 0 = finRotate (n + 2) i := npqRot_zero n i
  have hrot : ∀ b : Fin (n + 2) → Zd d L,
      T' ⟨List.ofFn σ, List.ofFn b⟩
        = T' ⟨List.ofFn (σ ∘ npqRot n i), List.ofFn (b ∘ npqRot n i)⟩ := fun b =>
    npq_rot_pow hT (i.val + 1) σ b
  have hup : ∀ x : Zd d L, Function.update a i x ∘ npqRot n i
      = Function.update (a ∘ npqRot n i) (Fin.last (n + 1)) x := by
    intro x
    rw [Function.update_comp_equiv]
    congr 1
    exact (Equiv.symm_apply_eq _).mpr hlast.symm
  have hne' : (σ ∘ npqRot n i) (Fin.last (n + 1)) ≠ (σ ∘ npqRot n i) 0 := by
    simpa [hlast, h0] using hne
  have hw := npq_ward_last hT n (σ ∘ npqRot n i) hne' (a ∘ npqRot n i)
  change ((L : ℂ) ^ d)⁻¹ * ∑ x : Zd d L, T' ⟨List.ofFn σ, List.ofFn (Function.update a i x)⟩ = _
  simp_rw [hrot, hup]
  rw [hw, ← hc, mul_assoc]
  rfl

end FamLemmas

end WardStep

/-! ## 4. The induction: one Ward step per index of `I_diff(σ) \ A` -/

section Induction

open RBM.Gauss.Sizes

/-- One term `(k_α, ξ_α, σ_α, ι_α, A_α)` of the expansion `(yurenAL)`. -/
private structure NPQTerm (m : ℕ) where
  k : ℕ
  ξ : ℤ
  σ : Fin k → Bool
  ι : Fin k → Fin m
  A : Finset (Fin k)

/-- The value `ξ c^{m-k} (Q^{(A)} T^{(k)}_σ)(a ∘ ι)` of a term. -/
private def NPQTerm.val {m : ℕ} (d L : ℕ) [NeZero L] (c : ℂ)
    (T : ∀ k : ℕ, (Fin k → Bool) → (Fin k → Zd d L) → ℂ) (a : Fin m → Zd d L) (t : NPQTerm m) : ℂ :=
  (t.ξ : ℂ) * c ^ (m - t.k) * zeroModeSet d L t.A (T t.k t.σ) (a ∘ t.ι)

/-- A term of the expansion of length `n+1`, transported along `e : Fin (n+1) → Fin (n+2)` with a sign. -/
private def NPQTerm.lift {n : ℕ} (e : Fin (n + 1) → Fin (n + 2)) (sg : ℤ) (t : NPQTerm (n + 1)) :
    NPQTerm (n + 2) :=
  ⟨t.k, sg * t.ξ, t.σ, e ∘ t.ι, t.A⟩

private theorem npq_lift_sum (d L : ℕ) [NeZero L] (c : ℂ)
    (T : ∀ k : ℕ, (Fin k → Bool) → (Fin k → Zd d L) → ℂ) {n : ℕ} (a : Fin (n + 2) → Zd d L)
    (e : Fin (n + 1) → Fin (n + 2)) (sg : ℤ) (Lq : List (NPQTerm (n + 1)))
    (hf : ∀ t ∈ Lq, t.k + 1 ≤ n + 1) :
    ((Lq.map (NPQTerm.lift e sg)).map (NPQTerm.val d L c T a)).sum
      = (sg : ℂ) * c * (Lq.map (NPQTerm.val d L c T (a ∘ e))).sum := by
  rw [List.map_map, mul_assoc, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  have hk := hf t ht
  have hpow : c ^ (n + 2 - t.k) = c * c ^ (n + 1 - t.k) := by
    rw [← pow_succ']; congr 1; omega
  simp only [Function.comp, NPQTerm.val, NPQTerm.lift, hpow]
  push_cast
  rw [show (a ∘ e) ∘ t.ι = a ∘ e ∘ t.ι from rfl]
  ring

/-- **The expansion `(yurenAL)`/`(yurenAK)` for a general loop functional with the Ward hypothesis
`NPQWard`**: for every `m`, `σ`, `B ⊆ I_diff(σ)` and `A`, a list of terms, independent of `L`, `c`,
`T`, with `1 ≤ k`, `k + 1 ≤ m`, `I_diff(σ_α) ⊆ A_α`, such that
`Q^(A) T_σ = Q^(A ∪ B) T_σ + ∑_α ξ_α c^{m-k_α} Q^(A_α) T_{σ_α} (· ∘ ι_α)`.
Induction on `m` (strong) and on `B`: for `i ∉ A`, `Q^(A) = Q^(A ∪ {i}) + P^(i) Q^(A)` and
`P^(i) T_σ = c (T^+ - T^-)` is the Ward step. -/
private theorem npq_main (d : ℕ) : ∀ (m : ℕ) (σ : Fin m → Bool) (B : Finset (Fin m)),
    B ⊆ STIdiff σ → ∀ A : Finset (Fin m),
    ∃ Ls : List (NPQTerm m),
      (∀ t ∈ Ls, 1 ≤ t.k ∧ t.k + 1 ≤ m ∧ STIdiff t.σ ⊆ t.A) ∧
      ∀ (L : ℕ) [NeZero L] (c : ℂ) (T : ∀ k : ℕ, (Fin k → Bool) → (Fin k → Zd d L) → ℂ),
        NPQWard d L c T → ∀ a : Fin m → Zd d L,
          zeroModeSet d L A (T m σ) a
            = zeroModeSet d L (A ∪ B) (T m σ) a + (Ls.map (NPQTerm.val d L c T a)).sum := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro σ B
  induction B using Finset.induction_on with
  | empty =>
    intro _ A
    exact ⟨[], by simp, fun L _ c T _ a => by simp⟩
  | insert i B hiB ihB =>
    intro hsub A
    have hB : B ⊆ STIdiff σ := (Finset.subset_insert _ _).trans hsub
    have hiI : i ∈ STIdiff σ := hsub (Finset.mem_insert_self _ _)
    by_cases hiA : i ∈ A
    · obtain ⟨Ls, hf, h⟩ := ihB hB A
      refine ⟨Ls, hf, fun L _ c T hW a => ?_⟩
      have hAB : A ∪ insert i B = A ∪ B := by
        rw [Finset.union_insert, Finset.insert_eq_of_mem (Finset.mem_union_left _ hiA)]
      rw [hAB]
      exact h L c T hW a
    · have hσi : σ i ≠ σ (finRotate m i) := by simpa [STIdiff] using hiI
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := by
        rcases m with _ | _ | n
        · exact i.elim0
        · exact absurd (congrArg σ (Fin.ext (by have := i.isLt; have := (finRotate _ i).isLt; omega))) hσi
        · exact ⟨n, rfl⟩
      -- the Ward step at `i`
      obtain ⟨e, he⟩ : ∃ e, e = npqIota n i := ⟨_, rfl⟩
      have heinj : Function.Injective e := he ▸ npqIota_injective n i
      have herange : ∀ j ∈ A, j ∈ Set.range e := fun j hj =>
        he ▸ npqIota_range n i j (fun h => hiA (h ▸ hj))
      obtain ⟨σp, hσp⟩ : ∃ σp, σp = npqSg σ i true := ⟨_, rfl⟩
      obtain ⟨σm, hσm⟩ : ∃ σm, σm = npqSg σ i false := ⟨_, rfl⟩
      obtain ⟨Ap, hAp⟩ : ∃ Ap : Finset (Fin (n + 1)), Ap = Finset.univ.filter fun j => e j ∈ A :=
        ⟨_, rfl⟩
      obtain ⟨Lp, hfp, hp⟩ := IH (n + 1) (by omega) σp (STIdiff σp) (Finset.Subset.refl _) Ap
      obtain ⟨Lm, hfm, hm⟩ := IH (n + 1) (by omega) σm (STIdiff σm) (Finset.Subset.refl _) Ap
      obtain ⟨L1, hf1, h1⟩ := ihB hB (insert i A)
      refine ⟨L1 ++ (⟨n + 1, 1, σp, e, Ap ∪ STIdiff σp⟩ :: ⟨n + 1, -1, σm, e, Ap ∪ STIdiff σm⟩ ::
        (Lp.map (NPQTerm.lift e 1) ++ Lm.map (NPQTerm.lift e (-1)))), ?_, ?_⟩
      · intro t ht
        simp only [List.mem_append, List.mem_cons, List.mem_map] at ht
        rcases ht with ht | rfl | rfl | ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
        · exact hf1 t ht
        · exact ⟨by change 1 ≤ n + 1; omega, by change n + 1 + 1 ≤ n + 2; omega, Finset.subset_union_right⟩
        · exact ⟨by change 1 ≤ n + 1; omega, by change n + 1 + 1 ≤ n + 2; omega, Finset.subset_union_right⟩
        · obtain ⟨h1', h2', h3'⟩ := hfp t' ht'
          exact ⟨h1', by simp only [NPQTerm.lift]; omega, h3'⟩
        · obtain ⟨h1', h2', h3'⟩ := hfm t' ht'
          exact ⟨h1', by simp only [NPQTerm.lift]; omega, h3'⟩
      · intro L _ c T hW a
        have hs : n + 2 - (n + 1) = 1 := by omega
        have e1 := npq_split i A hiA (T (n + 2) σ) a
        have e2 := h1 L c T hW a
        have e3 := congrFun (npq_avg_zms i A hiA (T (n + 2) σ)) a
        have e4 : avgOp d L i (T (n + 2) σ)
            = fun a' => (fun b => c * (T (n + 1) σp b - T (n + 1) σm b)) (a' ∘ e) := by
          funext a'
          rw [hσp, hσm, he]
          exact hW n σ i hσi a'
        have e5 := npq_zms_comp e heinj A herange
          (fun b => c * (T (n + 1) σp b - T (n + 1) σm b)) a
        have e6 := congrFun (npq_zms_lin Ap c (T (n + 1) σp) (T (n + 1) σm)) (a ∘ e)
        have e7 := hp L c T hW (a ∘ e)
        have e8 := hm L c T hW (a ∘ e)
        have hU : A ∪ insert i B = insert i A ∪ B := by
          rw [Finset.union_insert, Finset.insert_union]
        rw [← hAp] at e5
        rw [e4] at e3
        simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
        rw [npq_lift_sum d L c T a e 1 Lp (fun t ht => (hfp t ht).2.1),
          npq_lift_sum d L c T a e (-1) Lm (fun t ht => (hfm t ht).2.1), hU]
        simp only [NPQTerm.val, hs]
        rw [e1, e3, e5, e6, e2, e7, e8]
        push_cast
        ring

end Induction

/-! ## 5. `stNewPQ_holds` -/

namespace Gauss.Sizes

open RBM.Gauss RBM.Loop

/-- The sum over the list of terms is the sum over `Fin ℓ`. -/
private theorem npq_sum_get {α β : Type*} [AddCommMonoid β] (Ls : List α) (F : α → β) :
    ∑ i : Fin Ls.length, F (Ls.get i) = (Ls.map F).sum := by
  calc ∑ i : Fin Ls.length, F (Ls.get i) = (List.ofFn (F ∘ Ls.get)).sum := List.sum_ofFn.symm
    _ = ((List.ofFn Ls.get).map F).sum := by rw [List.map_ofFn]
    _ = (Ls.map F).sum := by rw [List.ofFn_get]

/-- **`lem: newPQ`** (`3_5:1482-1507`; expansions `(yurenAL)`, `(yurenAK)`, `3_5:1871-1886`): the pin
`STNewPQ` (`RBM3D/Induction/Step34Pins.lean:330`), for every `d`.  The data `(k_α, ξ_α, σ_α, ι_α, A_α)`
are built by induction on `m` and on `#(I_diff(σ) \ A)`, one Ward step per index (`npq_main`); the
same data serve `𝓛` (Ward identity `npq_loopL_ward`, both charge orders) and `𝒦` (`KLK_ward`).
Each Ward step lowers the length by one and multiplies by `(2 i N η_τ)⁻¹`:
`L^{-d} (2 i W^d η_τ)⁻¹ = (2 i N η_τ)⁻¹`, `N = (W L)^d`. -/
theorem stNewPQ_holds (d : ℕ) : STNewPQ d := by
  intro m σ A
  obtain ⟨Ls, hf, h⟩ := npq_main d m σ (STIdiff σ) (Finset.Subset.refl _) A
  refine ⟨Ls.length, fun α => (Ls.get α).k, fun α => (Ls.get α).ξ, fun α => (Ls.get α).σ,
    fun α => (Ls.get α).ι, fun α => (Ls.get α).A, ?_, ?_, ?_⟩
  · intro α
    have := hf _ (List.get_mem Ls α)
    exact ⟨this.1, this.2.1⟩
  · intro α
    exact (hf _ (List.get_mem Ls α)).2.2
  · intro sz n E τ hE hτ0 hτ1 ω a
    have hL : 3 ≤ sz.L n := sz.three_le_L n
    have hW : 1 ≤ sz.W n := sz.W_pos n
    have hη : 0 < etaT E τ := etaT_pos hE hτ1
    set c : ℂ := (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ))⁻¹ with hc
    have hcL : ((sz.L n : ℂ) ^ d)⁻¹ * (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E τ : ℂ))⁻¹ = c := by
      have hLne : ((sz.L n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hWne : ((sz.W n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hηne : (etaT E τ : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
      rw [hc]
      simp only [Sizes.size]
      push_cast
      rw [mul_pow]
      field_simp
    have hsum : ∀ T : ∀ k : ℕ, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → ℂ,
        ∑ α : Fin Ls.length, ((((Ls.get α).ξ : ℤ) : ℂ) /
            (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - (Ls.get α).k)) *
          zeroModeSet d (sz.L n) (Ls.get α).A (T (Ls.get α).k (Ls.get α).σ) (a ∘ (Ls.get α).ι)
        = (Ls.map (NPQTerm.val d (sz.L n) c T a)).sum := by
      intro T
      rw [← npq_sum_get Ls (NPQTerm.val d (sz.L n) c T a)]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [NPQTerm.val, hc, div_eq_mul_inv, inv_pow]
    constructor
    · -- `𝓛`
      have hHerm : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n τ ω)).IsHermitian :=
        (Sizes.gLoopFlow_seqHflow_isHermitian sz n τ ω).submatrix _
      have hz : (zt E τ).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
      have hfam : NPQFam d (sz.L n) ((2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E τ : ℂ))⁻¹)
          (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n τ ω)) (zt E τ)) :=
        ⟨fun s b σ a h => npq_loopL_rotate _ _ s b σ a h, fun s μ a ha => by
          have := npq_loopL_ward hHerm hz s μ a ha
          rwa [← etaT_eq_zt_im] at this⟩
      have hT : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
          Lloop sz n E τ σ a ω
            = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n τ ω)) (zt E τ)
                ⟨List.ofFn σ, List.ofFn a⟩ := fun k σ a => loopM_eq_loopL d (sz.L n) (sz.W n) _ (zt E τ) σ a
      have hward := npq_ward_of_fam hfam c hcL
      have key := h (sz.L n) c (fun k σ a => Lloop sz n E τ σ a ω)
        (by simpa only [hT] using hward) a
      rw [← hsum (fun k σ a => Lloop sz n E τ σ a ω)] at key
      exact key
    · -- `𝒦`
      have hfam : NPQFam d (sz.L n) ((2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E τ : ℂ))⁻¹)
          (KLK d (sz.L n) (sz.lam n) (sz.W n) E τ) :=
        ⟨fun s b σ a h => KLK_rotate d (sz.L n) (sz.W n) (sz.lam n) E hL hW hE τ ⟨hτ0, hτ1⟩ s b σ a h,
          fun s μ a ha => KLK_ward d (sz.L n) (sz.W n) (sz.lam n) E hL hW hE τ hτ0 hτ1 s μ a ha⟩
      have hward := npq_ward_of_fam hfam c hcL
      have key := h (sz.L n) c (fun k σ a => STKloop sz n E τ σ a) hward a
      rw [← hsum (fun k σ a => STKloop sz n E τ σ a)] at key
      exact key

end Gauss.Sizes

/-! ## 6. The compiled instance of `stNewPQ_holds`: `d = 3`, `m = 3`, `σ = (+,-,+)`, `A = ∅`

At the merged preflight sequence `sz0` (`L_0 = 4`, `W_0 = 32`, `N = 2097152`, `RBM3D/Defs/Sizes.lean:260`),
size index `n = 0`, `E = 0` (`|E| < 2`), `τ = 1/2` (`0 ≤ τ < 1`), every `ω` and every label vector
`a : Fin 3 → Z_4^3`.  The three deterministic hypotheses `|0| < 2`, `0 ≤ 1/2`, `1/2 < 1` are discharged
by `norm_num`; the loop has `I_diff(σ) = {0, 1}` (`σ_0 ≠ σ_1`, `σ_1 ≠ σ_2`); the data
`(ℓ, k, ξ, σ', ι, A')` are the ones of `stNewPQ_holds`, chosen before `sz`, `n`, `E`, `τ`, `ω`, `a`. -/

namespace Gauss.Sizes.NewPQInst

open RBM.Gauss.SizesInst

example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
    (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
    (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
    ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)),
      (zeroModeSet 3 (sz0.L 0) ∅ (fun a' => Lloop sz0 0 0 (1 / 2) ![true, false, true] a' ω) a =
        zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff ![true, false, true])
            (fun a' => Lloop sz0 0 0 (1 / 2) ![true, false, true] a' ω) a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                (Gauss.etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => Lloop sz0 0 0 (1 / 2) (σ' α) a' ω) (a ∘ ι α)) ∧
      (zeroModeSet 3 (sz0.L 0) ∅ (fun a' => STKloop sz0 0 0 (1 / 2) ![true, false, true] a') a =
        zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff ![true, false, true])
            (fun a' => STKloop sz0 0 0 (1 / 2) ![true, false, true] a') a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                (Gauss.etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => STKloop sz0 0 0 (1 / 2) (σ' α) a') (a ∘ ι α)) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := Gauss.Sizes.stNewPQ_holds 3 3 ![true, false, true] ∅
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a =>
    h sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ω a⟩

end Gauss.Sizes.NewPQInst

end RBM
