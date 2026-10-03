/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Split
import RBM3D.Loop.GLoop
import RBM3D.Green.EntryCore
import Mathlib.Algebra.Order.Chebyshev

/-!
# S1-31 (ticket T2063): the Ward identity for resolvent loops and the deterministic part of
`lem_ConArg`, `d ≥ 3`

Port of `RBM2D/Hierarchy/WardResolvent.lean` and `RBM2D/Induction/ConArgDet.lean` at commit
`c9a24cf` (the `d = 2` ports of `RBM1D/Loop/Continuity.lean` and of
`RBM1D/Loop/ContinuityAssembly.lean`)
onto the merged block-product index `Vtx d L W = Zd d L × Fin (W ^ d)`, block labels in `Zd d L`,
the merged `Gres`, `Eblk`, `Loop.LoopIdx`, the list-based loop `loopL` (`RBM3D/Loop/GLoopFlow.lean`;
RBM2D's `gloop`) and the Split vocabulary (`gchain`, `loopMax`, `symIdx`, `wmass`, `bw`;
`RBM3D/Induction/Split.lean`, T2033).  Everything here is for a **fixed deterministic Hermitian**
`H`: no expectation and no `≺`.  The paper statement `lem_ConArg` is at `3_5:42-57` (its proof, at
`3_5:60`, is "exactly the same as that for Lemma 5.1 in [YY_25], except for some minor changes in
notation"); the Ward identity is `WI_calL` (`1_2:1036-1042`,
`∑_{a_n} 𝓛^{(n)} = (2i W^d η_t)⁻¹ (𝓛^{(n-1),+} - 𝓛^{(n-1),-})` for `σ_1 = -σ_n`).  Here the block
`[a]` has `W^d` sites, `E_a = W^{-d} 1_{[a]}`, and `ℓ` does not enter.  Only the case
`σ_1 = +`, `σ_n = -` of `WI_calL` is ported (`sum_gloop_ward_last_div`), as in RBM2D.

## Part 1: `RBM.green_sub_green`, … `RBM.sum_gloop_ward_last_div` (RBM2D `Hierarchy/WardResolvent`)

The resolvent identity `G(z) - G(w) = (z-w) G(z) G(w)`, its conjugate form with `2iη`, the traced
form, and the summed Ward identity for `G`-loops: summing the last block label of a loop of
signs `(+, μ, -)` removes its `E_b` with the factor `W^{-d}` (RBM2D `W⁻²`):
`sum_gloop_ward_last_div`, the case `σ_1 = +`, `σ_n = -` of `WI_calL`.

## Part 2: `RBM.Ind.…` (RBM2D `Induction/ConArgDet`)

* `zSig`, `isUnit_sub_zSig`, `green_eq_add_smul_mul`, `Gres_eq_add_smul_mul`: **(6.3)**.
* `list_prod_add_eq`, `gchainMixed`, `gchain_eq_add_sum_gchainMixed`: **(6.7)**, **(6.8)**.
* `norm_gchain_apply_sq_le`: **(6.9)**, `C_m = m + 1`.
* `gloop_symm_eq_trace`: **(6.5)**.
* `ward_chain_row`, `ward_chain_row'`: **(6.12)**, row average `W^{-d} ∑_{α ∈ Fin (W^d)}`.
* `ztTilde`, `ztTilde_arith`: the arithmetic of `z̃_{t₁} = (t₂/t₁)^{1/2} z_{t₁}`.
* `IsGLoopProd`, `norm_trace_smul_sub_pow_mul_le`, `exists_conjTranspose_mul_Eblk`,
  `sum_norm_gchain_row_sq_le`: Ward for loop products and (6.12) as an inequality.
* `blockCols`, `blockSel`, `trace_gram_blockCols_pow`, `trace_gram_rpow_le`: the Gram matrix
  `A` of the `W^d` block columns; `R Rᵀ = W^d E_b`, and
  `(tr A^p)^{1/p} ≤ W^d (Im w)⁻¹ (max|L_w^{(p(2k-1))}|)^{1/p}`.
* `wmass_gchain_mul_gchain_le`, `wmass_gchainMixed_le`: **(6.10)**, the powers `W^{-d}` and `W^d`
  cancel exactly (RBM2D `W⁻²`, `W²`).
* `norm_gloop_symIdx_le_tilde`, `loopMax_two_mul_le_tilde`: **(6.11)**.

The only scale RBM2D takes from `Path/Scales` is `Path.etaT`, which is the merged
`RBM.Gauss.etaT` (`RBM3D/Loop/GLoop.lean:75`, `η_t = (1 - t) Im m^{(E)}`); no `d`-dimensional
scale (`scaleM`, `ellT`, `tailT`) enters any statement, so no private copy is needed.
`spectralZ`, `spectralM` are the merged `zt`, `mE`.  RBM2D's `Gsig H z s` is `Gres H z s`,
`BlockIndex L W` is `Vtx d L W`, `gloop L W H z I` is `loopL d L W H z I`.  The section `Checks`
holds the compiled instances at `d = 3`, `L = 3`, `W = 2`, `H = 0`.
-/

namespace RBM

open Matrix Finset RBM.Gauss

/-! ## Part 1: the resolvent Ward identity (RBM2D `Hierarchy/WardResolvent`, `c9a24cf`) -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent identity for two spectral parameters.
`RBM2D/Hierarchy/WardResolvent.lean:25` (`green_sub_green`). -/
theorem green_sub_green {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z - green H w =
      (z - w) • (green H z * green H w) := by
  have hz' : green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hz)
  have hw' : (H - w • (1 : Matrix n n ℂ)) * green H w = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.mp hw)
  calc
    green H z - green H w =
        green H z * ((H - w • (1 : Matrix n n ℂ)) * green H w) -
          (green H z * (H - z • (1 : Matrix n n ℂ))) * green H w := by
        rw [hz', hw', Matrix.one_mul, Matrix.mul_one]
    _ = green H z * ((H - w • (1 : Matrix n n ℂ)) -
          (H - z • (1 : Matrix n n ℂ))) * green H w := by noncomm_ring
    _ = green H z * ((z - w) • (1 : Matrix n n ℂ)) * green H w := by
        congr 2
        module
    _ = (z - w) • (green H z * green H w) := by
        simp

/-- The conjugate resolvent identity in the order `G(z̄)G(z)`.
`RBM2D/Hierarchy/WardResolvent.lean:48` (`green_sub_green_conj'`). -/
theorem green_sub_green_conj' {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) :
    green H z - green H ((starRingEnd ℂ) z) =
      (2 * Complex.I * (z.im : ℂ)) •
        (green H ((starRingEnd ℂ) z) * green H z) := by
  have h := green_sub_green hz' hz
  have hc : (2 * Complex.I * (z.im : ℂ)) =
      -((starRingEnd ℂ) z - z) := by
    have h0 := Complex.sub_conj z
    push_cast at h0
    linear_combination -h0
  rw [hc, neg_smul, ← h]
  abel

/-- The traced Ward identity against any matrix observable.
`RBM2D/Hierarchy/WardResolvent.lean:64` (`trace_green_sub_trace_green_conj'`). -/
theorem trace_green_sub_trace_green_conj' {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ)))
    (A : Matrix n n ℂ) :
    Matrix.trace (green H z * A) -
      Matrix.trace (green H ((starRingEnd ℂ) z) * A) =
      (2 * Complex.I * (z.im : ℂ)) *
        Matrix.trace (green H ((starRingEnd ℂ) z) * green H z * A) := by
  have h := congrArg (fun M : Matrix n n ℂ => Matrix.trace (M * A))
    (green_sub_green_conj' hz hz')
  simpa [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc] using h

end Resolvent

/-! ### Helpers shared by both parts

RBM2D's `Gsig`, `gloopProd_nil/cons/append`, `gloop_rotate`, `sum_gloop_head` live in
`RBM2D/Hierarchy/Loops.lean` (`:48`, `:99`, `:102`, `:117`, `:136`, `:147`); the merged
`GLoopFlow.lean` keeps the `gloopProd_*` private (`:391-401`), so they are copied here, private. -/

section Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Gres H z +` (a `Ring.inverse`) is `green H z`.
RBM2D `Hierarchy/Loops.lean:51` (`Gsig_true`). -/
private theorem cad_Gres_true (H : Matrix ι ι ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- `Gres H z -` is `green H z̄`.  RBM2D `Hierarchy/Loops.lean:54` (`Gsig_false`). -/
private theorem cad_Gres_false (H : Matrix ι ι ℂ) (z : ℂ) :
    Gres H z false = green H ((starRingEnd ℂ) z) := by
  simp only [green, Gres, Bool.false_eq_true, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- `G(σ)ᴴ = G(!σ)` for Hermitian `H`.  RBM2D `Hierarchy/Loops.lean:68` (`Gsig_conjTranspose`). -/
private theorem cad_Gres_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ)
    (σ : Bool) : (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

variable {d L W : ℕ} [NeZero L] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}

private theorem cad_gloopProd_nil : gloopProd d L W H z ⟨[], []⟩ = 1 := rfl

private theorem cad_gloopProd_cons (s : Bool) (b : Zd d L) (σ : List Bool)
    (a : List (Zd d L)) :
    gloopProd d L W H z ⟨s :: σ, b :: a⟩ =
      Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩ := rfl

private theorem cad_gloopProd_append {σ₁ : List Bool} {a₁ : List (Zd d L)}
    (h₁ : σ₁.length = a₁.length) (σ₂ : List Bool) (a₂ : List (Zd d L)) :
    gloopProd d L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩ =
      gloopProd d L W H z ⟨σ₁, a₁⟩ * gloopProd d L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp [gloopProd]
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, cad_gloopProd_cons, ih h, Matrix.mul_assoc]

/-- `loopL` is the trace of `gloopProd` (RBM2D `gloop`, `Hierarchy/Loops.lean:92`). -/
private theorem cad_loopL_eq (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I = Matrix.trace (gloopProd d L W H z I) := rfl

/-- Cyclicity of the trace rotates one matching sign/block pair to the end of the loop.
RBM2D `Hierarchy/Loops.lean:136` (`gloop_rotate`). -/
private theorem cad_gloop_rotate (s : Bool) (b : Zd d L) {σ : List Bool} {a : List (Zd d L)}
    (h : σ.length = a.length) :
    loopL d L W H z ⟨s :: σ, b :: a⟩ = loopL d L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [cad_loopL_eq, cad_loopL_eq, cad_gloopProd_cons, cad_gloopProd_append h [s] [b]]
  rw [Matrix.trace_mul_comm]
  simp only [cad_gloopProd_cons, cad_gloopProd_nil, Matrix.mul_one]

/-- The blocks partition the identity with factor `W^{-d}`.  RBM2D `Defs/Model.lean:83`
(`sum_Eblk`). -/
private theorem cad_sum_Eblk :
    ∑ a, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- Summing a loop over its first block label removes one `E_b` and gives the factor `W^{-d}`
(RBM2D `W⁻²`).  RBM2D `Hierarchy/Loops.lean:147` (`sum_gloop_head`). -/
private theorem cad_sum_gloop_head (s : Bool) (σ : List Bool) (a : List (Zd d L)) :
    ∑ b : Zd d L, loopL d L W H z ⟨s :: σ, b :: a⟩ =
      (((W : ℂ) ^ d)⁻¹) * Matrix.trace (Gres H z s * gloopProd d L W H z ⟨σ, a⟩) := by
  have hterm : ∀ b : Zd d L, loopL d L W H z ⟨s :: σ, b :: a⟩ =
      Matrix.trace (Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩) :=
    fun _ => rfl
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, cad_sum_Eblk]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end Aux

section TwoLoop

variable (d L W : ℕ) [NeZero L]

/-- The summed `(+,-)` two-loop Ward identity. The factor `2iη` is essential:
`z - conj z = 2iη`; summing the final block insertion contributes `W^{-d}`.
`RBM2D/Hierarchy/WardResolvent.lean:85` (`sum_gloop_two_ward`). -/
theorem sum_gloop_two_ward
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (a : Zd d L) :
    (2 * Complex.I * (z.im : ℂ)) *
      ∑ b : Zd d L, loopL d L W H z ⟨[true, false], [a, b]⟩ =
      (((W : ℂ) ^ d)⁻¹) *
        (Matrix.trace (green H z * Eblk d L W a) -
          Matrix.trace (green H ((starRingEnd ℂ) z) * Eblk d L W a)) := by
  have hrot : ∀ b : Zd d L,
      loopL d L W H z ⟨[true, false], [a, b]⟩ =
        loopL d L W H z ⟨[false, true], [b, a]⟩ :=
    fun b => cad_gloop_rotate true a rfl
  simp_rw [hrot]
  rw [cad_sum_gloop_head, cad_Gres_false,
    trace_green_sub_trace_green_conj' hz hz' (Eblk d L W a)]
  have hprod : gloopProd d L W H z ⟨[true], [a]⟩ =
      green H z * Eblk d L W a := by
    simp [cad_gloopProd_cons, cad_gloopProd_nil, cad_Gres_true]
  rw [hprod]
  change (2 * Complex.I * (z.im : ℂ)) *
      ((((W : ℂ) ^ d)⁻¹) *
        Matrix.trace (green H ((starRingEnd ℂ) z) *
          (green H z * Eblk d L W a))) = _
  rw [← Matrix.mul_assoc]
  ring

/-- The corrected `G`-loop Ward identity at arbitrary length with first
sign `+` and last sign `−`. The middle signs and labels have equal lengths,
so both sides are well-formed loops.
`RBM2D/Hierarchy/WardResolvent.lean:117` (`sum_gloop_ward_last`). -/
theorem sum_gloop_ward_last
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (μ : List Bool) (x : Zd d L) (a' : List (Zd d L))
    (hμ : μ.length = a'.length) :
    (2 * Complex.I * (z.im : ℂ)) *
      ∑ b : Zd d L,
        loopL d L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩ =
      (((W : ℂ) ^ d)⁻¹) *
        (loopL d L W H z ⟨true :: μ, x :: a'⟩ -
          loopL d L W H z ⟨false :: μ, x :: a'⟩) := by
  let P := gloopProd d L W H z ⟨μ, a'⟩
  have hlen : (true :: μ).length = (x :: a').length := by simp [hμ]
  have hrot : ∀ b : Zd d L,
      loopL d L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩ =
        loopL d L W H z ⟨false :: true :: μ, b :: x :: a'⟩ := by
    intro b
    exact (cad_gloop_rotate (d := d) (L := L) (W := W) (H := H) (z := z)
      false b hlen).symm
  simp_rw [hrot]
  rw [cad_sum_gloop_head]
  have hprod : gloopProd d L W H z ⟨true :: μ, x :: a'⟩ =
      Gres H z true * Eblk d L W x * P := by
    simp [P, cad_gloopProd_cons]
  rw [hprod]
  have hplus : loopL d L W H z ⟨true :: μ, x :: a'⟩ =
      Matrix.trace (green H z * Eblk d L W x * P) := by
    rw [cad_loopL_eq, cad_gloopProd_cons, cad_Gres_true]
  have hminus : loopL d L W H z ⟨false :: μ, x :: a'⟩ =
      Matrix.trace (green H ((starRingEnd ℂ) z) * Eblk d L W x * P) := by
    rw [cad_loopL_eq, cad_gloopProd_cons, cad_Gres_false]
  rw [hplus, hminus]
  have htrace := trace_green_sub_trace_green_conj' hz hz' (Eblk d L W x * P)
  simp only [Matrix.mul_assoc] at htrace ⊢
  simp only [cad_Gres_false, cad_Gres_true]
  rw [htrace]
  ring

/-- The literal divided form of the corrected `(WI_calL)` (`1_2:1036`) for nonreal `z`
and positive block width `W`: the sum over the last block label of a loop of signs
`(+, μ, −)` is `(𝓛^{(n-1),+} − 𝓛^{(n-1),−}) / (2i W^d Im z)`.
`RBM2D/Hierarchy/WardResolvent.lean:159` (`sum_gloop_ward_last_div`, `W^2 → W^d`). -/
theorem sum_gloop_ward_last_div [NeZero W]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hη : z.im ≠ 0)
    (μ : List Bool) (x : Zd d L) (a' : List (Zd d L))
    (hμ : μ.length = a'.length) :
    (∑ b : Zd d L,
      loopL d L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩) =
      (loopL d L W H z ⟨true :: μ, x :: a'⟩ -
        loopL d L W H z ⟨false :: μ, x :: a'⟩) /
        (2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ)) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hWd : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d hW
  have hηC : (z.im : ℂ) ≠ 0 := by exact_mod_cast hη
  have hD : 2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, hWd, hηC]
  apply (eq_div_iff hD).2
  have hbase := sum_gloop_ward_last d L W hz hz' μ x a' hμ
  calc
    (∑ b : Zd d L,
      loopL d L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩) *
        (2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ)) =
          (W : ℂ) ^ d * ((2 * Complex.I * (z.im : ℂ)) *
            ∑ b : Zd d L,
              loopL d L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩) := by ring
    _ = (W : ℂ) ^ d * ((((W : ℂ) ^ d)⁻¹) *
          (loopL d L W H z ⟨true :: μ, x :: a'⟩ -
            loopL d L W H z ⟨false :: μ, x :: a'⟩)) := by rw [hbase]
    _ = loopL d L W H z ⟨true :: μ, x :: a'⟩ -
          loopL d L W H z ⟨false :: μ, x :: a'⟩ := by field_simp

end TwoLoop

end RBM

/-! ## Part 2: the deterministic part of `lem_ConArg` (RBM2D `Induction/ConArgDet`, `c9a24cf`) -/

namespace RBM.Ind

open Matrix RBM.Gauss

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral parameter carried by the charge `s`: `z` for `+`, `z̄` for `-`.
By definition `Gres H z s = green H (zSig z s)`. -/
def zSig (z : ℂ) (s : Bool) : ℂ := if s then z else (starRingEnd ℂ) z

@[simp] theorem zSig_true (z : ℂ) : zSig z true = z := rfl

@[simp] theorem zSig_false (z : ℂ) : zSig z false = (starRingEnd ℂ) z := rfl

theorem Gres_eq_green_zSig (H : Matrix n n ℂ) (z : ℂ) (s : Bool) :
    Gres H z s = green H (zSig z s) := by
  simp only [green, Gres, zSig, Matrix.nonsing_inv_eq_ringInverse]

theorem norm_zSig_sub_zSig (z w : ℂ) (s : Bool) : ‖zSig z s - zSig w s‖ = ‖z - w‖ := by
  cases s
  · simp only [zSig_false, ← map_sub, Complex.norm_conj]
  · rfl

theorem im_zSig (z : ℂ) (s : Bool) : (zSig z s).im = if s then z.im else -z.im := by
  cases s <;> simp

/-- A Hermitian matrix minus a non-real multiple of the identity is invertible. -/
theorem isUnit_sub_smul_one_of_im_ne_zero {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : IsUnit (H - z • (1 : Matrix n n ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hHv : H *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have him := hH.im_star_dotProduct_mulVec_self v
  rw [hHv, dotProduct_smul, smul_eq_mul] at him
  have hd : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hpos : (∑ i, Complex.normSq (v i) : ℝ) ≠ 0 := by
    intro h0
    apply hv0
    funext i
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (v j))).mp h0 i (Finset.mem_univ i))
  rw [hd, RCLike.im_to_complex, Complex.im_mul_ofReal] at him
  exact hz ((mul_eq_zero.mp him).resolve_right hpos)

theorem isUnit_sub_zSig {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (s : Bool) : IsUnit (H - zSig z s • (1 : Matrix n n ℂ)) := by
  refine isUnit_sub_smul_one_of_im_ne_zero hH ?_
  rw [im_zSig]
  split_ifs
  · exact hz
  · exact neg_ne_zero.mpr hz

/-- **(6.3)**, the two-parameter resolvent identity `G = G̃ + (z - z̃)·G·G̃`, where
`G = (H - z)⁻¹` and `G̃ = (H - z̃)⁻¹` share the same matrix `H`. -/
theorem green_eq_add_smul_mul {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ))) (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z = green H w + (z - w) • (green H z * green H w) := by
  rw [← green_sub_green hz hw]
  abel

/-- **(6.3) with charges**: `G(σ) = G̃(σ) + (z_σ - z̃_σ)·G(σ)·G̃(σ)`, where `z_+ = z` and
`z_- = z̄`. -/
theorem Gres_eq_add_smul_mul {H : Matrix n n ℂ} {z w : ℂ} {s : Bool}
    (hz : IsUnit (H - zSig z s • (1 : Matrix n n ℂ)))
    (hw : IsUnit (H - zSig w s • (1 : Matrix n n ℂ))) :
    Gres H z s = Gres H w s + (zSig z s - zSig w s) • (Gres H z s * Gres H w s) := by
  simp only [Gres_eq_green_zSig]
  exact green_eq_add_smul_mul hz hw

/-- The conjugate resolvent identity in the order `G(z) G(z̄)`, from `green_sub_green` (private
helper: the merged `green_sub_green_conj'` has the order `G(z̄) G(z)`). -/
private theorem green_sub_green_conj {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) :
    green H z - green H ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ)) • (green H z * green H ((starRingEnd ℂ) z)) := by
  rw [green_sub_green hz hz']
  congr 1
  rw [Complex.sub_conj]
  push_cast
  ring

end Spectral

section Telescope

variable {R : Type*} [Ring R]

/-- **(6.7)**, the telescoping product identity for noncommuting factors:
\[ \prod_{k<m}(a_k+b_k) = \prod_{k<m}a_k
    + \sum_{l<m}\Bigl(\prod_{j<l}(a_j+b_j)\Bigr)\,b_l\,\Bigl(\prod_{l<j<m}a_j\Bigr), \]
all products taken in increasing order of the index. -/
theorem list_prod_add_eq (a b : ℕ → R) (m : ℕ) :
    ((List.range m).map fun k => a k + b k).prod
      = ((List.range m).map a).prod
        + ∑ l ∈ Finset.range m, ((List.range l).map fun k => a k + b k).prod * b l
            * ((List.range' (l + 1) (m - (l + 1))).map a).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsuf : ∀ l ∈ Finset.range m,
        ((List.range' (l + 1) (m + 1 - (l + 1))).map a).prod
          = ((List.range' (l + 1) (m - (l + 1))).map a).prod * a m := by
      intro l hl
      have hl' : l < m := Finset.mem_range.mp hl
      have h1 : m + 1 - (l + 1) = (m - (l + 1)) + 1 := by omega
      have h2 : l + 1 + 1 * (m - (l + 1)) = m := by omega
      rw [h1, List.range'_concat, h2, List.map_append, List.prod_append]
      simp
    have hsum : ∑ l ∈ Finset.range m, ((List.range l).map fun k => a k + b k).prod * b l
            * ((List.range' (l + 1) (m + 1 - (l + 1))).map a).prod
          = (∑ l ∈ Finset.range m, ((List.range l).map fun k => a k + b k).prod * b l
            * ((List.range' (l + 1) (m - (l + 1))).map a).prod) * a m := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hsuf l hl]; simp only [mul_assoc]
    rw [Finset.sum_range_succ, hsum, List.range_succ, List.map_append, List.prod_append,
      List.map_append, List.prod_append, Nat.sub_self]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.range'_zero]
    rw [mul_add, ih, add_mul, add_mul]
    abel

end Telescope

section ChainExpansion

variable {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}

/-- The `l`-th term of the chain expansion (6.8): the mixed chain
`G_1 E_{a_1} ⋯ E_{a_{l-1}} G_l · G̃_l E_{a_l} G̃_{l+1} ⋯ E_{a_{m-1}} G̃_m`
(indices counted from `0` here), with `l+1` resolvents at `z` and `m-l` at `w = z̃`, and
no `E` between `G_l` and `G̃_l`. -/
noncomputable def gchainMixed (d L W : ℕ) [NeZero L] [NeZero W]
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z w : ℂ) (τ : List Bool)
    (a : List (Zd d L)) (l : ℕ) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  gchain d L W H z (τ.take (l + 1)) (a.take l) * gchain d L W H w (τ.drop l) (a.drop l)

/-- **(6.8)**, the chain expansion.  If every resolvent of the chain at `z` is expanded
around `w = z̃` by (6.3), then
\[ C_z = C_w + \sum_{l} (z_{σ_l} - w_{σ_l})\,
      G_1E_{a_1}\cdots G_l\cdot\tilde G_lE_{a_l}\cdots\tilde G_m . \]
This is (6.7) with `a_k + b_k ↦ G_k E_{a_k}`, `a_k ↦ G̃_k E_{a_k}`; we prove it directly
by induction on the chain. -/
theorem gchain_eq_add_sum_gchainMixed {z w : ℂ}
    (hz : ∀ s, IsUnit (H - zSig z s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hw : ∀ s, IsUnit (H - zSig w s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    {τ : List Bool} {a : List (Zd d L)} (h : τ.length = a.length + 1) :
    gchain d L W H z τ a = gchain d L W H w τ a
      + ∑ l ∈ Finset.range τ.length,
          (zSig z (τ.getD l true) - zSig w (τ.getD l true)) • gchainMixed d L W H z w τ a l := by
  induction τ generalizing a with
  | nil => simp at h
  | cons s τ ih =>
    cases a with
    | nil =>
      have hτ : τ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hτ
      simp only [gchainMixed, List.length_singleton, Finset.sum_range_one, List.getD_cons_zero,
        List.drop_zero, gchain_single, List.take_succ_cons, List.take_nil]
      exact Gres_eq_add_smul_mul (hz s) (hw s)
    | cons c a =>
      have h' : τ.length = a.length + 1 := by simpa using h
      have key : Gres H z s * Eblk d L W c * gchain d L W H w τ a
          = gchain d L W H w (s :: τ) (c :: a)
            + (zSig z s - zSig w s) • (Gres H z s * gchain d L W H w (s :: τ) (c :: a)) := by
        rw [gchain_cons]
        nth_rewrite 1 [Gres_eq_add_smul_mul (hz s) (hw s)]
        simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [gchain_cons, ih h', Matrix.mul_add, key, List.length_cons, Finset.sum_range_succ']
      simp only [gchainMixed, gchain_cons, List.take_succ_cons, List.drop_succ_cons,
        List.getD_cons_succ, List.getD_cons_zero, List.take_zero, List.drop_zero, gchain_single]
      simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.mul_assoc]
      abel

/-- The elementary Cauchy–Schwarz step behind (6.9):
`‖x + ∑_{l<m} y_l‖² ≤ (m+1)(‖x‖² + ∑_{l<m} ‖y_l‖²)`. -/
theorem norm_add_sum_sq_le {E : Type*} [SeminormedAddCommGroup E] (x : E) (y : ℕ → E)
    (m : ℕ) :
    ‖x + ∑ l ∈ Finset.range m, y l‖ ^ 2
      ≤ (m + 1 : ℝ) * (‖x‖ ^ 2 + ∑ l ∈ Finset.range m, ‖y l‖ ^ 2) := by
  set f : ℕ → ℝ := fun k => if k = 0 then ‖x‖ else ‖y (k - 1)‖ with hf
  have hsum : ∑ k ∈ Finset.range (m + 1), f k = ‖x‖ + ∑ l ∈ Finset.range m, ‖y l‖ := by
    rw [Finset.sum_range_succ', add_comm]
    simp [hf]
  have hsum2 : ∑ k ∈ Finset.range (m + 1), f k ^ 2
      = ‖x‖ ^ 2 + ∑ l ∈ Finset.range m, ‖y l‖ ^ 2 := by
    rw [Finset.sum_range_succ', add_comm]
    simp [hf]
  have h1 : ‖x + ∑ l ∈ Finset.range m, y l‖ ≤ ∑ k ∈ Finset.range (m + 1), f k := by
    rw [hsum]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1)) (f := f)
  rw [Finset.card_range, hsum2] at h2
  push_cast at h2
  calc ‖x + ∑ l ∈ Finset.range m, y l‖ ^ 2 ≤ (∑ k ∈ Finset.range (m + 1), f k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **(6.9)**, the termwise Cauchy–Schwarz bound: for every entry `(i, j)`,
\[ |(C_z)_{ij}|^2 \le (m+1)\Bigl(|(C_{w})_{ij}|^2
      + |z-w|^2\sum_{l<m}\bigl|(G_1E_{a_1}\cdots G_l\tilde G_l\cdots\tilde G_m)_{ij}\bigr|^2\Bigr),
\]
`m` the number of resolvents in the chain.  The paper's `C_m` is `m + 1` here. -/
theorem norm_gchain_apply_sq_le {z w : ℂ}
    (hz : ∀ s, IsUnit (H - zSig z s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hw : ∀ s, IsUnit (H - zSig w s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    {τ : List Bool} {a : List (Zd d L)} (h : τ.length = a.length + 1)
    (i j : Vtx d L W) :
    ‖gchain d L W H z τ a i j‖ ^ 2
      ≤ (τ.length + 1 : ℝ) * (‖gchain d L W H w τ a i j‖ ^ 2
          + ‖z - w‖ ^ 2 *
            ∑ l ∈ Finset.range τ.length, ‖gchainMixed d L W H z w τ a l i j‖ ^ 2) := by
  have hij := congrFun (congrFun (gchain_eq_add_sum_gchainMixed hz hw h) i) j
  rw [Matrix.add_apply, Matrix.sum_apply] at hij
  rw [hij]
  refine (norm_add_sum_sq_le _ _ _).trans_eq ?_
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_zSig_sub_zSig, mul_pow]

end ChainExpansion

section SymmetricLoop

variable {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {z : ℂ}

omit [NeZero W] in
/-- **(6.5)**, the symmetric loop in normal form:
\[ \mathcal L_{σ',a'} = \langle E_{a_0}\,C_{σ,a}\,E_{a_m}\,C_{σ,a}^\dagger\rangle, \]
with `σ' = (σ_1, …, σ_m, \bar σ_m, …, \bar σ_1)` and
`a' = (a_1, …, a_{m-1}, a_m, a_{m-1}, …, a_1, a_0)`. -/
theorem gloop_symm_eq_trace (hH : H.IsHermitian) {τ : List Bool} {a : List (Zd d L)}
    (h : τ.length = a.length + 1) (am a0 : Zd d L) :
    loopL d L W H z ⟨τ ++ (τ.map (!·)).reverse, (a ++ [am]) ++ (a.reverse ++ [a0])⟩
      = Matrix.trace (Eblk d L W a0 * gchain d L W H z τ a * Eblk d L W am
          * (gchain d L W H z τ a)ᴴ) := by
  have h' : (τ.map (!·)).reverse.length = a.reverse.length + 1 := by simpa using h
  have hlen : τ.length = (a ++ [am]).length := by simpa using h
  rw [gchain_conjTranspose hH h, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (Eblk d L W a0), gchain_mul_Eblk h,
    gchain_mul_Eblk h', cad_loopL_eq, cad_gloopProd_append hlen]

omit [NeZero W] in
/-- A chain ending in `G(s)` is the loop product of its first blocks times `G(s)`. -/
theorem gchain_append_singleton {ρ : List Bool} {b : List (Zd d L)} (h : ρ.length = b.length)
    (s : Bool) :
    gchain d L W H z (ρ ++ [s]) b = gloopProd d L W H z ⟨ρ, b⟩ * Gres H z s := by
  induction ρ generalizing b with
  | nil =>
    obtain rfl : b = [] := List.eq_nil_of_length_eq_zero h.symm
    simp [cad_gloopProd_nil]
  | cons r ρ ih =>
    cases b with
    | nil => simp at h
    | cons c b =>
      have h' : ρ.length = b.length := by simpa using h
      rw [List.cons_append, gchain_cons, ih h', cad_gloopProd_cons]
      simp only [Matrix.mul_assoc]

omit [NeZero W] in
/-- `2iη·G(σ)G(σ)† = G(+) - G(-)` for either charge `σ`: the resolvent form of Ward's
identity `G G† = (G - G†)/(2i Im z)` used twice in §6. -/
theorem Gres_mul_conjTranspose (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (s : Bool) :
    (2 * Complex.I * (z.im : ℂ)) • (Gres H z s * (Gres H z s)ᴴ)
      = Gres H z true - Gres H z false := by
  rw [cad_Gres_conjTranspose hH]
  cases s
  · simp only [Bool.not_false, cad_Gres_true, cad_Gres_false]
    exact (green_sub_green_conj' hz hz').symm
  · simp only [Bool.not_true, cad_Gres_true, cad_Gres_false]
    exact (green_sub_green_conj hz hz').symm

omit [NeZero W] in
/-- `⟨E_{a₀} P P†⟩ = W^{-d} ∑_{i ∈ I_{a₀}} ‖P_{i·}‖²`: the trace against a block projection
is the averaged squared row norm. -/
theorem trace_Eblk_mul_mul_conjTranspose (P : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (a0 : Zd d L) :
    Matrix.trace (Eblk d L W a0 * P * Pᴴ)
      = ((W : ℂ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k : Vtx d L W,
          (Complex.normSq (P (a0, α) k) : ℂ) := by
  have hdiag : ∀ p : Vtx d L W, (Eblk d L W a0 * P * Pᴴ) p p
      = if p.1 = a0 then ((W : ℂ) ^ d)⁻¹ * ∑ k, (Complex.normSq (P p k) : ℂ) else 0 := by
    intro p
    rw [Matrix.mul_assoc, Eblk, Matrix.diagonal_mul]
    split_ifs
    · congr 1
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
    · simp
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hdiag]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a0]
  · simp [Finset.mul_sum]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ a0) h

omit [NeZero W] in
/-- Closing a half-chain around `G(s')` gives a symmetric loop of odd length:
`⟨E_{a₀} Q G(s') Q†⟩ = L_{(ρ, s', \bar ρ^{rev}), (b, b^{rev}, a₀)}` with
`Q = G_1E_{b_1}⋯G_kE_{b_k}`. -/
theorem trace_Eblk_gloopProd_Gsig_conjTranspose (hH : H.IsHermitian) {ρ : List Bool}
    {b : List (Zd d L)} (h : ρ.length = b.length) (s : Bool) (a0 : Zd d L) :
    Matrix.trace (Eblk d L W a0 * gloopProd d L W H z ⟨ρ, b⟩ * Gres H z s
        * (gloopProd d L W H z ⟨ρ, b⟩)ᴴ)
      = loopL d L W H z ⟨ρ ++ s :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  have hG : Gres H z s * (gloopProd d L W H z ⟨ρ, b⟩)ᴴ
      = gchain d L W H z (s :: (ρ.map (!·)).reverse) b.reverse := by
    have hc := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH
      (tau := ρ ++ [!s]) (a := b) (by simpa using h)
    rw [gchain_append_singleton h, Matrix.conjTranspose_mul, cad_Gres_conjTranspose hH,
      Bool.not_not] at hc
    rw [hc]
    simp
  have h' : (s :: (ρ.map (!·)).reverse).length = b.reverse.length + 1 := by simpa using h
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.trace_mul_comm, Matrix.mul_assoc,
    gchain_mul_Eblk h', cad_loopL_eq, cad_gloopProd_append h]

omit [NeZero W] in
/-- **(6.12)**, the Ward step.  With `v^{(l)}_k = (G_1E_{a_1}⋯E_{a_{l-1}}G_l)_{ik}`,
\[ 2i\operatorname{Im}z\cdot W^{-d}\sum_{i\in I_{a_0}}\|v^{(l)}\|_2^2
    = \mathcal L_{σ^{(1)}_l, \mathbf a_l} - \mathcal L_{σ^{(2)}_l, \mathbf a_l}, \]
where `σ^{(1,2)}_l = (σ_1, …, σ_{l-1}, ±, \bar σ_{l-1}, …, \bar σ_1)` and
`a_l = (a_1, …, a_{l-1}, a_{l-1}, …, a_1, a_0)` (a rotation of the paper's labelling).
Here the chain is `gchain (ρ ++ [s]) b` with `ρ = (σ_1, …, σ_{l-1})`, `s = σ_l`,
`b = (a_1, …, a_{l-1})`; the right side does not depend on `s`. -/
theorem ward_chain_row (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    {ρ : List Bool} {b : List (Zd d L)} (h : ρ.length = b.length) (s : Bool) (a0 : Zd d L) :
    (2 * Complex.I * (z.im : ℂ)) * (((W : ℂ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k : Vtx d L W,
        (Complex.normSq (gchain d L W H z (ρ ++ [s]) b (a0, α) k) : ℂ))
      = loopL d L W H z ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
        - loopL d L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  rw [← trace_Eblk_mul_mul_conjTranspose, ← trace_Eblk_gloopProd_Gsig_conjTranspose hH h,
    ← trace_Eblk_gloopProd_Gsig_conjTranspose hH h, ← Matrix.trace_sub, ← smul_eq_mul,
    ← Matrix.trace_smul, gchain_append_singleton h, Matrix.conjTranspose_mul]
  congr 1
  set Q := gloopProd d L W H z ⟨ρ, b⟩
  have hW := Gres_mul_conjTranspose hH hz hz' s
  calc (2 * Complex.I * (z.im : ℂ)) • (Eblk d L W a0 * (Q * Gres H z s) * ((Gres H z s)ᴴ * Qᴴ))
      = Eblk d L W a0 * Q * ((2 * Complex.I * (z.im : ℂ)) • (Gres H z s * (Gres H z s)ᴴ))
          * Qᴴ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hW, Matrix.mul_sub, Matrix.sub_mul]

omit [NeZero W] in
/-- **(6.12)** in the paper's form, solved for the row norms:
`W^{-d} ∑_{i ∈ I_{a₀}} ‖v^{(l)}‖² = (2i Im z)⁻¹ (L_{σ^{(1)}} - L_{σ^{(2)}})`. -/
theorem ward_chain_row' (hH : H.IsHermitian) (hη : z.im ≠ 0)
    {ρ : List Bool} {b : List (Zd d L)} (h : ρ.length = b.length) (s : Bool) (a0 : Zd d L) :
    ((W : ℂ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k : Vtx d L W,
        (Complex.normSq (gchain d L W H z (ρ ++ [s]) b (a0, α) k) : ℂ)
      = (2 * Complex.I * (z.im : ℂ))⁻¹
        * (loopL d L W H z ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
          - loopL d L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩) := by
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    simp [Complex.I_ne_zero, hη]
  rw [eq_inv_mul_iff_mul_eq₀ hc]
  exact ward_chain_row hH (isUnit_sub_smul_one_of_im_ne_zero hH hη)
    (isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hη)) h s a0

end SymmetricLoop

section Arithmetic

/-- The shifted spectral parameter of §6: `z̃_{t₁} := (t₂/t₁)^{1/2} z_{t₁}`. -/
noncomputable def ztTilde (E t₁ t₂ : ℝ) : ℂ := (Real.sqrt (t₂ / t₁) : ℂ) * zt E t₁

theorem ztTilde_im (E t₁ t₂ : ℝ) :
    (ztTilde E t₁ t₂).im = Real.sqrt (t₂ / t₁) * Gauss.etaT E t₁ := by
  rw [ztTilde, Complex.im_ofReal_mul, zt_im, Gauss.etaT]

theorem etaT_nonneg (E : ℝ) {t : ℝ} (ht : t ≤ 1) : 0 ≤ Gauss.etaT E t := by
  rw [Gauss.etaT, mE_im]
  have : 0 ≤ 1 - t := by linarith
  positivity

/-- In the bulk `|E| ≤ 2 - κ`, `Im m^{(E)} ≥ κ/2`. -/
theorem half_le_mE_im {E κ : ℝ} (hκ : 0 ≤ κ) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have : κ ≤ Real.sqrt (4 - E ^ 2) := by
    rw [Real.le_sqrt hκ (by nlinarith)]
    nlinarith
  linarith

variable {c E t₁ t₂ : ℝ}

/-- `1 ≤ (t₂/t₁)^{1/2} ≤ t₂/t₁ ≤ c⁻¹` and `(t₂/t₁)^{1/2} - 1 ≤ (t₂-t₁)/c`. -/
theorem sqrt_div_bounds (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) :
    1 ≤ Real.sqrt (t₂ / t₁) ∧ Real.sqrt (t₂ / t₁) ≤ c⁻¹
      ∧ Real.sqrt (t₂ / t₁) - 1 ≤ (t₂ - t₁) / c := by
  have ht₁ : 0 < t₁ := lt_of_lt_of_le hc h₁
  have hq : 1 ≤ t₂ / t₁ := (one_le_div ht₁).mpr h₁₂
  have hs1 : 1 ≤ Real.sqrt (t₂ / t₁) := Real.one_le_sqrt.mpr hq
  have hsq : Real.sqrt (t₂ / t₁) ^ 2 = t₂ / t₁ := Real.sq_sqrt (by linarith)
  have hle : Real.sqrt (t₂ / t₁) ≤ t₂ / t₁ := by nlinarith
  have hq' : t₂ / t₁ ≤ c⁻¹ := by
    rw [div_le_iff₀ ht₁]
    calc t₂ ≤ 1 := h₂
      _ = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ c⁻¹ * t₁ := mul_le_mul_of_nonneg_left h₁ (inv_nonneg.mpr hc.le)
  refine ⟨hs1, hle.trans hq', ?_⟩
  have h1 : Real.sqrt (t₂ / t₁) - 1 ≤ t₂ / t₁ - 1 := by linarith
  have h2 : t₂ / t₁ - 1 = (t₂ - t₁) / t₁ := by field_simp
  have h3 : (t₂ - t₁) / t₁ ≤ (t₂ - t₁) / c :=
    div_le_div_of_nonneg_left (by linarith) hc h₁
  linarith

/-- `Im z̃_{t₁} ≍ Im z_{t₁}`: `η_{t₁} ≤ Im z̃_{t₁} ≤ c⁻¹ η_{t₁}`. -/
theorem etaT_le_ztTilde_im (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) :
    Gauss.etaT E t₁ ≤ (ztTilde E t₁ t₂).im ∧ (ztTilde E t₁ t₂).im ≤ c⁻¹ * Gauss.etaT E t₁ := by
  obtain ⟨hs1, hsc, -⟩ := sqrt_div_bounds hc h₁ h₁₂ h₂
  have hη := etaT_nonneg E (h₁₂.trans h₂)
  rw [ztTilde_im]
  constructor
  · nlinarith
  · exact mul_le_mul_of_nonneg_right hsc hη

/-- `|z_{t₂} - z̃_{t₁}| ≤ C (t₂ - t₁)` with `C = 3/c + 1`. -/
theorem norm_zt_sub_ztTilde_le (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1)
    (hE : |E| ≤ 2) : ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (t₂ - t₁) := by
  obtain ⟨hs1, -, hs⟩ := sqrt_div_bounds hc h₁ h₁₂ h₂
  set s := Real.sqrt (t₂ / t₁)
  have hm := Gauss.norm_spectralM hE
  have hkey : zt E t₂ - ztTilde E t₁ t₂
      = ((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E)
        - ((t₂ - t₁ : ℝ) : ℂ) * mE E := by
    simp only [zt, ztTilde, s]
    push_cast
    ring
  have ht₁ : 1 - t₁ ≤ 1 := by linarith [lt_of_lt_of_le hc h₁]
  have ht₁' : 0 ≤ 1 - t₁ := by linarith
  have hin : ‖(E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E‖ ≤ 3 := by
    calc ‖(E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E‖
        ≤ ‖(E : ℂ)‖ + ‖((1 - t₁ : ℝ) : ℂ) * mE E‖ := norm_add_le _ _
      _ = |E| + (1 - t₁) := by
          rw [norm_mul, hm, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_of_nonneg ht₁', mul_one]
      _ ≤ 3 := by linarith
  rw [hkey]
  calc ‖((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E)
        - ((t₂ - t₁ : ℝ) : ℂ) * mE E‖
      ≤ ‖((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E)‖
        + ‖((t₂ - t₁ : ℝ) : ℂ) * mE E‖ := norm_sub_le _ _
    _ ≤ (s - 1) * 3 + (t₂ - t₁) := by
        rw [norm_mul, norm_mul, hm, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonpos (by linarith), Real.norm_of_nonneg (by linarith), mul_one]
        have := mul_le_mul_of_nonneg_left hin (by linarith : 0 ≤ -(1 - s))
        linarith
    _ ≤ 3 * ((t₂ - t₁) / c) + (t₂ - t₁) := by linarith
    _ = (3 / c + 1) * (t₂ - t₁) := by ring

/-- `|z_{t₂} - z̃_{t₁}| ≤ C (1 - t₁)`, the form stated in §6. -/
theorem norm_zt_sub_ztTilde_le_one_sub (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ 1) (hE : |E| ≤ 2) :
    ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (1 - t₁) := by
  refine (norm_zt_sub_ztTilde_le hc h₁ h₁₂ h₂ hE).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- In the bulk, `|z_{t₂} - z̃_{t₁}| ≤ C η_{t₁}` with `C = (3/c + 1)·(2/κ)`. -/
theorem norm_zt_sub_ztTilde_le_etaT {κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (h₁ : c ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) (hE : |E| ≤ 2 - κ) :
    ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (2 / κ) * Gauss.etaT E t₁ := by
  refine (norm_zt_sub_ztTilde_le_one_sub hc h₁ h₁₂ h₂ (by linarith)).trans ?_
  have hm := half_le_mE_im hκ.le hE
  have ht : 0 ≤ 1 - t₁ := by linarith
  have h1 : 1 - t₁ ≤ 2 / κ * Gauss.etaT E t₁ := by
    rw [Gauss.etaT, div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **The arithmetic of `z̃_{t₁}` in §6.**  For `c ≤ t₁ ≤ t₂ ≤ 1` and `|E| ≤ 2 - κ`:
\[ |z_{t_2}-\tilde z_{t_1}| \le C(1-t_1),\quad |z_{t_2}-\tilde z_{t_1}|^2 \le C\eta_{t_1}^2,
    \quad \frac{|z_{t_2}-\tilde z_{t_1}|^2}{\operatorname{Im}\tilde z_{t_1}} \le C\eta_{t_1},
    \quad \eta_{t_1}\le\operatorname{Im}\tilde z_{t_1}\le C\eta_{t_1}. \]
The constant depends only on `c` and `κ`. -/
theorem ztTilde_arith {κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∃ C > 0, ∀ E t₁ t₂ : ℝ, c ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 → |E| ≤ 2 - κ →
      ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ C * (1 - t₁)
      ∧ ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ C * Gauss.etaT E t₁ ^ 2
      ∧ ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 / (ztTilde E t₁ t₂).im ≤ C * Gauss.etaT E t₁
      ∧ Gauss.etaT E t₁ ≤ (ztTilde E t₁ t₂).im
      ∧ (ztTilde E t₁ t₂).im ≤ C * Gauss.etaT E t₁ := by
  set K := (3 / c + 1) * (2 / κ) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨(3 / c + 1) + K ^ 2 + c⁻¹, by positivity, ?_⟩
  intro E t₁ t₂ h₁ h₁₂ h₂ hE
  have hη := etaT_nonneg E (h₁₂.trans h₂)
  have hd := norm_zt_sub_ztTilde_le_etaT hc hκ h₁ h₁₂ h₂ hE
  have hd' := norm_zt_sub_ztTilde_le_one_sub hc h₁ h₁₂ h₂ (by linarith)
  obtain ⟨hIm1, hIm2⟩ := etaT_le_ztTilde_im (E := E) hc h₁ h₁₂ h₂
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have ht : 0 ≤ 1 - t₁ := by linarith
  have h3 : 0 ≤ 3 / c + 1 := by positivity
  have hC1 : K ^ 2 ≤ (3 / c + 1) + K ^ 2 + c⁻¹ := by linarith
  have hC2 : c⁻¹ ≤ (3 / c + 1) + K ^ 2 + c⁻¹ := by linarith
  have hsq : ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ K ^ 2 * Gauss.etaT E t₁ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  refine ⟨?_, ?_, ?_, hIm1, ?_⟩
  · refine hd'.trans ?_
    nlinarith
  · exact hsq.trans (mul_le_mul_of_nonneg_right hC1 (sq_nonneg _))
  · refine div_le_of_le_mul₀ (hη.trans hIm1) (by positivity) ?_
    calc ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ K ^ 2 * Gauss.etaT E t₁ ^ 2 := hsq
      _ = (K ^ 2 * Gauss.etaT E t₁) * Gauss.etaT E t₁ := by ring
      _ ≤ ((3 / c + 1) + K ^ 2 + c⁻¹) * Gauss.etaT E t₁ * (ztTilde E t₁ t₂).im := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hC1 hη) hIm1 hη (by positivity)
  · exact hIm2.trans (mul_le_mul_of_nonneg_right hC2 hη)

end Arithmetic

section LoopProd

variable {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {z : ℂ}

variable (d L W) in
/-- `M` is the loop product `∏_i G(σ_i) E_{a_i}` of some loop index of length `r`. -/
def IsGLoopProd (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (r : ℕ)
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) : Prop :=
  ∃ I : Loop.LoopIdx (Zd d L), I.σ.length = r ∧ I.a.length = r ∧ M = gloopProd d L W H z I

omit [NeZero W] in
theorem isGLoopProd_one : IsGLoopProd d L W H z 0 1 :=
  ⟨⟨[], []⟩, rfl, rfl, cad_gloopProd_nil.symm⟩

omit [NeZero W] in
theorem IsGLoopProd.mul {r r' : ℕ} {M M' : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (h : IsGLoopProd d L W H z r M) (h' : IsGLoopProd d L W H z r' M') :
    IsGLoopProd d L W H z (r + r') (M * M') := by
  obtain ⟨⟨σ, a⟩, hσ, ha, rfl⟩ := h
  obtain ⟨⟨σ', a'⟩, hσ', ha', rfl⟩ := h'
  refine ⟨⟨σ ++ σ', a ++ a'⟩, by simp_all, by simp_all, ?_⟩
  exact (cad_gloopProd_append (by simp_all) σ' a').symm

omit [NeZero W] in
theorem IsGLoopProd.norm_trace_le {r : ℕ} {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (h : IsGLoopProd d L W H z r M) : ‖trace M‖ ≤ loopMax d L W H z r := by
  obtain ⟨I, hσ, ha, rfl⟩ := h
  exact norm_gloop_le_loopMax I hσ ha

omit [NeZero W] in
/-- The trace of a power of `c(Z₊ - Z₋)`, `Z_±` loop products of length `q`, times a loop
product of length `r`, is bounded by `(2|c|)^j max|L^{(jq+r)}|`: expand one factor at a time. -/
theorem norm_trace_smul_sub_pow_mul_le {q : ℕ} {Zp Zm : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hp : IsGLoopProd d L W H z q Zp) (hm : IsGLoopProd d L W H z q Zm) {c : ℂ} {β : ℝ}
    (hβ : 2 * ‖c‖ ≤ β) (j : ℕ) :
    ∀ {r : ℕ} {R : Matrix (Vtx d L W) (Vtx d L W) ℂ}, IsGLoopProd d L W H z r R →
      ‖trace ((c • (Zp - Zm)) ^ j * R)‖ ≤ β ^ j * loopMax d L W H z (j * q + r) := by
  have hβ0 : 0 ≤ β := le_trans (by positivity) hβ
  induction j with
  | zero =>
    intro r R hR
    simpa using hR.norm_trace_le
  | succ j ih =>
    intro r R hR
    have e : (j + 1) * q + r = j * q + (q + r) := by ring
    rw [pow_succ, Matrix.mul_assoc, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_sub, trace_smul, trace_sub, e, norm_smul]
    have h1 := ih (hp.mul hR)
    have h2 := ih (hm.mul hR)
    calc ‖c‖ * ‖trace ((c • (Zp - Zm)) ^ j * (Zp * R)) - trace ((c • (Zp - Zm)) ^ j * (Zm * R))‖
        ≤ ‖c‖ * (β ^ j * loopMax d L W H z (j * q + (q + r))
            + β ^ j * loopMax d L W H z (j * q + (q + r))) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (norm_nonneg _)
      _ = (2 * ‖c‖) * (β ^ j * loopMax d L W H z (j * q + (q + r))) := by ring
      _ ≤ β * (β ^ j * loopMax d L W H z (j * q + (q + r))) :=
          mul_le_mul_of_nonneg_right hβ (mul_nonneg (pow_nonneg hβ0 _) (loopMax_nonneg _))
      _ = _ := by ring

end LoopProd

section Ward

variable {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {z : ℂ}

omit [NeZero W] in
/-- The matrix form of closing a half-chain around `G(s)`:
`Q G(s) Q† E_{a₀} = ∏ G E` over the index `(ρ, s, \bar ρ^{rev}), (b, b^{rev}, a₀)`. -/
theorem gloopProd_Gsig_conjTranspose_Eblk (hH : H.IsHermitian) {ρ : List Bool}
    {b : List (Zd d L)} (h : ρ.length = b.length) (s : Bool) (a0 : Zd d L) :
    gloopProd d L W H z ⟨ρ, b⟩ * Gres H z s * (gloopProd d L W H z ⟨ρ, b⟩)ᴴ * Eblk d L W a0
      = gloopProd d L W H z ⟨ρ ++ s :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  have hG : Gres H z s * (gloopProd d L W H z ⟨ρ, b⟩)ᴴ
      = gchain d L W H z (s :: (ρ.map (!·)).reverse) b.reverse := by
    have hc := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH
      (tau := ρ ++ [!s]) (a := b) (by simpa using h)
    rw [gchain_append_singleton h, Matrix.conjTranspose_mul, cad_Gres_conjTranspose hH,
      Bool.not_not] at hc
    rw [hc]
    simp
  have h' : (s :: (ρ.map (!·)).reverse).length = b.reverse.length + 1 := by simpa using h
  rw [Matrix.mul_assoc (gloopProd d L W H z ⟨ρ, b⟩), hG, Matrix.mul_assoc, gchain_mul_Eblk h',
    ← cad_gloopProd_append h]

omit [NeZero W] in
/-- **Ward's identity for the Gram matrix of (6.10).**  For a chain `Y` with `k` resolvents,
`Y† Y E_b = (2i Im z)⁻¹ (Z₊ - Z₋)` with `Z_±` loop products of length `2k - 1`. -/
theorem exists_conjTranspose_mul_Eblk (hH : H.IsHermitian) (hz : z.im ≠ 0) {τ : List Bool}
    {c : List (Zd d L)} (h : τ.length = c.length + 1) (b : Zd d L) :
    ∃ Zp Zm : Matrix (Vtx d L W) (Vtx d L W) ℂ,
      IsGLoopProd d L W H z (2 * τ.length - 1) Zp ∧ IsGLoopProd d L W H z (2 * τ.length - 1) Zm ∧
      (gchain d L W H z τ c)ᴴ * gchain d L W H z τ c * Eblk d L W b
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Zp - Zm) := by
  have hY := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH h
  set τ' := (τ.map (!·)).reverse with hτ'
  have hlen : τ'.length = τ.length := by simp [hτ']
  rcases List.eq_nil_or_concat' τ' with h0 | ⟨ρ, s, hρ⟩
  · rw [h0] at hlen; simp at hlen; omega
  have hρτ : ρ.length + 1 = τ.length := by
    have := congrArg List.length hρ
    rw [List.length_append, List.length_singleton] at this
    omega
  have hρlen : ρ.length = c.reverse.length := by
    rw [List.length_reverse]; omega
  have hQ : gchain d L W H z τ' c.reverse = gloopProd d L W H z ⟨ρ, c.reverse⟩ * Gres H z s := by
    rw [hρ, gchain_append_singleton hρlen]
  set Q := gloopProd d L W H z ⟨ρ, c.reverse⟩
  have hY2 : gchain d L W H z τ c = (Q * Gres H z s)ᴴ := by
    rw [← hQ, ← hY, conjTranspose_conjTranspose]
  have hYY : (gchain d L W H z τ c)ᴴ * gchain d L W H z τ c
      = Q * (Gres H z s * (Gres H z s)ᴴ) * Qᴴ := by
    rw [hY2, conjTranspose_conjTranspose, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hW := Gres_mul_conjTranspose (z := z) hH (isUnit_sub_smul_one_of_im_ne_zero hH hz)
    (isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz)) s
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have hGG : Gres H z s * (Gres H z s)ᴴ
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gres H z true - Gres H z false) := by
    rw [← hW, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hlen2 : ∀ t : Bool, (ρ ++ t :: (ρ.map (!·)).reverse).length = 2 * τ.length - 1 := by
    intro t; simp; omega
  have hlen3 : (c.reverse ++ (c.reverse.reverse ++ [b])).length = 2 * τ.length - 1 := by
    simp; omega
  refine ⟨_, _,
    ⟨⟨ρ ++ true :: (ρ.map (!·)).reverse, c.reverse ++ (c.reverse.reverse ++ [b])⟩,
      hlen2 true, hlen3, rfl⟩,
    ⟨⟨ρ ++ false :: (ρ.map (!·)).reverse, c.reverse ++ (c.reverse.reverse ++ [b])⟩,
      hlen2 false, hlen3, rfl⟩, ?_⟩
  rw [← gloopProd_Gsig_conjTranspose_Eblk hH hρlen, ← gloopProd_Gsig_conjTranspose_Eblk hH hρlen,
    hYY, hGG, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.sub_mul]

omit [NeZero W] in
/-- **(6.12) as an inequality**: `W^{-d} ∑_{i ∈ I_{a₀}} ‖v^{(l)}‖² ≤ (Im z)⁻¹ max|L^{(2l-1)}|`,
where `v^{(l)}` is the row `i` of a chain with `l` resolvents. -/
theorem sum_norm_gchain_row_sq_le (hH : H.IsHermitian) (hz : 0 < z.im) {ρ : List Bool}
    {b : List (Zd d L)} (h : ρ.length = b.length) (s : Bool) (a0 : Zd d L) :
    ((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k : Vtx d L W,
        ‖gchain d L W H z (ρ ++ [s]) b (a0, α) k‖ ^ 2
      ≤ (z.im)⁻¹ * loopMax d L W H z (2 * ρ.length + 1) := by
  have hw := ward_chain_row' (H := H) hH hz.ne' h s a0
  set S : ℝ := ((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k : Vtx d L W,
    ‖gchain d L W H z (ρ ++ [s]) b (a0, α) k‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hSC : (S : ℂ) = ((W : ℂ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k : Vtx d L W,
      (Complex.normSq (gchain d L W H z (ρ ++ [s]) b (a0, α) k) : ℂ) := by
    rw [hS]
    simp only [← Complex.sq_norm]
    push_cast
    rfl
  have hlen : ∀ t : Bool, (ρ ++ t :: (ρ.map (!·)).reverse).length = 2 * ρ.length + 1 := by
    intro t; simp; ring
  have hlen' : (b ++ (b.reverse ++ [a0])).length = 2 * ρ.length + 1 := by simp [h]; ring
  have h1 := norm_gloop_le_loopMax (L := L) (W := W) (H := H) (z := z)
    ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ (hlen true) hlen'
  have h2 := norm_gloop_le_loopMax (L := L) (W := W) (H := H) (z := z)
    ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ (hlen false) hlen'
  have hnc : ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ = (2 * z.im)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hz.le]
    norm_num
  calc S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hS0]
    _ = ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ * ‖loopL d L W H z
          ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
        - loopL d L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩‖ := by
        rw [hSC, hw, norm_mul]
    _ ≤ (2 * z.im)⁻¹ * (loopMax d L W H z (2 * ρ.length + 1)
          + loopMax d L W H z (2 * ρ.length + 1)) := by
        rw [hnc]
        exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
          (by positivity)
    _ = _ := by field_simp; ring

end Ward

section Gram

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The columns `Y_{·,(b,β)}`, `β ∈ Fin (W ^ d)`, of a matrix, as vectors of `ℓ²`: the vectors
`w^{(l)}_j`, `j ∈ I_b`, of (6.10). -/
noncomputable def blockCols (Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) :
    Fin (W ^ d) → EuclideanSpace ℂ (Vtx d L W) :=
  fun β => WithLp.toLp 2 (fun k => Y k (b, β))

/-- The selection matrix `R_{x,β} = 1(x = (b,β))` of the block `I_b`. -/
noncomputable def blockSel (b : Zd d L) : Matrix (Vtx d L W) (Fin (W ^ d)) ℂ :=
  Matrix.of fun x β => if x = (b, β) then 1 else 0

omit [NeZero W] in
theorem gram_blockCols (Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) :
    gram ℂ (blockCols Y b) = (blockSel b)ᵀ * (Yᴴ * Y) * blockSel b := by
  ext β β'
  simp [gram_apply, blockCols, PiLp.inner_apply, blockSel, Matrix.mul_apply, mul_comm]

omit [NeZero L] in
theorem blockSel_mul_transpose (b : Zd d L) :
    blockSel (W := W) b * (blockSel b)ᵀ = ((W : ℂ) ^ d) • Eblk d L W b := by
  ext x y
  simp only [blockSel, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Eblk,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = b
    · rw [Finset.sum_eq_single x.2]
      · simp [hx, Prod.ext_iff]
      · intro β _ hβ; simp [Prod.ext_iff, hβ.symm]
      · simp
    · simp [hx, Prod.ext_iff]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hxy)]
    simp only [mul_ite, mul_one, mul_zero]
    refine Finset.sum_eq_zero fun β _ => ?_
    split_ifs with h1 h2 <;>
      first | rfl | exact absurd (h1.trans h2.symm) hxy | exact absurd (h1.trans h2.symm).symm hxy

omit [NeZero W] in
theorem transpose_blockSel_mul (b : Zd d L) :
    (blockSel (W := W) b)ᵀ * blockSel (W := W) b = 1 := by
  ext β β'
  simp [blockSel, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem trace_transpose_mul_mul_pow_succ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (R : Matrix m n ℂ) (K : Matrix m m ℂ) (p : ℕ) :
    trace ((Rᵀ * K * R) ^ (p + 1)) = trace ((K * (R * Rᵀ)) ^ (p + 1)) := by
  have key : ∀ p : ℕ, (Rᵀ * K * R) ^ (p + 1) = Rᵀ * ((K * (R * Rᵀ)) ^ p * K * R) := by
    intro p
    induction p with
    | zero => simp [Matrix.mul_assoc]
    | succ p ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [key, trace_mul_comm, pow_succ]
  simp only [Matrix.mul_assoc]

/-- `tr (A^{p+1}) = (W^d)^{p+1} tr ((Y†Y E_b)^{p+1})` for the Gram matrix `A` of the block
columns of `Y` (the identity behind "`(2i Im z / W^d)^p tr A^p` is a sum of loops" in §6). -/
theorem trace_gram_blockCols_pow (Y : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L)
    (p : ℕ) :
    trace (gram ℂ (blockCols Y b) ^ (p + 1))
      = ((W : ℂ) ^ d) ^ (p + 1) * trace ((Yᴴ * Y * Eblk d L W b) ^ (p + 1)) := by
  rw [gram_blockCols, trace_transpose_mul_mul_pow_succ, blockSel_mul_transpose, Matrix.mul_smul,
    smul_pow, trace_smul, smul_eq_mul]

omit [NeZero W] in
/-- `∑_i bw_b(i) f(i) = W^{-d} ∑_{α ∈ Fin (W^d)} f(b, α)`. -/
theorem sum_bw_mul (b : Zd d L) (f : Vtx d L W → ℝ) :
    ∑ i, bw b i * f i = ((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), f (b, α) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [bw, Finset.mul_sum]
  · intro c _ hc; simp [bw, hc]
  · simp

end Gram

section Six10

variable {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}

/-- The `ℓ²` bound on the Gram matrix of (6.10): for a chain `Y` with `k` resolvents at `w`
and `p ≥ 1`, `(tr A^p)^{1/p} ≤ W^d (Im w)⁻¹ (max|L_w^{(p(2k-1))}|)^{1/p}`. -/
theorem trace_gram_rpow_le (hH : H.IsHermitian) {w : ℂ} (hw : 0 < w.im) {τ : List Bool}
    {c : List (Zd d L)} (h : τ.length = c.length + 1) (b : Zd d L) {p : ℕ} (hp : 1 ≤ p) :
    (trace (gram ℂ (blockCols (gchain d L W H w τ c) b) ^ p)).re ^ (1 / (p : ℝ))
      ≤ (W : ℝ) ^ d * (w.im)⁻¹ * loopMax d L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  set Y := gchain d L W H w τ c
  set LM := loopMax d L W H w ((p' + 1) * (2 * τ.length - 1))
  obtain ⟨Zp, Zm, hZp, hZm, hK⟩ := exists_conjTranspose_mul_Eblk hH hw.ne' h b
  have hc : 2 * ‖(2 * Complex.I * (w.im : ℂ))⁻¹‖ ≤ (w.im)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hw.le]
    field_simp
    norm_num
  have hb : ‖trace ((Yᴴ * Y * Eblk d L W b) ^ (p' + 1))‖ ≤ (w.im)⁻¹ ^ (p' + 1) * LM := by
    rw [hK]
    have := norm_trace_smul_sub_pow_mul_le hZp hZm hc (p' + 1) (isGLoopProd_one (L := L) (W := W)
      (H := H) (z := w))
    simpa using this
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hLM : 0 ≤ LM := loopMax_nonneg _
  have hnorm : ‖trace (gram ℂ (blockCols Y b) ^ (p' + 1))‖
      ≤ ((W : ℝ) ^ d * (w.im)⁻¹) ^ (p' + 1) * LM := by
    rw [trace_gram_blockCols_pow, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, mul_pow,
      mul_assoc (((W : ℝ) ^ d) ^ (p' + 1))]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hp0 : ((p' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  set x := (trace (gram ℂ (blockCols Y b) ^ (p' + 1))).re
  calc x ^ (1 / ((p' + 1 : ℕ) : ℝ)) ≤ |x ^ (1 / ((p' + 1 : ℕ) : ℝ))| := le_abs_self _
    _ ≤ |x| ^ (1 / ((p' + 1 : ℕ) : ℝ)) := Real.abs_rpow_le_abs_rpow _ _
    _ ≤ (((W : ℝ) ^ d * (w.im)⁻¹) ^ (p' + 1) * LM) ^ (1 / ((p' + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) ((Complex.abs_re_le_norm _).trans hnorm)
          (by positivity)
    _ = (W : ℝ) ^ d * (w.im)⁻¹ * LM ^ (1 / ((p' + 1 : ℕ) : ℝ)) := by
        rw [Real.mul_rpow (by positivity) hLM, one_div,
          Real.pow_rpow_inv_natCast (by positivity) (by omega)]

/-- **(6.10)** summed over the rows, with the Ward identities (6.12) and (Gram).  For the
mixed chain `M = X·Y`, `X` a chain of `l` resolvents at `z` (ending in `G_l`) and `Y` a chain of
`k` resolvents at `w` (starting with `G̃_l`),
\[ \sum_{i\in I_{a_0}, j\in I_{a_m}} W^{-2d}|M_{ij}|^2
    \le (\operatorname{Im} z\operatorname{Im} w)^{-1}\max|\mathcal L_z^{(2l-1)}|
      \bigl(\max|\mathcal L_w^{(p(2k-1))}|\bigr)^{1/p}. \] -/
theorem wmass_gchain_mul_gchain_le (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {ρ : List Bool} {b₁ : List (Zd d L)} (h₁ : ρ.length = b₁.length) (s : Bool)
    {τ : List Bool} {c : List (Zd d L)} (h₂ : τ.length = c.length + 1) {p : ℕ} (hp : 1 ≤ p)
    (a0 am : Zd d L) :
    wmass (bw a0) (bw am) (gchain d L W H z (ρ ++ [s]) b₁ * gchain d L W H w τ c)
      ≤ (z.im * w.im)⁻¹ * loopMax d L W H z (2 * ρ.length + 1)
        * loopMax d L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by
  set X := gchain d L W H z (ρ ++ [s]) b₁
  set Y := gchain d L W H w τ c
  set M := X * Y
  set T := (trace (gram ℂ (blockCols Y am) ^ p)).re ^ (1 / (p : ℝ))
  set v : Fin (W ^ d) → EuclideanSpace ℂ (Vtx d L W) :=
    fun α => WithLp.toLp 2 (fun k => star (X (a0, α) k))
  have hinner : ∀ α β, inner ℂ (v α) (blockCols Y am β) = M (a0, α) (am, β) := by
    intro α β
    simp [v, blockCols, PiLp.inner_apply, M, Matrix.mul_apply, mul_comm]
  have hv : ∀ α, ‖v α‖ ^ 2 = ∑ k, ‖X (a0, α) k‖ ^ 2 := by
    intro α
    rw [EuclideanSpace.norm_sq_eq]
    simp [v]
  have h61 : ∀ α, ∑ β, ‖M (a0, α) (am, β)‖ ^ 2 ≤ (∑ k, ‖X (a0, α) k‖ ^ 2) * T := by
    intro α
    have := sum_norm_inner_sq_le_trace_pow (v α) (blockCols Y am) hp
    simp_rw [hinner, hv] at this
    exact this
  have hT := trace_gram_rpow_le hH hw h₂ am hp
  have hrow := sum_norm_gchain_row_sq_le (W := W) (H := H) hH hz h₁ s a0
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  set LMz := loopMax d L W H z (2 * ρ.length + 1)
  set LMw := loopMax d L W H w (p * (2 * τ.length - 1))
  have hLMw : 0 ≤ LMw ^ (1 / (p : ℝ)) := Real.rpow_nonneg (loopMax_nonneg _) _
  have hS0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k, ‖X (a0, α) k‖ ^ 2 := by positivity
  calc wmass (bw a0) (bw am) M
      = ∑ i, bw a0 i * ∑ j, bw am j * ‖M i j‖ ^ 2 := by
        unfold wmass
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, bw a0 i * (((W : ℝ) ^ d)⁻¹ * ∑ β : Fin (W ^ d), ‖M i (am, β)‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => by rw [sum_bw_mul am (fun j => ‖M i j‖ ^ 2)]
    _ = ((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d),
          (((W : ℝ) ^ d)⁻¹ * ∑ β : Fin (W ^ d), ‖M (a0, α) (am, β)‖ ^ 2) :=
        sum_bw_mul a0 (fun i => ((W : ℝ) ^ d)⁻¹ * ∑ β : Fin (W ^ d), ‖M i (am, β)‖ ^ 2)
    _ ≤ ((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d),
          (((W : ℝ) ^ d)⁻¹ * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)) := by
        gcongr with α
        exact h61 α
    _ = ((W : ℝ) ^ d)⁻¹ * (((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k, ‖X (a0, α) k‖ ^ 2)
          * T := by
        have e : ∀ α : Fin (W ^ d), ((W : ℝ) ^ d)⁻¹ * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)
            = (∑ k, ‖X (a0, α) k‖ ^ 2) * (((W : ℝ) ^ d)⁻¹ * T) := fun α => by ring
        simp_rw [e, ← Finset.sum_mul]
        ring
    _ ≤ ((W : ℝ) ^ d)⁻¹ * (((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k, ‖X (a0, α) k‖ ^ 2)
          * ((W : ℝ) ^ d * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg (by positivity) hS0)
    _ ≤ ((W : ℝ) ^ d)⁻¹ * ((z.im)⁻¹ * LMz) * ((W : ℝ) ^ d * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) := by
        gcongr
    _ = (z.im * w.im)⁻¹ * LMz * LMw ^ (1 / (p : ℝ)) := by
        field_simp

end Six10

section Six11

variable {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}

/-- The `l`-th mixed chain of (6.8) satisfies the bound (6.10):
`W^{-2d} ∑_{i ∈ I_b, j ∈ I_{b'}} |(G_1 E ⋯ G_l G̃_l ⋯ G̃_m)_{ij}|²
  ≤ (Im z Im w)⁻¹ max|L_z^{(2l+1)}| (max|L_w^{(p(2(m-l)-1))}|)^{1/p}` (`l` counted from `0`). -/
theorem wmass_gchainMixed_le (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    {σ : List Bool} {a : List (Zd d L)} (h : σ.length = a.length + 1) {p : ℕ} (hp : 1 ≤ p)
    (b' b : Zd d L) {l : ℕ} (hl : l < σ.length) :
    wmass (bw b) (bw b') (gchainMixed d L W H z w σ a l)
      ≤ (z.im * w.im)⁻¹ * (loopMax d L W H z (2 * l + 1)
        * loopMax d L W H w (p * (2 * (σ.length - l) - 1)) ^ (1 / (p : ℝ))) := by
  have h₁ : (σ.take l).length = (a.take l).length := by simp; omega
  have h₂ : (σ.drop l).length = (a.drop l).length + 1 := by simp; omega
  have key := wmass_gchain_mul_gchain_le (W := W) hH hz hw h₁ σ[l] h₂ hp b b'
  rw [List.take_concat_get' σ l hl] at key
  have e1 : (σ.take l).length = l := by simp; omega
  have e2 : (σ.drop l).length = σ.length - l := by simp
  rw [e1, e2] at key
  rw [gchainMixed, ← mul_assoc]
  exact key

/-- **(6.9) + (6.10) + (6.12) = (6.11)**, one symmetric loop at a time.  For a chain `C` of
`m` resolvents, the symmetric loop `⟨C E_{b'} C† E_b⟩` at `z` is bounded by the one at `w`
plus the error terms of the expansion (6.8):
\[ |\mathcal L_z| \le (m+1)\Bigl(|\mathcal L_w| + \frac{|z-w|^2}{\operatorname{Im}z\,
   \operatorname{Im}w}\sum_{l<m}\max|\mathcal L_z^{(2l+1)}|\,
   \bigl(\max|\mathcal L_w^{(p(2(m-l)-1))}|\bigr)^{1/p}\Bigr). \] -/
theorem norm_gloop_symIdx_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {σ : List Bool} {a : List (Zd d L)} (h : σ.length = a.length + 1) {p : ℕ}
    (hp : 1 ≤ p) (b' b : Zd d L) :
    ‖loopL d L W H z (symIdx σ a b' b)‖
      ≤ (σ.length + 1 : ℝ) * (‖loopL d L W H w (symIdx σ a b' b)‖ + ‖z - w‖ ^ 2
        * ((z.im * w.im)⁻¹ * ∑ l ∈ Finset.range σ.length, loopMax d L W H z (2 * l + 1)
          * loopMax d L W H w (p * (2 * (σ.length - l) - 1)) ^ (1 / (p : ℝ)))) := by
  rw [gloop_symIdx hH h, gloop_symIdx hH h, norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk,
    norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk]
  have hent := norm_gchain_apply_sq_le (isUnit_sub_zSig hH hz.ne') (isUnit_sub_zSig hH hw.ne') h
  set u := bw (W := W) b
  set v := bw (W := W) b'
  have hu : ∀ i, 0 ≤ u i := bw_nonneg b
  have hv : ∀ j, 0 ≤ v j := bw_nonneg b'
  set m := σ.length
  set M := gchainMixed d L W H z w σ a
  have hswap : ∑ l ∈ Finset.range m, wmass u v (M l)
      = ∑ i, ∑ j, u i * v j * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2 := by
    unfold wmass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hmix : ∑ l ∈ Finset.range m, wmass u v (M l)
      ≤ (z.im * w.im)⁻¹ * ∑ l ∈ Finset.range m, loopMax d L W H z (2 * l + 1)
          * loopMax d L W H w (p * (2 * (m - l) - 1)) ^ (1 / (p : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl =>
      wmass_gchainMixed_le hH hz hw h hp b' b (Finset.mem_range.mp hl)
  calc wmass u v (gchain d L W H z σ a)
      ≤ ∑ i, ∑ j, u i * v j * ((m + 1 : ℝ) * (‖gchain d L W H w σ a i j‖ ^ 2
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hent i j) (mul_nonneg (hu i) (hv j))
    _ = (m + 1 : ℝ) * (wmass u v (gchain d L W H w σ a)
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, wmass u v (M l)) := by
        have e1 : ∀ i j, u i * v j * ((m + 1 : ℝ) * (‖gchain d L W H w σ a i j‖ ^ 2
            + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2))
            = (m + 1 : ℝ) * (u i * v j * ‖gchain d L W H w σ a i j‖ ^ 2)
              + ((m + 1 : ℝ) * ‖z - w‖ ^ 2) * (u i * v j * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2) :=
          fun i j => by ring
        rw [hswap, wmass]
        simp_rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ _ := by gcongr

/-- **(6.11) for the maxima**: for `m ≥ 1`, `p ≥ 1`,
\[ \max|\mathcal L_z^{(2m)}| \le (m+1)\Bigl(\max|\mathcal L_w^{(2m)}| + \frac{|z-w|^2}
   {\operatorname{Im}z\,\operatorname{Im}w}\sum_{l<m}\max|\mathcal L_z^{(2l+1)}|\,
   \bigl(\max|\mathcal L_w^{(p(2(m-l)-1))}|\bigr)^{1/p}\Bigr). \]
Every loop of length `2m` is controlled by symmetric ones ((5.115)). -/
theorem loopMax_two_mul_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : 1 ≤ p) :
    loopMax d L W H z (2 * m)
      ≤ (m + 1 : ℝ) * (loopMax d L W H w (2 * m) + ‖z - w‖ ^ 2
        * ((z.im * w.im)⁻¹ * ∑ l ∈ Finset.range m, loopMax d L W H z (2 * l + 1)
          * loopMax d L W H w (p * (2 * (m - l) - 1)) ^ (1 / (p : ℝ)))) := by
  refine loopMax_le fun I hσ ha => norm_gloop_le_of_symIdx_le hH hm ?_ I hσ ha
  intro σ a hσ' ha' b' b
  have h : σ.length = a.length + 1 := by omega
  refine (norm_gloop_symIdx_le_tilde hH hz hw h hp b' b).trans ?_
  rw [hσ']
  gcongr
  have := norm_gloop_symIdx_le_loopMax (W := W) (H := H) (z := w) h b' b
  rwa [hσ'] at this

end Six11


section Checks

/-! ### Compiled instances at `d = 3`, `L = 3`, `W = 2`

`N = (W L)^d = 216` sites, `W^d = 8` sites per block, `L^d = 27` block labels.  The matrix of
the instances of the five targets is `cad_Hd = diag(β)`, `β` the within-block coordinate of the
site (values `0, …, 7`, real, so Hermitian, and not a multiple of the identity).  The spectral
data are those of `E = 0`, `t₁ = 1/4`, `t₂ = 1/2`: `m^{(0)} = i`, `z = z_{t₂} = i/2`,
`w = z̃_{t₁} = (3√2/4) i`, both with positive imaginary part (`cad_im_z`, `cad_im_w`).
The `H = 0`, `z = i` values at the end show the factor `W^{-d} = 1/8` of the Ward identity
(`W^{-2} = 1/4` would give a different value). -/

private noncomputable def cad_Hd : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ :=
  Matrix.diagonal fun x => ((x.2 : ℕ) : ℂ)

private theorem cad_Hd_herm : cad_Hd.IsHermitian := by
  refine Matrix.isHermitian_diagonal_iff.mpr fun x => ?_
  simp [IsSelfAdjoint]

private theorem cad_mE_zero : mE 0 = Complex.I := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  simp [mE, hsqrt]

private theorem cad_im_z : (zt 0 (1 / 2)).im = 1 / 2 := by
  rw [Gauss.spectralZ_im, cad_mE_zero]
  simp
  norm_num

/-- `Im z̃ = 3√2/4` at `E = 0`, `t₁ = 1/4`, `t₂ = 1/2`. -/
private theorem cad_im_w' : (ztTilde 0 (1 / 4) (1 / 2)).im = 3 * Real.sqrt 2 / 4 := by
  rw [ztTilde_im, Gauss.etaT, Gauss.spectralM_im]
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [h4, show (1 / 2 : ℝ) / (1 / 4) = 2 by norm_num]
  ring

private theorem cad_im_w : 0 < (ztTilde 0 (1 / 4) (1 / 2)).im := by
  rw [cad_im_w']
  positivity

private theorem cad_z_pos : 0 < (zt 0 (1 / 2)).im := by
  rw [cad_im_z]; norm_num

private theorem cad_conj_im_ne {z : ℂ} (hz : 0 < z.im) : ((starRingEnd ℂ) z).im ≠ 0 := by
  simpa using hz.ne'

/-- **Target `green_sub_green`** (`RBM.green_sub_green`) at `H = cad_Hd` on `Vtx 3 3 2`,
`z = z_{t₂}`, `w = z̃_{t₁}`. -/
example :
    green cad_Hd (zt 0 (1 / 2)) - green cad_Hd (ztTilde 0 (1 / 4) (1 / 2))
      = (zt 0 (1 / 2) - ztTilde 0 (1 / 4) (1 / 2)) •
          (green cad_Hd (zt 0 (1 / 2)) * green cad_Hd (ztTilde 0 (1 / 4) (1 / 2))) :=
  green_sub_green (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_im_w.ne')

/-- **Target `sum_gloop_ward_last_div`** at `H = cad_Hd`, `z = z_{t₂}`, `μ = (−, +)`,
`x = 0`, `a' = (0, 1)`: a loop of length `4` with the last label summed over `Zd 3 3`
(27 labels). -/
example :
    (∑ b : Zd 3 3, loopL 3 3 2 cad_Hd (zt 0 (1 / 2))
        ⟨true :: [false, true] ++ [false], (0 : Zd 3 3) :: [0, 1] ++ [b]⟩)
      = (loopL 3 3 2 cad_Hd (zt 0 (1 / 2)) ⟨true :: [false, true], (0 : Zd 3 3) :: [0, 1]⟩
          - loopL 3 3 2 cad_Hd (zt 0 (1 / 2)) ⟨false :: [false, true], (0 : Zd 3 3) :: [0, 1]⟩)
        / (2 * Complex.I * (2 : ℂ) ^ 3 * ((zt 0 (1 / 2)).im : ℂ)) :=
  sum_gloop_ward_last_div 3 3 2
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm (cad_conj_im_ne cad_z_pos)) cad_z_pos.ne'
    [false, true] 0 [0, 1] rfl

/-- `sum_gloop_ward_last` (the undivided form), same data. -/
example :
    (2 * Complex.I * ((zt 0 (1 / 2)).im : ℂ)) *
      ∑ b : Zd 3 3, loopL 3 3 2 cad_Hd (zt 0 (1 / 2))
        ⟨true :: [false, true] ++ [false], (0 : Zd 3 3) :: [0, 1] ++ [b]⟩
      = (((2 : ℂ) ^ 3)⁻¹) *
        (loopL 3 3 2 cad_Hd (zt 0 (1 / 2)) ⟨true :: [false, true], (0 : Zd 3 3) :: [0, 1]⟩
          - loopL 3 3 2 cad_Hd (zt 0 (1 / 2))
              ⟨false :: [false, true], (0 : Zd 3 3) :: [0, 1]⟩) :=
  sum_gloop_ward_last 3 3 2
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm (cad_conj_im_ne cad_z_pos))
    [false, true] 0 [0, 1] rfl

/-- `sum_gloop_two_ward`, same data. -/
example (a : Zd 3 3) :
    (2 * Complex.I * ((zt 0 (1 / 2)).im : ℂ)) *
      ∑ b : Zd 3 3, loopL 3 3 2 cad_Hd (zt 0 (1 / 2)) ⟨[true, false], [a, b]⟩
      = (((2 : ℂ) ^ 3)⁻¹) *
        (Matrix.trace (green cad_Hd (zt 0 (1 / 2)) * Eblk 3 3 2 a)
          - Matrix.trace (green cad_Hd ((starRingEnd ℂ) (zt 0 (1 / 2))) * Eblk 3 3 2 a)) :=
  sum_gloop_two_ward 3 3 2
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm (cad_conj_im_ne cad_z_pos)) a

/-- **Target `ztTilde_arith`** at `c = t₁ = 1/4`, `κ = 1`, `E = 1/2`, `t₂ = 1/2`: all hypotheses
(`c ≤ t₁ ≤ t₂ ≤ 1`, `|E| ≤ 2 - κ`) hold, and the five conclusions are available. -/
example :
    ∃ C > 0, ‖zt (1 / 2) (1 / 2) - ztTilde (1 / 2) (1 / 4) (1 / 2)‖ ≤ C * (1 - 1 / 4)
      ∧ ‖zt (1 / 2) (1 / 2) - ztTilde (1 / 2) (1 / 4) (1 / 2)‖ ^ 2
          ≤ C * Gauss.etaT (1 / 2) (1 / 4) ^ 2
      ∧ ‖zt (1 / 2) (1 / 2) - ztTilde (1 / 2) (1 / 4) (1 / 2)‖ ^ 2
          / (ztTilde (1 / 2) (1 / 4) (1 / 2)).im ≤ C * Gauss.etaT (1 / 2) (1 / 4)
      ∧ Gauss.etaT (1 / 2) (1 / 4) ≤ (ztTilde (1 / 2) (1 / 4) (1 / 2)).im
      ∧ (ztTilde (1 / 2) (1 / 4) (1 / 2)).im ≤ C * Gauss.etaT (1 / 2) (1 / 4) := by
  obtain ⟨C, hC, h⟩ := ztTilde_arith (c := 1 / 4) (κ := 1) (by norm_num) (by norm_num)
  exact ⟨C, hC, h (1 / 2) (1 / 4) (1 / 2) le_rfl (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by norm_num)]; norm_num)⟩

/-- **Target `loopMax_two_mul_le_tilde`** at `H = cad_Hd` on `Vtx 3 3 2`, `z = z_{t₂}`,
`w = z̃_{t₁}`, `m = 1`, `p = 1`. -/
example :
    loopMax 3 3 2 cad_Hd (zt 0 (1 / 2)) (2 * 1)
      ≤ ((1 : ℕ) + 1 : ℝ) * (loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (2 * 1)
        + ‖zt 0 (1 / 2) - ztTilde 0 (1 / 4) (1 / 2)‖ ^ 2
          * (((zt 0 (1 / 2)).im * (ztTilde 0 (1 / 4) (1 / 2)).im)⁻¹
            * ∑ l ∈ Finset.range 1, loopMax 3 3 2 cad_Hd (zt 0 (1 / 2)) (2 * l + 1)
              * loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (1 * (2 * (1 - l) - 1))
                ^ (1 / ((1 : ℕ) : ℝ)))) :=
  loopMax_two_mul_le_tilde cad_Hd_herm cad_z_pos cad_im_w le_rfl le_rfl

/-- `loopMax_two_mul_le_tilde` at `m = 2`, `p = 2`. -/
example :
    loopMax 3 3 2 cad_Hd (zt 0 (1 / 2)) (2 * 2)
      ≤ ((2 : ℕ) + 1 : ℝ) * (loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (2 * 2)
        + ‖zt 0 (1 / 2) - ztTilde 0 (1 / 4) (1 / 2)‖ ^ 2
          * (((zt 0 (1 / 2)).im * (ztTilde 0 (1 / 4) (1 / 2)).im)⁻¹
            * ∑ l ∈ Finset.range 2, loopMax 3 3 2 cad_Hd (zt 0 (1 / 2)) (2 * l + 1)
              * loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (2 * (2 * (2 - l) - 1))
                ^ (1 / ((2 : ℕ) : ℝ)))) :=
  loopMax_two_mul_le_tilde cad_Hd_herm cad_z_pos cad_im_w (by norm_num) (by norm_num)

/-- **Target `trace_gram_rpow_le`** at `H = cad_Hd`, `w = z̃_{t₁}`, the chain `τ = (+)`,
`c = ()` (`k = 1`), block `b = 0`, `p = 1`. -/
example :
    (trace (gram ℂ (blockCols (gchain 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) [true] [])
        (0 : Zd 3 3)) ^ 1)).re ^ (1 / ((1 : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ 3 * ((ztTilde 0 (1 / 4) (1 / 2)).im)⁻¹
        * loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (1 * (2 * [true].length - 1))
          ^ (1 / ((1 : ℕ) : ℝ)) :=
  trace_gram_rpow_le cad_Hd_herm cad_im_w rfl 0 le_rfl

/-- `trace_gram_rpow_le` at a chain of two resolvents, `τ = (+, −)`, `c = (1)`, `b = 2`,
`p = 2`. -/
example :
    (trace (gram ℂ (blockCols (gchain 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) [true, false]
        [(1 : Zd 3 3)]) (2 : Zd 3 3)) ^ 2)).re ^ (1 / ((2 : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ 3 * ((ztTilde 0 (1 / 4) (1 / 2)).im)⁻¹
        * loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (2 * (2 * [true, false].length - 1))
          ^ (1 / ((2 : ℕ) : ℝ)) :=
  trace_gram_rpow_le cad_Hd_herm cad_im_w rfl 2 (by norm_num)

/-- `wmass_gchain_mul_gchain_le` (6.10), `ρ = b₁ = ()`, `s = +`, `τ = (+)`, `c = ()`, `p = 1`. -/
example :
    wmass (bw (0 : Zd 3 3)) (bw (1 : Zd 3 3))
        (gchain 3 3 2 cad_Hd (zt 0 (1 / 2)) ([] ++ [true]) [] *
          gchain 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) [true] [])
      ≤ ((zt 0 (1 / 2)).im * (ztTilde 0 (1 / 4) (1 / 2)).im)⁻¹
        * loopMax 3 3 2 cad_Hd (zt 0 (1 / 2)) (2 * ([] : List Bool).length + 1)
        * loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (1 * (2 * [true].length - 1))
          ^ (1 / ((1 : ℕ) : ℝ)) :=
  wmass_gchain_mul_gchain_le cad_Hd_herm cad_z_pos cad_im_w rfl true rfl le_rfl 0 1

/-- **(6.12)** `ward_chain_row` at `H = cad_Hd`, `z = z_{t₂}`, `ρ = (+)`, `b = (0)`, `s = −`. -/
example :
    (2 * Complex.I * ((zt 0 (1 / 2)).im : ℂ)) * (((2 : ℂ) ^ 3)⁻¹ *
        ∑ α : Fin (2 ^ 3), ∑ k : Vtx 3 3 2,
          (Complex.normSq (gchain 3 3 2 cad_Hd (zt 0 (1 / 2)) ([true] ++ [false]) [(0 : Zd 3 3)]
            ((1 : Zd 3 3), α) k) : ℂ))
      = loopL 3 3 2 cad_Hd (zt 0 (1 / 2))
          ⟨[true] ++ true :: ([true].map (!·)).reverse,
            [(0 : Zd 3 3)] ++ ([(0 : Zd 3 3)].reverse ++ [(1 : Zd 3 3)])⟩
        - loopL 3 3 2 cad_Hd (zt 0 (1 / 2))
          ⟨[true] ++ false :: ([true].map (!·)).reverse,
            [(0 : Zd 3 3)] ++ ([(0 : Zd 3 3)].reverse ++ [(1 : Zd 3 3)])⟩ :=
  ward_chain_row cad_Hd_herm
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm (cad_conj_im_ne cad_z_pos)) rfl false 1

/-! #### Values at `H = 0`, `z = i` (the factor `W^{-d} = 1/8`) -/

/-- For `H = 0` the Green function is `(-z)⁻¹ · 1`. -/
private theorem cad_green_zero {n : Type*} [Fintype n] [DecidableEq n] {z : ℂ} (hz : z ≠ 0) :
    green (0 : Matrix n n ℂ) z = (-z)⁻¹ • (1 : Matrix n n ℂ) := by
  unfold green
  rw [Matrix.inv_eq_right_inv]
  simp [smul_smul, hz]

private theorem cad_green_zero_I :
    green (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
      = Complex.I • (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) := by
  rw [cad_green_zero Complex.I_ne_zero]
  simp

private theorem cad_green_zero_conj_I :
    green (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) ((starRingEnd ℂ) Complex.I)
      = (-Complex.I) • (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) := by
  rw [cad_green_zero (by simp)]
  simp

/-- At `H = 0`, `z = i`: `𝓛_{(+),(x)} = i` and `𝓛_{(-),(x)} = -i` (`tr E_x = 1`). -/
private theorem cad_loop_one_true (x : Zd 3 3) :
    loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I ⟨[true], [x]⟩ = Complex.I := by
  rw [cad_loopL_eq, cad_gloopProd_cons, cad_gloopProd_nil, Matrix.mul_one, cad_Gres_true,
    cad_green_zero_I, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, trace_Eblk, smul_eq_mul,
    mul_one]

private theorem cad_loop_one_false (x : Zd 3 3) :
    loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I ⟨[false], [x]⟩
      = -Complex.I := by
  rw [cad_loopL_eq, cad_gloopProd_cons, cad_gloopProd_nil, Matrix.mul_one, cad_Gres_false,
    cad_green_zero_conj_I, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, trace_Eblk,
    smul_eq_mul, mul_one]

/-- **`sum_gloop_ward_last_div` at `H = 0`, `z = i`, `μ = a' = ()`**: the sum over the last block
label of the two-loops `𝓛_{(+,-),(x,b)}` equals `(i - (-i)) / (2i · 8 · 1) = 1/8 ≠ 0`: the factor
is `W^{-d} = 1/8`, not the `d = 2` factor `W^{-2} = 1/4`. -/
private theorem cad_ward_div_value (x : Zd 3 3) :
    (∑ b : Zd 3 3, loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
        ⟨true :: ([] : List Bool) ++ [false], x :: ([] : List (Zd 3 3)) ++ [b]⟩) = 1 / 8 := by
  have h := sum_gloop_ward_last_div 3 3 2
    (H := (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)) (z := Complex.I)
    (isUnit_sub_smul_one_of_im_ne_zero Matrix.isHermitian_zero (by simp))
    (isUnit_sub_smul_one_of_im_ne_zero Matrix.isHermitian_zero (by simp)) (by simp)
    [] x [] rfl
  rw [h]
  have e1 : (⟨true :: ([] : List Bool), x :: ([] : List (Zd 3 3))⟩ : Loop.LoopIdx (Zd 3 3))
      = ⟨[true], [x]⟩ := rfl
  have e2 : (⟨false :: ([] : List Bool), x :: ([] : List (Zd 3 3))⟩ : Loop.LoopIdx (Zd 3 3))
      = ⟨[false], [x]⟩ := rfl
  rw [e1, e2, cad_loop_one_true, cad_loop_one_false]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp only [Complex.I_im, Complex.ofReal_one]
  field_simp
  norm_num

/-- **(6.12)** at `H = 0`, `z = i`: the row sum is `∑_{α ∈ Fin 8} ∑_k |G_{(a₀,α),k}|² = 8`, so
`W^{-d} ∑ = 1`, whereas the `d = 2` normalisation `W^{-2}` would give `2`. -/
private theorem cad_check_ward_row (a0 : Zd 3 3) :
    ∑ α : Fin (2 ^ 3), ∑ k : Vtx 3 3 2,
        (Complex.normSq (gchain 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
          ([] ++ [true]) [] (a0, α) k) : ℂ) = 8 := by
  have hG : gchain 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I ([] ++ [true]) []
      = Complex.I • (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) := by
    rw [List.nil_append, gchain_single, cad_Gres_true, cad_green_zero_I]
  have hk : ∀ p : Vtx 3 3 2,
      ∑ k : Vtx 3 3 2,
        (Complex.normSq ((Complex.I • (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)) p k) : ℂ)
        = 1 := by
    intro p
    simp [Matrix.one_apply, apply_ite Complex.normSq, apply_ite (Complex.ofReal)]
  rw [hG]
  simp only [hk]
  simp

end Checks

end RBM.Ind
