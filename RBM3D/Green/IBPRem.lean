/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.IBP
import RBM3D.Green.CondDom
import RBM3D.Green.LocalLaw

/-!
# The per-time integration-by-parts remainder: `‖ibpRem‖ ≺ Ψ²` off the diagonal, `≺ 1` on it

Paper: arXiv:2507.20274, (3.5) `GavLGEX`, whose proof is "that of Lemma 4.1 in [YY_25]"; the
standing hypothesis `W ≥ N^𝔠` is (2.9) `Main_DEL_COND`.  The mathematics is the proof of
(3.5) `GavLGEX` in [YY_25, Lemma 4.1]: the remainder of the integration-by-parts display,
`E_i[G_ii (G_kk - m)] - m (G_kk - m) = E_i[(G_ii - m)(G_kk - m)] + m (E_i(G_kk - m) - (G_kk - m))`
(`ibpRem_eq_add`), is `O≺(Ψ²)` for `k ≠ i`: the first summand is a product of two entries of
`G - m` (each `≺ Ψ`, the local law `LocalLawDetSeq`), the second is the minor-replacement error
(`(G_kk - m) - (G^{(i)}_kk - m) = O(|G_ki| |G_ik|)` on the good event, and `G^{(i)}_kk` is
`E_i`-invariant).  On the diagonal `k = i` only `≺ 1` is claimed.  This file is the input
`ibpRem` of the statement `IBPDetThm d`.

## Contents (namespace `Green`)

* `IBPRemOffPair d L W` -- ordered pairs of distinct fine indices.
* `IBPRem_hΨlow_of_floor` -- `W^{-d/2} ≤ Ψ` gives `size^{-1} ≤ Ψ²`, the `hΨlow` below.
* `perTimeDomAt_green_diag_sub`, `perTimeDomAt_green_offdiag`, `perTimeDomAt_prod_green_diag_sub`
  -- `|G_ii - m| ≺ Ψ`, `|G_ij| ≺ Ψ` (`i ≠ j`), `|(G_ii - m)(G_jj - m)| ≺ Ψ²`, from `hll`.
* `perTimeDomAt_condRow_prod_green_diag` -- `E_i[(G_ii - m)(G_jj - m)] ≺ Ψ²`.
* `perTimeDomAt_greenDiagCentered_sub_minor` -- the minor replacement `≺ Ψ²` on the good event.
* `perTimeDomAt_condRow_greenDiagCentered_sub_self` -- `E_i(G_jj - m) - (G_jj - m) ≺ Ψ²`, `i ≠ j`.
* `perTimeDomAt_ibpRem_offdiag` -- `ibpRem (i, j) ≺ Ψ²`, `i ≠ j`.
* `perTimeDomAt_greenDiagCentered_one`, `perTimeDomAt_condExpDiag_one` -- `≺ 1`.
* `perTimeDomAt_ibpRem_diag` -- `ibpRem (i, i) ≺ 1`.
* `perTimeDomAt_ibpRem` -- the endpoint: `ibpRem (i, j) ≺ 1` on the diagonal, `≺ Ψ²` off it.

## Conventions

* **`d`-dimensional exponents.**  No exponent of a statement contains `d`: every power of `N` is
  the same power of `sz.size n = (W L)^d`, `Kenv`, `B` and `τ` are free reals, the constants
  are `2` (the minor replacement `1/|G_ii| ≤ 2` on `δ ≤ 1/2`; `ζ + ζ ≤ 2 ζ`).
* **The floor.**  No statement takes the floor `W^{-d/2} ≤ Ψ` as a hypothesis.  The floor enters
  only as `hΨlow : size^{-B} ≤ Ψ²` with `B ≥ 0` free; from `W^{-d/2} ≤ Ψ` it holds with `B = 1`,
  since `size = (W L)^d ≥ W^d` (`L ≥ 1`; `IBPRem_hΨlow_of_floor`, for every `d` and `n`), so every
  statement holds at that floor (the consumer `IBPDetThm d` obtains `hΨlow`, `hΨ1`, `hΨ0` from its
  own premises).
* **`hd : 1 ≤ d`** (from `perTimeDomAt_of_le_left_on` of Green/CondDom.lean) on
  `perTimeDomAt_greenDiagCentered_sub_minor`, `perTimeDomAt_condRow_greenDiagCentered_sub_self`,
  `perTimeDomAt_ibpRem_offdiag`, `perTimeDomAt_ibpRem`: the first calls it, the other three use
  the first.  The other seven statements carry no `hd`; `hd : 3 ≤ d` is not used (`hll` is a
  hypothesis).
* `IBPRemOffPair d L W` is a subtype of pairs over the fine index `Idx d L W` (`OffPair` of
  Green/EntryDom.lean is over the block-product index `Vtx d L W`).
* The private helpers: `IBPRem_precomp` (reindexing), `IBPRem_add` (`ζ + ζ ≤ 2 ζ`),
  `IBPRem_goodEvent` (the unfolding `{∀ i j, llErrMat ≤ δ} ⊆ GoodEvent`), and `IBPRem_Gres_true`
  (`Gres H z true = green H z`: `llErrMat` is stated through `Gres`, the entries of this file
  through `green`).
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss RBM.Path RBM.Ind.PerTimeCalc.PerTime
open scoped ENNReal

/-! ### Off-diagonal pairs, and three combinators -/

/-- Ordered pairs of distinct fine indices, at the fine lattice `Idx d L W`.  (`OffPair` of
Green/EntryDom.lean is over the block-product index `Vtx d L W`.) -/
abbrev IBPRemOffPair (d L W : ℕ) : Type := {p : Idx d L W × Idx d L W // p.1 ≠ p.2}

/-- Reindexing preserves a per-time domination. -/
private theorem IBPRem_precomp {d : ℕ} {sz : Sizes d} {U V : ℕ → Type*} {ξ ζ : ∀ n, U n → Sizes.SeqΩ sz → ℝ}
    (g : ∀ n, V n → U n) (h : PerTimeDomAt (Sizes.seqP sz) sz.size ξ ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (fun n a ω => ξ n (g n a) ω)
      (fun n a ω => ζ n (g n a) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn a
  exact hn (g n a)

/-- `≺` is closed under addition when both bounds agree: `perTimeCalc_add`, then
`perTimeCalc_mono` with `ζ + ζ ≤ 2 ζ`. -/
private theorem IBPRem_add {d : ℕ} {sz : Sizes d} (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ₁ ξ₂ ζ : ∀ n, U n → Sizes.SeqΩ sz → ℝ} (hζ0 : ∀ n a ω, 0 ≤ ζ n a ω)
    (h₁ : PerTimeDomAt (Sizes.seqP sz) sz.size ξ₁ ζ)
    (h₂ : PerTimeDomAt (Sizes.seqP sz) sz.size ξ₂ ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (fun n a ω => ξ₁ n a ω + ξ₂ n a ω) ζ :=
  perTimeCalc_mono hsize hζ0 2 (Eventually.of_forall fun n a ω => by linarith)
    (perTimeCalc_add hsize h₁ h₂)

/-- `Gres H z true` (a `Ring.inverse`) is `green H z = (H - z)⁻¹`. -/
private theorem IBPRem_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- The good event `{∀ i j, llErrMat ≤ δ}` at one `ω` is the `GoodEvent`
(`GoodEvent G m δ := ∀ x y, ‖G x y - (if x = y then m else 0)‖ ≤ δ`, `llErrMat` at
`M = H_u`, `green H z = (H - z)⁻¹`): the unfolding of `llErrMat` and `IBPRem_Gres_true`. -/
private theorem IBPRem_goodEvent {d : ℕ} {sz : Sizes d} {n : ℕ} {E u δ : ℝ} {ω : Sizes.SeqΩ sz}
    (h : ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) E u (Sizes.seqHflow sz n u ω) i j ≤ δ) :
    GoodEvent (green (Sizes.seqHflow sz n u ω) (zt E u)) (mE E) δ := fun x y => by
  have h1 := h x y
  unfold llErrMat at h1
  rwa [IBPRem_Gres_true] at h1

/-- **The floor of the statements gives the polynomial floor.**  From
`W^{-d/2} ≤ Ψ` (the floor of `IBPDetThm d`) one gets
`size^{-1} ≤ Ψ²`, the `hΨlow` of this file with `B = 1`: `Ψ² ≥ W^{-d}` and
`size = (W L)^d ≥ W^d`.  It holds for every `d` and every `n`. -/
theorem IBPRem_hΨlow_of_floor {d : ℕ} (sz : Sizes d) (n : ℕ) {Ψ : ℝ}
    (hfloor : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) :
    ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ Ψ * Ψ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hW.le _
  have hsq : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
      = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [← Real.rpow_add hW, show (-(d : ℝ) / 2 + -(d : ℝ) / 2) = -(d : ℝ) by ring,
      Real.rpow_neg hW.le, Real.rpow_natCast]
  have hle : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.W n) ^ d ≤ sz.size n :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hL) d
    exact_mod_cast h
  calc ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) = ((sz.size n : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_anti₀ (by positivity) hle
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := hsq.symm
    _ ≤ Ψ * Ψ := mul_le_mul hfloor hfloor h0 (h0.trans hfloor)

/-! ### From the local law: `|G_ii - m|`, `|G_ij|`, `|(G_ii - m)(G_jj - m)|` -/

section LocalLaw

variable {d : ℕ} {sz : Sizes d} {E t Ψ : ℕ → ℝ}

/-- **`|G_ii - m| ≺ Ψ`**, per time, from the local law: `llErrMat i i = ‖G_ii - m‖`. -/
theorem perTimeDomAt_green_diag_sub (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n))
      (fun n i ω =>
        ‖green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) i i - mE (E n)‖)
      (fun n _ _ => Ψ n) :=
  stochDom_of_le_left_eventually
    (ξ' := fun n (i : Idx d (sz.L n) (sz.W n)) ω =>
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i i)
    (Eventually.of_forall fun n i ω => by simp [llErrMat, IBPRem_Gres_true])
    (IBPRem_precomp (fun n (i : Idx d (sz.L n) (sz.W n)) => ((), i, i)) hll)

/-- **`|G_ij| ≺ Ψ` for `i ≠ j`**, per time, from the local law: `llErrMat i j = ‖G_ij‖` for
`i ≠ j`. -/
theorem perTimeDomAt_green_offdiag (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n))
      (fun n v ω =>
        ‖green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) v.1.1 v.1.2‖)
      (fun n _ _ => Ψ n) :=
  stochDom_of_le_left_eventually
    (ξ' := fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) ω =>
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) v.1.1 v.1.2)
    (Eventually.of_forall fun n v ω => by simp [llErrMat, IBPRem_Gres_true, v.2])
    (IBPRem_precomp (fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) => ((), v.1.1, v.1.2)) hll)

/-- **`|(G_ii - m)(G_jj - m)| ≺ Ψ²`**, per time, from the local law.  `hsize` is needed by
`perTimeCalc_mul`. -/
theorem perTimeDomAt_prod_green_diag_sub (hsize : Tendsto sz.size atTop atTop)
    (hΨ0 : ∀ n, 0 ≤ Ψ n) (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω =>
        ‖(green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) q.1 q.1 - mE (E n))
          * (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) q.2 q.2
            - mE (E n))‖)
      (fun n _ _ => Ψ n * Ψ n) := by
  have h1 := IBPRem_precomp
    (fun n (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => q.1)
    (perTimeDomAt_green_diag_sub hll)
  have h2 := IBPRem_precomp
    (fun n (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => q.2)
    (perTimeDomAt_green_diag_sub hll)
  exact stochDom_of_le_left_eventually (Eventually.of_forall fun n q ω => le_of_eq (norm_mul _ _))
    (perTimeCalc_mul hsize (fun n q ω => norm_nonneg _) (fun n q ω => hΨ0 n) h1 h2)

end LocalLaw

/-! ### The row-conditional expectation of the product, and the minor replacement -/

section Rem

variable {d : ℕ} {sz : Sizes d} {E t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`E_i[(G_ii - m)(G_jj - m)] ≺ Ψ²`**, per time, under the envelope `hEnv` and the floor
`hΨlow`: `perTimeDomAt_condRow_of_envelope` at `X = (G_ii - m)(G_jj - m)`, `k = i`,
`Env = (η_t⁻¹ + 1)²` (`‖G_ii - m‖ ≤ η_t⁻¹ + 1`), `ζ = χ = Ψ²`. -/
theorem perTimeDomAt_condRow_prod_green_diag (hsize : Tendsto sz.size atTop atTop)
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv)
    (hB : 0 ≤ B)
    (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n)
    (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω =>
        ‖condRow sz n q.1
          (fun η => (green (Sizes.seqHflow sz n (t n) η) (zt (E n) (t n)) q.1 q.1
              - mE (E n))
            * (green (Sizes.seqHflow sz n (t n) η) (zt (E n) (t n)) q.2 q.2
              - mE (E n))) ω‖)
      (fun n _ _ => Ψ n * Ψ n) := by
  have hΨΨ0 : ∀ (n : ℕ) (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      0 ≤ Ψ n * Ψ n := fun n _ _ => mul_nonneg (hΨ0 n) (hΨ0 n)
  refine perTimeDomAt_condRow_of_envelope hsize
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (X := fun n (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ω =>
      (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) q.1 q.1 - mE (E n))
        * (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) q.2 q.2
          - mE (E n)))
    (ζ := fun n _ _ => Ψ n * Ψ n) (χ := fun n _ _ => Ψ n * Ψ n)
    (k := fun n (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => q.1)
    (Env := fun n => ((etaT (E n) (t n))⁻¹ + 1) ^ 2)
    (fun n q => ((measurable_green_apply sz n (t n) (zt (E n) (t n)) q.1 q.1).sub
      measurable_const).mul ((measurable_green_apply sz n (t n) (zt (E n) (t n)) q.2 q.2).sub
        measurable_const))
    (fun n q => measurable_const) hΨΨ0 hΨΨ0 hKenv hB ?_ hEnv
    (fun n q ω => integrable_const _)
    (perTimeDomAt_const sz (fun n => mul_nonneg (hΨ0 n) (hΨ0 n)) hΨlow) ?_
    (perTimeDomAt_prod_green_diag_sub hsize hΨ0 hll)
  · intro n q ω
    rw [norm_mul, sq]
    have h1 := norm_green_diag_sub_mE_le (sz := sz) (n := n) (hE n) (ht1 n) (t n) q.1 ω
    have h2 := norm_green_diag_sub_mE_le (sz := sz) (n := n) (hE n) (ht1 n) (t n) q.2 ω
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  · simp only [condRowReal_const]
    exact perTimeCalc_refl hsize hΨΨ0

/-- **`|greenDiagCentered j - greenMinorDiagCentered^{(i)} j| ≺ Ψ²` for `i ≠ j`**, per time, with
the good event `hΩ`: on `hΩ` the pointwise minor formula [YY_25, (4.9)],
`norm_greenDiagCentered_sub_minor_le`, bounds it by `2 |G_ji| |G_ij|`, which is `≺ Ψ²` (two
off-diagonal entries, `perTimeCalc_mul`; the factor `2` is `IBPRem_add` applied to the product
twice, `2 ξ = ξ + ξ`).  The pair `v = (i, j)` carries `v.2 : i ≠ j`, and the minor entry is
`⟨j, v.2.symm⟩`. -/
theorem perTimeDomAt_greenDiagCentered_sub_minor (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop)
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2)
    (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}))
    (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n))
      (fun n v ω =>
        ‖greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2 ω
          - greenMinorDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.1
            ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun n _ _ => Ψ n * Ψ n) := by
  have hswap := IBPRem_precomp
    (fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) =>
      (⟨(v.1.2, v.1.1), Ne.symm v.2⟩ : IBPRemOffPair d (sz.L n) (sz.W n)))
    (perTimeDomAt_green_offdiag hll)
  have hprod := perTimeCalc_mul hsize (fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) ω => norm_nonneg _)
    (fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) ω => hΨ0 n) hswap (perTimeDomAt_green_offdiag hll)
  have h2 := IBPRem_add hsize
    (ζ := fun n (_ : IBPRemOffPair d (sz.L n) (sz.W n)) (_ : Sizes.SeqΩ sz) => Ψ n * Ψ n)
    (fun n _ _ => mul_nonneg (hΨ0 n) (hΨ0 n)) hprod hprod
  refine perTimeDomAt_of_le_left_on hd hΩ ?_ h2
  filter_upwards [hδ1] with n hδN ω hω v
  have hb := norm_greenDiagCentered_sub_minor_le sz n (hE n) (ht1 n) hδN (IBPRem_goodEvent hω)
    v.1.1 v.1.2 v.2
  linarith

/-- **`|E_i(G_jj - m) - (G_jj - m)| ≺ Ψ²` for `i ≠ j`**, per time: `perTimeDomAt_condRow_sub_self`
at `X = G_jj - m`, the row-`i`-free surrogate
`X' = G^{(i)}_jj - m` (`finDepOffRow_greenMinorMat_apply`), `Env = (η_t⁻¹ + 1)²`
(`‖X - X'‖ ≤ 2 η_t⁻¹`), and `‖X - X'‖ ≺ Ψ²` from
`perTimeDomAt_greenDiagCentered_sub_minor`. -/
theorem perTimeDomAt_condRow_greenDiagCentered_sub_self (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop)
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv)
    (hB : 0 ≤ B)
    (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n)
    (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2)
    (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}))
    (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n))
      (fun n v ω =>
        ‖condRow sz n v.1.1
            (greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2) ω
          - greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2 ω‖)
      (fun n _ _ => Ψ n * Ψ n) := by
  have hΨΨ0 : ∀ (n : ℕ) (v : IBPRemOffPair d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      0 ≤ Ψ n * Ψ n := fun n _ _ => mul_nonneg (hΨ0 n) (hΨ0 n)
  refine perTimeDomAt_condRow_sub_self hsize
    (V := fun n => IBPRemOffPair d (sz.L n) (sz.W n))
    (X := fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) =>
      greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2)
    (X' := fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) =>
      greenMinorDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.1
        ⟨v.1.2, Ne.symm v.2⟩)
    (ζ := fun n _ _ => Ψ n * Ψ n) (χ := fun n _ _ => Ψ n * Ψ n)
    (k := fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) => v.1.1)
    (Env := fun n => ((etaT (E n) (t n))⁻¹ + 1) ^ 2)
    (fun n v => measurable_greenDiagCentered sz n (t n) (zt (E n) (t n))
      (mE (E n)) v.1.2)
    (fun n v => measurable_greenMinorDiagCentered sz n (t n) (zt (E n) (t n))
      (mE (E n)) v.1.1 _)
    (fun n v => measurable_const) hΨΨ0 hΨΨ0 hKenv hB ?_ hEnv
    (fun n v ω => integrable_const _)
    (perTimeDomAt_const sz (fun n => mul_nonneg (hΨ0 n) (hΨ0 n)) hΨlow) ?_
    (perTimeCalc_refl hsize hΨΨ0)
    (fun n v => (finDepOffRow_greenMinorMat_apply sz n (t n) (zt (E n) (t n)) v.1.1
      ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩).comp fun z => z - mE (E n))
    ?_ (perTimeDomAt_greenDiagCentered_sub_minor hd hsize hE ht1 hΨ0 hδ1 hΩ hll)
  · intro n v ω
    have hη : 0 < etaT (E n) (t n) := etaT_pos (hE n) (ht1 n)
    have hzim : (zt (E n) (t n)).im = etaT (E n) (t n) := zt_im (E n) (t n)
    have h1 := norm_green_apply_le_etaT (sz := sz) (n := n) (hE n) (ht1 n) (t n) v.1.2 v.1.2 ω
    have h2 := norm_greenMinorMat_apply_le_etaT (sz := sz) (n := n) (hE n) (ht1 n) (t n)
      (κ := v.1.1) ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩ ω
    rw [hzim] at h1 h2
    have hη0 : (0 : ℝ) ≤ (etaT (E n) (t n))⁻¹ := inv_nonneg.2 hη.le
    have hstep : ‖greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2 ω
        - greenMinorDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.1
          ⟨v.1.2, Ne.symm v.2⟩ ω‖ ≤ 2 * (etaT (E n) (t n))⁻¹ := by
      have he : greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2 ω
          - greenMinorDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.1
            ⟨v.1.2, Ne.symm v.2⟩ ω
          = green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) v.1.2 v.1.2
            - greenMinorMat sz n (t n) (zt (E n) (t n)) v.1.1 ω ⟨v.1.2, Ne.symm v.2⟩
              ⟨v.1.2, Ne.symm v.2⟩ := by
        simp only [greenDiagCentered, greenMinorDiagCentered]; ring
      rw [he]
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    refine hstep.trans ?_
    nlinarith
  · simp only [condRowReal_const]
    exact perTimeCalc_refl hsize hΨΨ0
  · intro n v
    exact rowIntegrable_of_measurable_of_bound
      (measurable_greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) v.1.2)
      (norm_greenDiagCentered_le_env (hE n) (ht1 n) (t n) v.1.2)

/-- **The integration-by-parts remainder `ibpRem` at `(i, j)`, `i ≠ j`, is `≺ Ψ²`**, per time:
`ibpRem_eq_add` splits it into
`E_i[(G_ii - m)(G_jj - m)]` and `m (E_i(G_jj - m) - (G_jj - m))`, `‖m‖ = 1`. -/
theorem perTimeDomAt_ibpRem_offdiag (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop)
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv)
    (hB : 0 ≤ B)
    (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n)
    (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2)
    (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}))
    (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => IBPRemOffPair d (sz.L n) (sz.W n))
      (fun n v ω => ‖ibpRem sz n (E n) (t n) (v.1.1, v.1.2) ω‖)
      (fun n _ _ => Ψ n * Ψ n) := by
  have hΨΨ0 : ∀ (n : ℕ) (v : IBPRemOffPair d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz),
      0 ≤ Ψ n * Ψ n := fun n _ _ => mul_nonneg (hΨ0 n) (hΨ0 n)
  have hp := IBPRem_precomp (fun n (v : IBPRemOffPair d (sz.L n) (sz.W n)) => (v.1.1, v.1.2))
    (perTimeDomAt_condRow_prod_green_diag hsize hE ht1 hΨ0 hKenv hB hEnv hΨlow hll)
  have hm := perTimeDomAt_condRow_greenDiagCentered_sub_self hd hsize hE ht1 hΨ0 hKenv hB hEnv
    hΨlow hδ1 hΩ hll
  refine stochDom_of_le_left_eventually (Eventually.of_forall fun n v ω => ?_)
    (IBPRem_add hsize hΨΨ0 hp hm)
  rw [ibpRem_eq_add (hE n) (ht1 n) v.1.1 v.1.2 ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE (hE n).le, one_mul]
  exact le_rfl

end Rem

section One

variable {d : ℕ} {sz : Sizes d} {E t δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`|greenDiagCentered| ≺ 1`**, per time, with the good event `hΩ`: on `hΩ`,
`‖G_kk - m‖ ≤ δ n ≤ 1/2 ≤ 1` (`perTimeDomAt_of_highProb`; `1 ≤ size^τ` for every `Sizes`, so no
`hsize`).  The index family `V` and the site map `kk` are free. -/
theorem perTimeDomAt_greenDiagCentered_one {V : ℕ → Type*}
    (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2)
    (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}))
    (kk : ∀ n, V n → Idx d (sz.L n) (sz.W n)) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := V)
      (fun n a ω =>
        ‖greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) (kk n a) ω‖)
      (fun _ _ _ => (1 : ℝ)) := by
  refine perTimeDomAt_of_highProb hΩ fun τ hτ => ?_
  filter_upwards [hδ1] with n hδN ω hω a
  have h1N : (1 : ℝ) ≤ (sz.size n : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
  have h := (IBPRem_goodEvent hω).norm_diag_sub_le (kk n a)
  simp only [greenDiagCentered]
  rw [mul_one]
  linarith

/-- **`|condExpDiag i| ≺ 1`**, per time, with the good event `hΩ` and the envelope `hEnv`:
`perTimeDomAt_condRow_of_envelope` at `X = G_ii - m`, `k = i`, `ζ = χ = 1`,
`Env = (η_t⁻¹ + 1)²`; the floor is `size^{-B} ≤ 1`. -/
theorem perTimeDomAt_condExpDiag_one (hsize : Tendsto sz.size atTop atTop)
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv)
    (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2)
    (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n})) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n))
      (fun n i ω =>
        ‖condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) i ω‖)
      (fun _ _ _ => (1 : ℝ)) := by
  have hone : ∀ (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), (0 : ℝ) ≤ 1 :=
    fun _ _ _ => zero_le_one
  have hlow : PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n (_ : Idx d (sz.L n) (sz.W n)) (_ : Sizes.SeqΩ sz) => (sz.size n : ℝ) ^ (-B))
      (fun _ _ _ => (1 : ℝ)) := by
    refine perTimeDomAt_const sz (fun _ => zero_le_one) (Eventually.of_forall fun n => ?_)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast sz.one_le_size n) (by linarith)
  refine perTimeDomAt_condRow_of_envelope hsize
    (V := fun n => Idx d (sz.L n) (sz.W n))
    (X := fun n (i : Idx d (sz.L n) (sz.W n)) =>
      greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) i)
    (ζ := fun _ _ _ => (1 : ℝ)) (χ := fun _ _ _ => (1 : ℝ))
    (k := fun n (i : Idx d (sz.L n) (sz.W n)) => i)
    (Env := fun n => ((etaT (E n) (t n))⁻¹ + 1) ^ 2)
    (fun n i => measurable_greenDiagCentered sz n (t n) (zt (E n) (t n))
      (mE (E n)) i)
    (fun n i => measurable_const) hone hone hKenv hB ?_ hEnv
    (fun n i ω => integrable_const _) hlow ?_
    (perTimeDomAt_greenDiagCentered_one hδ1 hΩ fun n (i : Idx d (sz.L n) (sz.W n)) => i)
  · intro n i ω
    have h1 := norm_green_diag_sub_mE_le (sz := sz) (n := n) (hE n) (ht1 n) (t n) i ω
    have hη0 : (0 : ℝ) ≤ (etaT (E n) (t n))⁻¹ :=
      (inv_pos.2 (etaT_pos (hE n) (ht1 n))).le
    simp only [greenDiagCentered]
    nlinarith
  · simp only [condRowReal_const]
    exact perTimeCalc_refl hsize hone

end One

section Whole

variable {d : ℕ} {sz : Sizes d} {E t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`|ibpRem (i, i)| ≺ 1`**, per time:
`ibpRem_eq_add` at `(i, i)` and the three bounds `E_i[(G_ii - m)²] ≺ Ψ² ≤ 1` (`hΨ1`),
`|condExpDiag i| ≺ 1`, `|G_ii - m| ≺ 1`. -/
theorem perTimeDomAt_ibpRem_diag (hsize : Tendsto sz.size atTop atTop)
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv)
    (hB : 0 ≤ B)
    (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n)
    (hΨ1 : ∀ᶠ n : ℕ in atTop, Ψ n * Ψ n ≤ 1)
    (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2)
    (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}))
    (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n))
      (fun n i ω => ‖ibpRem sz n (E n) (t n) (i, i) ω‖)
      (fun _ _ _ => (1 : ℝ)) := by
  have hone : ∀ (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz), (0 : ℝ) ≤ 1 :=
    fun _ _ _ => zero_le_one
  have hP1 : PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n))
      (fun n i ω =>
        ‖condRow sz n i
          (fun η => (green (Sizes.seqHflow sz n (t n) η) (zt (E n) (t n)) i i
              - mE (E n))
            * (green (Sizes.seqHflow sz n (t n) η) (zt (E n) (t n)) i i
              - mE (E n))) ω‖)
      (fun _ _ _ => (1 : ℝ)) :=
    mono_right_eventually
      (IBPRem_precomp (fun n (i : Idx d (sz.L n) (sz.W n)) => (i, i))
        (perTimeDomAt_condRow_prod_green_diag hsize hE ht1 hΨ0 hKenv hB hEnv hΨlow hll))
      (hΨ1.mono fun n hn u ω => hn)
  have hP2 := perTimeDomAt_condExpDiag_one hsize hE ht1 hKenv hB hEnv hδ1 hΩ
  have hP3 := perTimeDomAt_greenDiagCentered_one (E := E) (t := t) hδ1 hΩ
    (fun n (i : Idx d (sz.L n) (sz.W n)) => i)
  refine stochDom_of_le_left_eventually (Eventually.of_forall fun n i ω => ?_)
    (IBPRem_add hsize hone hP1 (IBPRem_add hsize hone hP2 hP3))
  rw [ibpRem_eq_add (hE n) (ht1 n) i i ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE (hE n).le, one_mul]
  refine add_le_add le_rfl ?_
  have hrw : condRow sz n i (greenDiagCentered sz n (t n) (zt (E n) (t n))
        (mE (E n)) i) ω
      - (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) i i - mE (E n))
      = condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) i ω
        - greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n)) i ω := rfl
  rw [hrw]
  exact norm_sub_le _ _

/-- **`|ibpRem (i, j)|` is `≺ 1` on the diagonal and `≺ Ψ²` off it**, per time: the endpoint of
the file.  The hypotheses are `hll : LocalLawDetSeq sz E t Ψ` and `hΩ`, the `HighProbAt` of the
good event `‖G_t - m‖_max ≤ δ n`, plus `hsize`. -/
theorem perTimeDomAt_ibpRem (hd : 1 ≤ d) (hsize : Tendsto sz.size atTop atTop)
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n) (hKenv : 0 ≤ Kenv)
    (hB : 0 ≤ B)
    (hEnv : ∀ᶠ n : ℕ in atTop, ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (sz.size n : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ n : ℕ in atTop, (sz.size n : ℝ) ^ (-B) ≤ Ψ n * Ψ n)
    (hΨ1 : ∀ᶠ n : ℕ in atTop, Ψ n * Ψ n ≤ 1)
    (hδ1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 / 2)
    (hΩ : HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}))
    (hll : LocalLawDetSeq sz E t Ψ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω => ‖ibpRem sz n (E n) (t n) q ω‖)
      (fun n q _ => if q.1 = q.2 then (1 : ℝ) else Ψ n * Ψ n) := by
  have hoff := perTimeDomAt_ibpRem_offdiag hd hsize hE ht1 hΨ0 hKenv hB hEnv hΨlow hδ1 hΩ hll
  have hdiag := perTimeDomAt_ibpRem_diag hsize hE ht1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hδ1 hΩ hll
  intro τ hτ D hD
  filter_upwards [hoff τ hτ D hD, hdiag τ hτ D hD] with n h1 h2 q
  obtain ⟨i, j⟩ := q
  by_cases hq : i = j
  · subst hq
    simpa using h2 i
  · have := h1 ⟨(i, j), hq⟩
    simpa [hq] using this

end Whole

end RBM.Green
