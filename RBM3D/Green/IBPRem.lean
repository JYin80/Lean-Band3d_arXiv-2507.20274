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

Ticket T2114 (ST-1, S1-29).  Port of `RBM2D/Green/IBPRem.lean` at RBM2D commit `c9a24cf` (886
lines; the code region, lines 1-528 (up to `end Whole`), is kept, the private `Checks` part is replaced by the
instances at the end of this file) to `d ≥ 3`, with the renaming rules R1-R3 of
`docs/tickets/ST1-COMMON.md` (`d : Sizes` becomes `sz : Sizes d`, `Idx L W` becomes `Idx d L W`,
`spectralZ`, `spectralM` become the merged `zt`, `mE`).  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): (`GavLGEX`) (`3_5:33`), whose proof is "that of
Lemma 4.1 in [YY_25]" (`3_5:37`); the standing hypothesis `W ≥ N^𝔠` is (`Main_DEL_COND`)
(`1_2:359`).  The mathematics is the proof of (`GavLGEX`) in [YY_25] (`Acta:4577, 4587`): the
remainder of the integration-by-parts display,
`E_i[G_ii (G_kk - m)] - m (G_kk - m) = E_i[(G_ii - m)(G_kk - m)] + m (E_i(G_kk - m) - (G_kk - m))`
(`ibpRem_eq_add`), is `O≺(Ψ²)` for `k ≠ i`: the first summand is a product of two entries of
`G - m` (each `≺ Ψ`, the local law `LocalLawDetSeq`), the second is the minor-replacement error
(`(G_kk - m) - (G^{(i)}_kk - m) = O(|G_ki| |G_ik|)` on the good event, and `G^{(i)}_kk` is
`E_i`-invariant).  On the diagonal `k = i` only `≺ 1` is claimed.  This file is the input
`ibpRem` of the pin `IBPDetThm d` (S1-30).

## Contents (namespace `RBM.Green`)

* `IBPRemOffPair d L W` -- ordered pairs of distinct fine indices.
* `IBPRem_hΨlow_of_floor` -- (new) `W^{-d/2} ≤ Ψ` gives `size^{-1} ≤ Ψ²`, the `hΨlow` below.
* `perTimeDomAt_green_diag_sub`, `perTimeDomAt_green_offdiag`, `perTimeDomAt_prod_green_diag_sub`
  -- `|G_ii - m| ≺ Ψ`, `|G_ij| ≺ Ψ` (`i ≠ j`), `|(G_ii - m)(G_jj - m)| ≺ Ψ²`, from `hll`.
* `perTimeDomAt_condRow_prod_green_diag` -- `E_i[(G_ii - m)(G_jj - m)] ≺ Ψ²`.
* `perTimeDomAt_greenDiagCentered_sub_minor` -- the minor replacement `≺ Ψ²` on the good event.
* `perTimeDomAt_condRow_greenDiagCentered_sub_self` -- `E_i(G_jj - m) - (G_jj - m) ≺ Ψ²`, `i ≠ j`.
* `perTimeDomAt_ibpRem_offdiag` -- `ibpRem (i, j) ≺ Ψ²`, `i ≠ j`.
* `perTimeDomAt_greenDiagCentered_one`, `perTimeDomAt_condExpDiag_one` -- `≺ 1`.
* `perTimeDomAt_ibpRem_diag` -- `ibpRem (i, i) ≺ 1`.
* `perTimeDomAt_ibpRem` -- the endpoint: `ibpRem (i, j) ≺ 1` on the diagonal, `≺ Ψ²` off it.

## Differences from RBM2D (every other statement equals RBM2D's after the renaming)

* **`d`-dimensional exponents.**  No exponent of a statement contains `d`: every power of `N` is
  the same power of `sz.size n = (W L)^d` (R3), `Kenv`, `B` and `τ` are free reals, the constants
  are `2` (the minor replacement `1/|G_ii| ≤ 2` on `δ ≤ 1/2`; `ζ + ζ ≤ 2 ζ`).  The `d = 2` tokens
  of RBM2D were two docstring phrases (`Z2 (W L)`, `size n = (W L)²`).
* **The floor.**  No statement takes the pin floor `W^{-d/2} ≤ Ψ` (`3_5:27`, D213) as a
  hypothesis.  The floor enters only as `hΨlow : size^{-B} ≤ Ψ²` with `B ≥ 0` free; from
  `W^{-d/2} ≤ Ψ` it holds with `B = 1`, since `size = (W L)^d ≥ W^d` (`L ≥ 1`;
  `IBPRem_hΨlow_of_floor`, for every `d` and `n`), so every
  statement holds at the floor of T2108 (the consumer `IBPDetThm d`, S1-30, obtains `hΨlow`,
  `hΨ1`, `hΨ0` from its own premises).  The old floor `W⁻¹ ≤ Ψ` is not needed.
* **`hd : 1 ≤ d`** (D200, from the merged `perTimeDomAt_of_le_left_on`, `CondDom.lean:401`) on
  `perTimeDomAt_greenDiagCentered_sub_minor`, `perTimeDomAt_condRow_greenDiagCentered_sub_self`,
  `perTimeDomAt_ibpRem_offdiag`, `perTimeDomAt_ibpRem`: the first calls it, the other three use
  the first.  The other seven statements carry no `hd`;
  `hd : 3 ≤ d` (D201) is not used (`hll` is a hypothesis).
* `ibpRem_eq_add` is called without `gaussIBP d` (a theorem, T2091 audit O1).
* `IBPRemOffPair d L W` is a subtype of pairs over the fine index `Idx d L W` (the merged
  `OffPair` of `EntryDom.lean` is over the block-product index `Vtx d L W`).
* The private helpers of RBM2D keep their role: `IBPRem_precomp` (reindexing), `IBPRem_add`
  (`ζ + ζ ≤ 2 ζ`), `IBPRem_goodEvent` (the unfolding `{∀ i j, llErrMat ≤ δ} ⊆ GoodEvent`), and the
  new `IBPRem_Gres_true` (`Gres H z true = green H z`: `llErrMat` is stated through the merged
  `Gres`, the entries of this file through `green`).  `IBPRem_one_le_size` is the merged
  `Sizes.one_le_size` (not ported).
* Not ported: the private `Checks` part (lines 531-886 of RBM2D); the instances at the end of
  this file replace it, at `d = 3`.
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss RBM.Path RBM.Ind.PerTimeCalc.PerTime
open scoped ENNReal

/-! ### Off-diagonal pairs, and three combinators -/

/-- Ordered pairs of distinct fine indices (RBM2D `IBPRemOffPair`, `Green/IBPRem.lean:98`; RBM1D
`OffPair`, `EntryBound.lean:1501`, at the fine lattice `Idx d L W`).  The merged `OffPair` of
`EntryDom.lean` is over the block-product index `Vtx d L W`. -/
abbrev IBPRemOffPair (d L W : ℕ) : Type := {p : Idx d L W × Idx d L W // p.1 ≠ p.2}

/-- Reindexing preserves a per-time domination (RBM1D `UnifDomIcc.precomp`). -/
private theorem IBPRem_precomp {d : ℕ} {sz : Sizes d} {U V : ℕ → Type*} {ξ ζ : ∀ n, U n → Sizes.SeqΩ sz → ℝ}
    (g : ∀ n, V n → U n) (h : PerTimeDomAt (Sizes.seqP sz) sz.size ξ ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (fun n a ω => ξ n (g n a) ω)
      (fun n a ω => ζ n (g n a) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn a
  exact hn (g n a)

/-- `≺` is closed under addition when both controls agree (RBM1D `UnifDomIcc.add'`): the merged
`perTimeCalc_add`, then `perTimeCalc_mono` with `ζ + ζ ≤ 2 ζ`. -/
private theorem IBPRem_add {d : ℕ} {sz : Sizes d} (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ₁ ξ₂ ζ : ∀ n, U n → Sizes.SeqΩ sz → ℝ} (hζ0 : ∀ n a ω, 0 ≤ ζ n a ω)
    (h₁ : PerTimeDomAt (Sizes.seqP sz) sz.size ξ₁ ζ)
    (h₂ : PerTimeDomAt (Sizes.seqP sz) sz.size ξ₂ ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (fun n a ω => ξ₁ n a ω + ξ₂ n a ω) ζ :=
  perTimeCalc_mono hsize hζ0 2 (Eventually.of_forall fun n a ω => by linarith)
    (perTimeCalc_add hsize h₁ h₂)

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`. -/
private theorem IBPRem_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- The good event `{∀ i j, llErrMat ≤ δ}` at one `ω` is the `GoodEvent` of the merged (4.9)
(`GoodEvent G m δ := ∀ x y, ‖G x y - (if x = y then m else 0)‖ ≤ δ`, `llErrMat` at
`M = H_u`, `green H z = (H - z)⁻¹`): the unfolding of `llErrMat` and `IBPRem_Gres_true`. -/
private theorem IBPRem_goodEvent {d : ℕ} {sz : Sizes d} {n : ℕ} {E u δ : ℝ} {ω : Sizes.SeqΩ sz}
    (h : ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) E u (Sizes.seqHflow sz n u ω) i j ≤ δ) :
    GoodEvent (green (Sizes.seqHflow sz n u ω) (zt E u)) (mE E) δ := fun x y => by
  have h1 := h x y
  unfold llErrMat at h1
  rwa [IBPRem_Gres_true] at h1

/-- **The floor of the pins gives the polynomial floor of the statements.**  From
`W^{-d/2} ≤ Ψ` (`3_5:27`, D213; the floor of `IBPDetThm d`, `LocalLaw.lean:186`) one gets
`size^{-1} ≤ Ψ²`, the `hΨlow` of this file with `B = 1`: `Ψ² ≥ W^{-d}` and
`size = (W L)^d ≥ W^d`.  It holds for every `d` and every `n` (the ticket's floor check; RBM2D
used `W⁻¹ ≤ Ψ`). -/
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

/-- **`|G_ii - m| ≺ Ψ`**, per time, from the local law (RBM1D `unifDomIcc_green_diag_subN`,
`CondStableFlow:63` at `c06b103`): `llErrMat i i = ‖G_ii - m‖`. -/
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

/-- **`|G_ij| ≺ Ψ` for `i ≠ j`**, per time, from the local law (RBM1D
`unifDomIcc_green_offdiagN`, `CondStableFlow:72`): `llErrMat i j = ‖G_ij‖` for `i ≠ j`. -/
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

/-- **`|(G_ii - m)(G_jj - m)| ≺ Ψ²`**, per time, from the local law (RBM1D
`unifDomIcc_prod_green_diag_subN`, `CondStableFlow:84`).  `hsize` is needed by the merged
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
`hΨlow` (RBM1D `unifDomIcc_condRow_prod_green_diagN`, `CondStableFlow:107`): the merged
`perTimeDomAt_condRow_of_envelope` at `X = (G_ii - m)(G_jj - m)`, `k = i`,
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

/-- **`|greenDiagCentered_j - greenMinorDiagCentered^{(i)}_j| ≺ Ψ²` for `i ≠ j`**, per time, with
the good event `hΩ` (RBM1D `unifDomIcc_greenDiagCentered_sub_minorN`, `CondStableFlow:147`): on
`hΩ` the pointwise (4.9), `norm_greenDiagCentered_sub_minor_le`, bounds it by
`2 |G_ji| |G_ij|`, which is `≺ Ψ²` (two off-diagonal entries, `perTimeCalc_mul`; RBM1D's
`UnifDomIcc.const_mul_left` with `c = 2` is here `IBPRem_add` applied to the product twice,
`2 ξ = ξ + ξ`).  The pair `v = (i, j)` carries `v.2 : i ≠ j`, and the minor entry is
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

/-- **`|E_i(G_jj - m) - (G_jj - m)| ≺ Ψ²` for `i ≠ j`**, per time (RBM1D
`unifDomIcc_condRow_greenDiagCentered_sub_selfN`, `CondStableFlow:175`): the merged
`perTimeDomAt_condRow_sub_self` at `X = G_jj - m`, the row-`i`-free surrogate
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

/-- **The integration-by-parts remainder `ibpRem` at `(i, j)`, `i ≠ j`, is `≺ Ψ²`**, per time
(RBM1D `unifDomIcc_ibpRem_offdiagN`, `CondStableFlow:238`): `ibpRem_eq_add` splits it into
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

/-- **`|greenDiagCentered| ≺ 1`**, per time, with the good event `hΩ` (RBM1D
`unifDomIcc_greenDiagCentered_oneN`, `CondStableFlow:269`): on `hΩ`, `‖G_kk - m‖ ≤ δ n ≤ 1/2 ≤ 1`
(`perTimeDomAt_of_highProb`; `1 ≤ size^τ` for every `Sizes`, so no `hsize`).  The index family
`V` and the site map `kk` are free. -/
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

/-- **`|condExpDiag_i| ≺ 1`**, per time, with the good event `hΩ` and the envelope `hEnv`
(RBM1D `unifDomIcc_condExpDiag_oneN`, `CondStableFlow:284`): the merged
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

/-- **`|ibpRem (i, i)| ≺ 1`**, per time (RBM1D `unifDomIcc_ibpRem_diagN`, `CondStableFlow:322`):
`ibpRem_eq_add` at `(i, i)` and the three bounds `E_i[(G_ii - m)²] ≺ Ψ² ≤ 1` (`hΨ1`),
`|condExpDiag_i| ≺ 1`, `|G_ii - m| ≺ 1`. -/
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

/-- **`|ibpRem (i, j)|` is `≺ 1` on the diagonal and `≺ Ψ²` off it**, per time (RBM1D
`unifDomIcc_ibpRemN`, `CondStableFlow:359`): the endpoint of the file.  The hypotheses are those of
RBM1D in the per-time form (`hll : LocalLawDetSeq sz E t Ψ`, `hΩ` the `HighProbAt` of the good
event `‖G_t - m‖_max ≤ δ n`), plus `hsize` (T2156a). -/
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

/-! ### Instances: a compiled nonempty instance of every target, at `d = 3`

The data is the preflight sequence `sz0` of `Defs/Sizes.lean` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`size n = (W_n L_n)^3`; `n = 0` is `L = 4`, `W = 32`, `size = 2097152`), `E_n = 0` (`m = i`),
`t_n = 1/2` (`η_t = (1 - t) Im m = 1/2`, so `(η_t⁻¹ + 1)² = 9`), `Ψ_n = W_n^{-3/2}` (the floor of the
pins itself), `δ_n = 1/4`, `Kenv = B = 1`.  Every deterministic hypothesis (`hd`, `hsize`, `hE`,
`ht1`, `hΨ0`, `hKenv`, `hB`, `hEnv`, `hΨlow`, `hΨ1`, `hδ1`) is proved at the data, for every `n` (no
`N = 0`, no collapsed window, no eventuality used).  The single remaining hypothesis of each
instance is `(asGMc)` at `c = 3/2`, `AsGMcSeq sz0 E t (3/2)` (another gate's pin, DECISIONS §70):
it is `hll` at `Ψ = W^{-3/2}` (`asGMcSeq_iff`), and the good event `hΩ` at `δ = 1/4` is derived
from it (merged `entryDom_goodSet_highProb_of_asGMc`, `W^{-3/4} ≤ 1/4` from `W ≥ 16`). -/

section Checks

open RBM.Gauss.SizesInst RBM.Gauss.StochDomAtInst

/-- The energy `E n = 0`. -/
private def IBPRemCkE : ℕ → ℝ := fun _ => 0

/-- The time `t n = 1/2`. -/
private noncomputable def IBPRemCkT : ℕ → ℝ := fun _ => 1 / 2

/-- The scale `Ψ n = W_n^{-3/2}`, the floor `W^{-d/2}` at `d = 3`. -/
private noncomputable def IBPRemCkPsi : ℕ → ℝ := fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))

/-- The good-event threshold `δ n = 1/4`. -/
private noncomputable def IBPRemCkDelta : ℕ → ℝ := fun _ => 1 / 4

/-- The good event `{‖G_t - m‖_max ≤ δ n}` at the data. -/
private abbrev IBPRemCkGood (n : ℕ) : Set sz0.SeqΩ :=
  {ω | ∀ i j : Idx 3 (sz0.L n) (sz0.W n),
    llErrMat 3 (sz0.L n) (sz0.W n) (IBPRemCkE n) (IBPRemCkT n)
      (Sizes.seqHflow sz0 n (IBPRemCkT n) ω) i j ≤ IBPRemCkDelta n}

/-- `W_n ≥ 32` at the data (`W_n = (2(n+1))^5`). -/
private theorem IBPRemCk_W_ge (n : ℕ) : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
  have h : 2 ^ 5 ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h2 : (32 : ℕ) ≤ sz0.W n := by simpa [sz0] using h
  exact_mod_cast h2

/-- `size n = W_n^3 L_n^3 ≥ W_n^3` at the data. -/
private theorem IBPRemCk_W3_le_size (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) ^ 3 ≤ (sz0.size n : ℝ) := by
  have hL : 1 ≤ sz0.L n := by have := sz0.three_le_L n; omega
  have h : (sz0.W n) ^ 3 ≤ sz0.size n := by
    change (sz0.W n) ^ 3 ≤ (sz0.W n * sz0.L n) ^ 3
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hL) 3
  exact_mod_cast h

private theorem IBPRemCk_hE (n : ℕ) : |IBPRemCkE n| < 2 := by
  simp [IBPRemCkE]

private theorem IBPRemCk_ht1 (n : ℕ) : IBPRemCkT n < 1 := by
  norm_num [IBPRemCkT]

private theorem IBPRemCk_hΨ0 (n : ℕ) : 0 ≤ IBPRemCkPsi n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- `Ψ² = W^{-3}`. -/
private theorem IBPRemCk_Psi_mul (n : ℕ) :
    IBPRemCkPsi n * IBPRemCkPsi n = (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ := by
  have hW0 : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith [IBPRemCk_W_ge n]
  unfold IBPRemCkPsi
  rw [← Real.rpow_add hW0, show (-(3 / 2 : ℝ) + -(3 / 2)) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hW0.le, Real.rpow_natCast]

private theorem IBPRemCk_hΨ1 : ∀ᶠ n : ℕ in atTop, IBPRemCkPsi n * IBPRemCkPsi n ≤ 1 :=
  Eventually.of_forall fun n => by
    rw [IBPRemCk_Psi_mul]
    have := IBPRemCk_W_ge n
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))

/-- `size⁻¹ ≤ Ψ²`: the floor `hΨlow` with `B = 1`, from the pin floor `W^{-3/2} ≤ Ψ` through
`IBPRem_hΨlow_of_floor` (the floor check of the ticket, at `d = 3`: here `Ψ` is the floor itself). -/
private theorem IBPRemCk_hΨlow :
    ∀ᶠ n : ℕ in atTop, (sz0.size n : ℝ) ^ (-(1 : ℝ)) ≤ IBPRemCkPsi n * IBPRemCkPsi n :=
  Eventually.of_forall fun n => IBPRem_hΨlow_of_floor sz0 n (by
    change ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
    norm_num)

/-- `η_{1/2} = 1/2` at `E = 0` (`Im m = 1`). -/
private theorem IBPRemCk_etaT (n : ℕ) : etaT (IBPRemCkE n) (IBPRemCkT n) = 1 / 2 := by
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  change (1 - 1 / 2) * (mE 0).im = 1 / 2
  rw [mE_im, h4]
  norm_num

/-- The envelope `(η_t⁻¹ + 1)² = 9 ≤ W^3 ≤ size¹`, with `Kenv = 1`. -/
private theorem IBPRemCk_hEnv :
    ∀ᶠ n : ℕ in atTop,
      ((etaT (IBPRemCkE n) (IBPRemCkT n))⁻¹ + 1) ^ 2 ≤ (sz0.size n : ℝ) ^ (1 : ℝ) :=
  Eventually.of_forall fun n => by
    have hW := IBPRemCk_W_ge n
    have h3 : (32 : ℝ) ^ 3 ≤ ((sz0.W n : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hW 3
    have h4 := IBPRemCk_W3_le_size n
    rw [IBPRemCk_etaT, Real.rpow_one, show (((1 : ℝ) / 2)⁻¹ + 1) ^ 2 = 9 by norm_num]
    norm_num at h3
    linarith

private theorem IBPRemCk_hδ1 : ∀ᶠ n : ℕ in atTop, IBPRemCkDelta n ≤ 1 / 2 :=
  Eventually.of_forall fun n => by norm_num [IBPRemCkDelta]

/-- The off-diagonal pair type is nonempty at every `n` of the data (the fine lattice has
`size n ≥ 2097152` sites, so it has two distinct ones): an instance of `IBPRemOffPair`. -/
private theorem IBPRemCk_offPair_nonempty (n : ℕ) :
    Nonempty (IBPRemOffPair 3 (sz0.L n) (sz0.W n)) := by
  have hL := sz0.three_le_L n
  have hW := sz0.W_pos n
  have : Fact (1 < sz0.W n * sz0.L n) := ⟨by nlinarith⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Idx 3 (sz0.L n) (sz0.W n))
  exact ⟨⟨(x, y), hxy⟩⟩

/-! #### The probabilistic hypotheses at the data

`hll` at the data is `(asGMc)` (`3_5:30`) at `c = 3/2`, `‖G_t - m‖_max ≺ W^{-3/2}`
(`asGMcSeq_iff`, definitional), and `hΩ` follows from it: the merged
`entryDom_goodSet_highProb_of_asGMc` gives the good event `Ω(t, c/2) = Ω(t, 3/4)` with high
probability, and `W^{-3/4} ≤ 1/4 = δ` from `W ≥ 16`. -/

/-- `hll` at the data is `AsGMcSeq` at `c = 3/2`. -/
private theorem IBPRemCk_hll (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    LocalLawDetSeq sz0 IBPRemCkE IBPRemCkT IBPRemCkPsi :=
  (asGMcSeq_iff sz0 IBPRemCkE IBPRemCkT (3 / 2)).1 hAs

/-- `hΩ` at the data, from `(asGMc)` at `c = 3/2`. -/
private theorem IBPRemCk_hΩ (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    HighProbAt (Sizes.seqP sz0) sz0.size IBPRemCkGood := by
  have h1 := entryDom_goodSet_highProb_of_asGMc sz0 sz0_admissible (E := IBPRemCkE) (t := IBPRemCkT)
    (c := 3 / 2) (by norm_num) hAs
  refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono h1 ?_
  refine Eventually.of_forall fun n ω hω i j => ?_
  have hW : (16 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by linarith [IBPRemCk_W_ge n]
  have h16 : (16 : ℝ) ^ (-(3 / 2 / 2) : ℝ) = 1 / 8 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ ((4 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
      ← Real.rpow_mul (by norm_num), show ((4 : ℕ) : ℝ) * (-(3 / 2 / 2) : ℝ) = -((3 : ℕ) : ℝ) by
        norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  have hb : ((sz0.W n : ℕ) : ℝ) ^ (-(3 / 2 / 2) : ℝ) ≤ IBPRemCkDelta n :=
    calc ((sz0.W n : ℕ) : ℝ) ^ (-(3 / 2 / 2) : ℝ) ≤ (16 : ℝ) ^ (-(3 / 2 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hW (by norm_num)
      _ = 1 / 8 := h16
      _ ≤ IBPRemCkDelta n := by norm_num [IBPRemCkDelta]
  exact (hω i j).trans hb

/-! #### The instances

One instance per target: it applies the target at the data above, with `(asGMc)` at `c = 3/2` as
the only hypothesis (`hll`, `hΩ` derived) and every deterministic hypothesis proved. -/

private theorem IBPRem_inst_green_diag_sub
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ‖green (Sizes.seqHflow sz0 n (IBPRemCkT n) ω)
        (zt (IBPRemCkE n) (IBPRemCkT n)) i i - mE (IBPRemCkE n)‖)
      (fun n _ _ => IBPRemCkPsi n) :=
  perTimeDomAt_green_diag_sub (IBPRemCk_hll hAs)

private theorem IBPRem_inst_green_offdiag
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => IBPRemOffPair 3 (sz0.L n) (sz0.W n))
      (fun n v ω => ‖green (Sizes.seqHflow sz0 n (IBPRemCkT n) ω)
        (zt (IBPRemCkE n) (IBPRemCkT n)) v.1.1 v.1.2‖)
      (fun n _ _ => IBPRemCkPsi n) :=
  perTimeDomAt_green_offdiag (IBPRemCk_hll hAs)

private theorem IBPRem_inst_prod_green_diag_sub
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q ω => ‖(green (Sizes.seqHflow sz0 n (IBPRemCkT n) ω)
          (zt (IBPRemCkE n) (IBPRemCkT n)) q.1 q.1 - mE (IBPRemCkE n))
        * (green (Sizes.seqHflow sz0 n (IBPRemCkT n) ω)
          (zt (IBPRemCkE n) (IBPRemCkT n)) q.2 q.2 - mE (IBPRemCkE n))‖)
      (fun n _ _ => IBPRemCkPsi n * IBPRemCkPsi n) :=
  perTimeDomAt_prod_green_diag_sub tendsto_sz0_size IBPRemCk_hΨ0 (IBPRemCk_hll hAs)

private theorem IBPRem_inst_condRow_prod_green_diag
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q ω => ‖condRow sz0 n q.1
        (fun η => (green (Sizes.seqHflow sz0 n (IBPRemCkT n) η)
            (zt (IBPRemCkE n) (IBPRemCkT n)) q.1 q.1 - mE (IBPRemCkE n))
          * (green (Sizes.seqHflow sz0 n (IBPRemCkT n) η)
            (zt (IBPRemCkE n) (IBPRemCkT n)) q.2 q.2 - mE (IBPRemCkE n))) ω‖)
      (fun n _ _ => IBPRemCkPsi n * IBPRemCkPsi n) :=
  perTimeDomAt_condRow_prod_green_diag (Kenv := 1) (B := 1) tendsto_sz0_size IBPRemCk_hE IBPRemCk_ht1
    IBPRemCk_hΨ0 zero_le_one zero_le_one IBPRemCk_hEnv IBPRemCk_hΨlow (IBPRemCk_hll hAs)

private theorem IBPRem_inst_greenDiagCentered_sub_minor
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => IBPRemOffPair 3 (sz0.L n) (sz0.W n))
      (fun n v ω => ‖greenDiagCentered sz0 n (IBPRemCkT n) (zt (IBPRemCkE n) (IBPRemCkT n))
          (mE (IBPRemCkE n)) v.1.2 ω
        - greenMinorDiagCentered sz0 n (IBPRemCkT n) (zt (IBPRemCkE n) (IBPRemCkT n))
          (mE (IBPRemCkE n)) v.1.1 ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun n _ _ => IBPRemCkPsi n * IBPRemCkPsi n) :=
  perTimeDomAt_greenDiagCentered_sub_minor (δ := IBPRemCkDelta) (by norm_num) tendsto_sz0_size IBPRemCk_hE
    IBPRemCk_ht1 IBPRemCk_hΨ0 IBPRemCk_hδ1 (IBPRemCk_hΩ hAs) (IBPRemCk_hll hAs)

private theorem IBPRem_inst_condRow_greenDiagCentered_sub_self
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => IBPRemOffPair 3 (sz0.L n) (sz0.W n))
      (fun n v ω => ‖condRow sz0 n v.1.1
            (greenDiagCentered sz0 n (IBPRemCkT n) (zt (IBPRemCkE n) (IBPRemCkT n))
              (mE (IBPRemCkE n)) v.1.2) ω
          - greenDiagCentered sz0 n (IBPRemCkT n) (zt (IBPRemCkE n) (IBPRemCkT n))
            (mE (IBPRemCkE n)) v.1.2 ω‖)
      (fun n _ _ => IBPRemCkPsi n * IBPRemCkPsi n) :=
  perTimeDomAt_condRow_greenDiagCentered_sub_self (δ := IBPRemCkDelta) (Kenv := 1) (B := 1)
    (by norm_num)
    tendsto_sz0_size IBPRemCk_hE IBPRemCk_ht1 IBPRemCk_hΨ0 zero_le_one zero_le_one IBPRemCk_hEnv
    IBPRemCk_hΨlow IBPRemCk_hδ1 (IBPRemCk_hΩ hAs) (IBPRemCk_hll hAs)

private theorem IBPRem_inst_ibpRem_offdiag
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => IBPRemOffPair 3 (sz0.L n) (sz0.W n))
      (fun n v ω => ‖ibpRem sz0 n (IBPRemCkE n) (IBPRemCkT n) (v.1.1, v.1.2) ω‖)
      (fun n _ _ => IBPRemCkPsi n * IBPRemCkPsi n) :=
  perTimeDomAt_ibpRem_offdiag (δ := IBPRemCkDelta) (Kenv := 1) (B := 1) (by norm_num) tendsto_sz0_size IBPRemCk_hE
    IBPRemCk_ht1 IBPRemCk_hΨ0 zero_le_one zero_le_one IBPRemCk_hEnv IBPRemCk_hΨlow IBPRemCk_hδ1 (IBPRemCk_hΩ hAs) (IBPRemCk_hll hAs)

private theorem IBPRem_inst_greenDiagCentered_one
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ‖greenDiagCentered sz0 n (IBPRemCkT n)
        (zt (IBPRemCkE n) (IBPRemCkT n)) (mE (IBPRemCkE n)) i ω‖)
      (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_greenDiagCentered_one (δ := IBPRemCkDelta) (t := IBPRemCkT) IBPRemCk_hδ1 (IBPRemCk_hΩ hAs)
    (fun n (i : Idx 3 (sz0.L n) (sz0.W n)) => i)

private theorem IBPRem_inst_condExpDiag_one
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ‖condExpDiag sz0 n (IBPRemCkT n) (zt (IBPRemCkE n) (IBPRemCkT n))
        (mE (IBPRemCkE n)) i ω‖)
      (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_condExpDiag_one (δ := IBPRemCkDelta) (Kenv := 1) (B := 1) tendsto_sz0_size IBPRemCk_hE
    IBPRemCk_ht1 zero_le_one zero_le_one IBPRemCk_hEnv IBPRemCk_hδ1 (IBPRemCk_hΩ hAs)

private theorem IBPRem_inst_ibpRem_diag
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ‖ibpRem sz0 n (IBPRemCkE n) (IBPRemCkT n) (i, i) ω‖)
      (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_ibpRem_diag (δ := IBPRemCkDelta) (Kenv := 1) (B := 1) tendsto_sz0_size IBPRemCk_hE
    IBPRemCk_ht1 IBPRemCk_hΨ0 zero_le_one zero_le_one IBPRemCk_hEnv IBPRemCk_hΨlow IBPRemCk_hΨ1
    IBPRemCk_hδ1 (IBPRemCk_hΩ hAs) (IBPRemCk_hll hAs)

/-- **The endpoint `perTimeDomAt_ibpRem` at the data**: `d = 3`, `sz0`, `E_n = 0`, `t_n = 1/2`,
`Ψ_n = W_n^{-3/2}` (the floor of the pins), `δ_n = 1/4`, `Kenv = B = 1`; the single hypothesis is
`(asGMc)` at `c = 3/2` (another gate's pin). -/
private theorem IBPRem_inst_ibpRem
    (hAs : AsGMcSeq sz0 IBPRemCkE IBPRemCkT (3 / 2)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q ω => ‖ibpRem sz0 n (IBPRemCkE n) (IBPRemCkT n) q ω‖)
      (fun n q _ => if q.1 = q.2 then (1 : ℝ) else IBPRemCkPsi n * IBPRemCkPsi n) :=
  perTimeDomAt_ibpRem (δ := IBPRemCkDelta) (Kenv := 1) (B := 1) (by norm_num) tendsto_sz0_size IBPRemCk_hE
    IBPRemCk_ht1 IBPRemCk_hΨ0 zero_le_one zero_le_one IBPRemCk_hEnv IBPRemCk_hΨlow IBPRemCk_hΨ1
    IBPRemCk_hδ1 (IBPRemCk_hΩ hAs) (IBPRemCk_hll hAs)


end Checks

end RBM.Green
