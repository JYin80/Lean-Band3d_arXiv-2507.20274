/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.CombesThomas
import RBM3D.BA.ImmLower
import RBM3D.BA.FlowPins
import RBM3D.Green.EntryCore
import RBM3D.Defs.RadialSum
import RBM3D.Analysis.Resolvent

/-!
# The Schur structure of the block Anderson resolvent with the deterministic hopping (BA-G1)

Ticket T2296.  Paper: `paper/tex/7_8_light_weight.tex` (`7_8:line`), `paper/tex/1_2_Intro_model_result.tex`
(`1_2:line`).  Deterministic part of the block Anderson `G`-chain (`7_8:1916-1950`, `7_8:2041-2069`): no
probability, no a.s. block support, no large-deviation estimate.

* Section 1 (targets 1, 2): the chain domain `BAdom` gives the real-axis bulk data at the flow parameters
  (`zztE_BA`, `7_8:1796`), every `n`; `(eq:WO)` gives `0 < g₀ ≤ 𝔡⁻¹` eventually.
* Section 2 (targets 3-7): `M = M^{(B)} ⊗ I_{W^d}` entrywise (`(def_G0)`, `1_2:631`), `‖M‖_max ≤ 1`, the
  exponential decay `(Mbound_AO2)` (`7_8:1902`) and the `ℓ¹` rows, uniform in `L, W`.
* Section 3 (target 8): `G_t - M = -M (√t V + t m) G_t = -G_t (√t V + t m) M` (`H_t = g₀ Ψ + √t V`,
  `z_t = E + (1 - t) m`, `1_2:685`, `:716`).
* Section 4 (targets 9-11): `Ψ` has no in-block entries; the Schur formulas `(4.7)`, `(4.8)` for
  `H = D + X` with `D` off-block and `X` in-block, split into the random / mixed / deterministic parts.
* Section 5: compiled nonempty instances in `RBM.BA.GreenSchurInst`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.show false

noncomputable section

open Filter Matrix

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. Targets 1, 2: the flow data on the chain domain -/

/-- `Im z_n > 0` on the chain domain (`N^{-1+ε} ≤ Im z_n`, `N ≥ 1`). -/
private theorem GreenSchur_zim_pos {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  linarith

/-- **Target 1** (`zztE_BA`, `7_8:1796`): the chain domain gives real-axis bulk data at the flow parameters,
for every `n`; `m` is `BAmF`, the real-axis value at `(g₀_n, E_n)`. -/
theorem BAflow_real {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) := by
  have hz := GreenSchur_zim_pos sz h n
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  have hr := BAdom_real hz hm (h.2 n).1
  have e := BAm_real_eq_of_self d (sz.L n) _ _ _ hr.1
  have e' : BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n =
      BAm d (sz.L n) (sz.lam n) (z n) / (Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) : ℂ) := e
  rw [e']
  exact hr

/-- **Target 2** (`(eq:WO)`, `1_2:363`, at the flow coupling): eventually `0 < g₀_n ≤ 𝔡⁻¹`. -/
theorem BAflow_lam0_window {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹ := by
  filter_upwards [h.1.2.2.2.2] with n hn
  obtain ⟨hlo, hhi⟩ := hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hlo
  have hz := GreenSchur_zim_pos sz h n
  have hm := (BAm_self d (sz.L n) (sz.lam n) (z n) hz).1
  have ht0 := BAt0_pos hz hm
  have ht1 := BAt0_lt_one hz hm
  have hs0 : 0 < Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) := Real.sqrt_pos.mpr ht0
  have hs1 : Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) ≤ 1 := Real.sqrt_le_one.mpr ht1.le
  have e : BAflowLam0 sz z n =
      Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n := rfl
  rw [e]
  refine ⟨mul_pos hs0 hlam, ?_⟩
  nlinarith

/-! ## 2. Targets 3-7: `M = M^{(B)} ⊗ I_{W^d}` and its bounds -/

/-- **Target 3** (`(def_G0)`, `1_2:631`): `M_{xy} = 1(x, y same offset) M^{(B)}_{[x][y]}`. -/
theorem BAMfine_eq {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (hm : 0 < (BAmF sz lam0 E n).im)
    (x y : Idx d (sz.L n) (sz.W n)) :
    BAMfine sz lam0 E n x y =
      if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then
        BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
          (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1
      else 0 := by
  have hw : ((E n : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by
    simpa using hm.ne'
  exact BAMres_fine_apply d (sz.L n) (sz.W n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) hw x y

/-- **Target 4** (`‖M‖_max ≤ 1`): the Ward row identity at the real axis, `∑_b |M^{(B)}_{ab}|² = 1`. -/
theorem BAMfine_norm_le_one {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (h : BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n))
    (x y : Idx d (sz.L n) (sz.W n)) : ‖BAMfine sz lam0 E n x y‖ ≤ 1 := by
  rw [BAMfine_eq sz lam0 E n h.1 x y]
  split_ifs
  · have hrow := BAMB_row_sq_real d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) h
      (split d (sz.L n) (sz.W n) x).1
    have hle : ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
        (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1‖ ^ 2 ≤ 1 := by
      rw [← hrow]
      exact Finset.single_le_sum (f := fun b => ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
        (split d (sz.L n) (sz.W n) x).1 b‖ ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ (split d (sz.L n) (sz.W n) y).1)
    nlinarith [norm_nonneg (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
        (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1)]
  · simp

/-- **Target 5** (`(Mbound_AO2)`, `7_8:1902`, on the fine lattice): for every `0 < g₀ ≤ Λ`, with the rate
`BAct_rate d Λ κ` (`d, Λ, κ` only). -/
theorem BAMfine_decay (d : ℕ) (hd : 0 < d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) (sz : Sizes d)
    (lam0 E : ℕ → ℝ) (n : ℕ) (hL : 3 ≤ sz.L n) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ Λ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖BAMfine sz lam0 E n x y‖ ≤ (BAct_rate d Λ κ)⁻¹ *
      Real.exp (-BAct_rate d Λ κ *
        (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - (split d (sz.L n) (sz.W n) y).1) : ℝ)) := by
  rw [BAMfine_eq sz lam0 E n hr.1.1 x y]
  split_ifs
  · exact BAMB_decay_large d (sz.L n) hL hd Λ (lam0 n) κ (E n) (BAmF sz lam0 E n) hΛ hg hgΛ hκ hr _ _
  · have := BAct_rate_pos d Λ κ hd hΛ hκ
    rw [norm_zero]
    exact mul_nonneg (inv_nonneg.mpr this.le) (Real.exp_pos _).le

/-- **Target 6** (`ℓ¹` row of `M^{(B)}`, uniform in `L`; `d = k + 2`): `∑_b |M^{(B)}_{ab}| ≤ c⁻¹ expC k c`,
`c = BAct_rate (k + 2) Λ κ`. -/
theorem BAMB_row_l1 (k L : ℕ) [NeZero L] (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal (k + 2) L g κ E m) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ‖BAMB (k + 2) L g (E : ℂ) m a b‖ ≤
      (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ) := by
  have hc := BAct_rate_pos (k + 2) Λ κ (by omega) hΛ hκ
  calc ∑ b : Zd (k + 2) L, ‖BAMB (k + 2) L g (E : ℂ) m a b‖
      ≤ ∑ b : Zd (k + 2) L, (BAct_rate (k + 2) Λ κ)⁻¹ *
          Real.exp (-(BAct_rate (k + 2) Λ κ * (zdistD (k + 2) L (a - b) : ℝ))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have := BAMB_decay_large (k + 2) L hL (by omega) Λ g κ E m hΛ hg hgΛ hκ hr a b
        rwa [neg_mul] at this
    _ = (BAct_rate (k + 2) Λ κ)⁻¹ * ∑ x : Zd (k + 2) L,
          Real.exp (-(BAct_rate (k + 2) Λ κ * (zdistD (k + 2) L x : ℝ))) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.subLeft a)
          (fun x : Zd (k + 2) L => Real.exp (-(BAct_rate (k + 2) Λ κ * (zdistD (k + 2) L x : ℝ))))
    _ ≤ (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ) :=
        mul_le_mul_of_nonneg_left (sum_radial_exp_decay_le k hc) (inv_nonneg.mpr hc.le)

/-- The sum over the fine lattice of a function of the block coordinate, supported on one offset, is the sum
over the blocks. -/
private theorem GreenSchur_fibre_sum (d L W : ℕ) [NeZero L] [NeZero W] (x : Idx d L W) (f : Zd d L → ℝ) :
    ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ b : Zd d L, f b := by
  have h : ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ y : Idx d L W, (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0)
        (splitEquiv d L W y) := rfl
  rw [h, Equiv.sum_comp (splitEquiv d L W) (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0),
    Fintype.sum_prod_type]
  simp

/-- **Target 7** (`ℓ¹` row of `M` on the fine lattice, uniform in `L, W`; `d = k + 2`):
`∑_y |M_{xy}| ≤ c⁻¹ expC k c`. -/
theorem BAMfine_row_l1 (k : ℕ) (sz : Sizes (k + 2)) (lam0 E : ℕ → ℝ) (n : ℕ) (Λ κ : ℝ) (hL : 3 ≤ sz.L n)
    (hΛ : 0 < Λ) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ Λ) (hκ : 0 < κ)
    (hr : BAReal (k + 2) (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (x : Idx (k + 2) (sz.L n) (sz.W n)) :
    ∑ y : Idx (k + 2) (sz.L n) (sz.W n), ‖BAMfine sz lam0 E n x y‖ ≤
      (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ) := by
  have h1 : ∑ y : Idx (k + 2) (sz.L n) (sz.W n), ‖BAMfine sz lam0 E n x y‖ =
      ∑ y : Idx (k + 2) (sz.L n) (sz.W n),
        (if (split (k + 2) (sz.L n) (sz.W n) x).2 = (split (k + 2) (sz.L n) (sz.W n) y).2 then
          ‖BAMB (k + 2) (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
            (split (k + 2) (sz.L n) (sz.W n) x).1 (split (k + 2) (sz.L n) (sz.W n) y).1‖ else 0) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [BAMfine_eq sz lam0 E n hr.1.1 x y]
    split_ifs <;> simp
  rw [h1]
  refine le_trans (le_of_eq (GreenSchur_fibre_sum (k + 2) (sz.L n) (sz.W n) x
    (fun b => ‖BAMB (k + 2) (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
      (split (k + 2) (sz.L n) (sz.W n) x).1 b‖))) ?_
  exact BAMB_row_l1 k (sz.L n) hL Λ (lam0 n) κ (E n) (BAmF sz lam0 E n) hΛ hg hgΛ hκ hr _

/-! ## 3. Target 8: the resolvent identity with the deterministic hopping -/

/-- New vocabulary: `√t V + t m`, so that `G_t⁻¹ - M⁻¹ = BAflowPert` (`H_t = g₀ Ψ + √t V`,
`z_t = E + (1 - t) m`, `M = (g₀ Ψ - E - m)⁻¹`). -/
noncomputable def BAflowPert {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam 0) n t ω i j) +
    ((t : ℂ) * BAmF sz lam0 E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- `H_t = g₀ Ψ + √t V` is Hermitian. -/
private theorem GreenSchur_H_herm {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA lam0 n t ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n t ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- `g₀ Ψ` is Hermitian. -/
private theorem GreenSchur_Psi_herm {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) :
    ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- **Target 8** (`G_t - M = -M (√t V + t m) G_t = -G_t (√t V + t m) M`; `t < 1`, `Im m > 0`): the resolvent
identity of the block Anderson flow with the deterministic hopping, both orders. -/
theorem BAGt_sub_BAMfine {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (ht : t < 1)
    (hm : 0 < (BAmF sz lam0 E n).im) :
    BAGt sz lam0 E n t ω - BAMfine sz lam0 E n =
        -(BAMfine sz lam0 E n * BAflowPert sz lam0 E n t ω * BAGt sz lam0 E n t ω) ∧
      BAGt sz lam0 E n t ω - BAMfine sz lam0 E n =
        -(BAGt sz lam0 E n t ω * BAflowPert sz lam0 E n t ω * BAMfine sz lam0 E n) := by
  set m := BAmF sz lam0 E n with hmdef
  set A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    sz.seqHflowBA lam0 n t ω - ztOf m (E n) t • (1 : Matrix _ _ ℂ) with hA
  set B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) - ((E n : ℂ) + m) • (1 : Matrix _ _ ℂ) with hB
  have hzim : (ztOf m (E n) t).im ≠ 0 := by
    rw [ztOf_im]
    unfold etaOf
    exact (mul_pos (by linarith) hm).ne'
  have hwim : ((E n : ℂ) + m).im ≠ 0 := by simpa using hm.ne'
  have hUA : IsUnit A := isUnit_sub_smul_of_isHermitian (GreenSchur_H_herm sz lam0 n t ω) hzim
  have hUB : IsUnit B := isUnit_sub_smul_of_isHermitian (GreenSchur_Psi_herm sz lam0 n) hwim
  have hG : BAGt sz lam0 E n t ω = Ring.inverse A := by
    unfold BAGt Gres
    simp only [↓reduceIte]
    rfl
  have hM : BAMfine sz lam0 E n = Ring.inverse B := rfl
  have hAB : A - B = BAflowPert sz lam0 E n t ω := by
    unfold BAflowPert
    have e1 : ztOf m (E n) t = (E n : ℂ) + (1 - (t : ℂ)) * m := rfl
    have e2 : sz.seqHflowBA lam0 n t ω = (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) +
        Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam 0) n t ω i j := rfl
    rw [hA, hB, e2, e1]
    module
  rw [hG, hM, ← hAB]
  have h1 : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel _ hUA
  have h2 : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel _ hUA
  have h3 : Ring.inverse B * B = 1 := Ring.inverse_mul_cancel _ hUB
  have h4 : B * Ring.inverse B = 1 := Ring.mul_inverse_cancel _ hUB
  have e1 : Ring.inverse B * (A - B) * Ring.inverse A = Ring.inverse B - Ring.inverse A := by
    rw [mul_sub, sub_mul, mul_assoc (Ring.inverse B) A (Ring.inverse A), h2, mul_one, h3, one_mul]
  have e2 : Ring.inverse A * (A - B) * Ring.inverse B = Ring.inverse B - Ring.inverse A := by
    rw [mul_sub, sub_mul, h1, one_mul, mul_assoc (Ring.inverse A) B (Ring.inverse B), h4, mul_one]
  refine ⟨?_, ?_⟩
  · rw [e1, neg_sub]
  · rw [e2, neg_sub]

/-! ## 4. Targets 9-11: `Ψ` off-block, and the Schur formulas `(4.7)`, `(4.8)` for `H = D + X` -/

/-- **Target 9** (`Ψ^{(B)}_{aa} = 0`): `Ψ` has no in-block entries. -/
theorem BAPsiI_inBlock (d L W : ℕ) [NeZero L] [NeZero W] (x y : Idx d L W)
    (h : (split d L W x).1 = (split d L W y).1) : PsiI d L W x y = 0 := by
  unfold PsiI PsiV
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  have h' : (splitEquiv d L W x).1 = (splitEquiv d L W y).1 := h
  have h0 : PsiB d L (splitEquiv d L W x).1 (splitEquiv d L W y).1 = 0 := by
    rw [h']
    simp [PsiB, Adj]
  rw [h0, zero_mul]

/-- The double sum over `κ × κ` splits along a predicate on each variable. -/
private theorem GreenSchur_sum_split2 {κ : Type} [Fintype κ] (p : κ → Prop) [DecidablePred p]
    (f : κ → κ → ℂ) :
    ∑ k, ∑ l, f k l =
      (∑ k ∈ Finset.univ.filter p, ∑ l ∈ Finset.univ.filter p, f k l) +
      (∑ k ∈ Finset.univ.filter p, ∑ l ∈ Finset.univ.filter (fun l => ¬ p l), f k l) +
      (∑ k ∈ Finset.univ.filter (fun k => ¬ p k), ∑ l ∈ Finset.univ.filter p, f k l) +
      (∑ k ∈ Finset.univ.filter (fun k => ¬ p k), ∑ l ∈ Finset.univ.filter (fun l => ¬ p l), f k l) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]
  have h1 : ∀ k : κ, ∑ l, f k l =
      (∑ l ∈ Finset.univ.filter p, f k l) + ∑ l ∈ Finset.univ.filter (fun l => ¬ p l), f k l :=
    fun k => (Finset.sum_filter_add_sum_filter_not Finset.univ p (f k)).symm
  simp only [h1, Finset.sum_add_distrib]
  ring

/-- **Target 10** (Schur `(4.8)`, the diagonal entry, with `H = D + X`; `D` off-block, `X` in-block): the quadratic
form `∑_{k,l} H_{ik} G^{(i)}_{kl} H_{li}` splits into the random-random, the two mixed and the deterministic part.
(BA structure: `b = (split ·).1`, `D = g₀ Ψ`, `X = √t V`.) -/
theorem green_diag_split {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β)
    (D X : Matrix ι ι ℂ) (z : ℂ) (hD : ∀ i k, b i = b k → D i k = 0) (hX : ∀ i k, b i ≠ b k → X i k = 0)
    (hU : IsUnit (D + X - z • (1 : Matrix ι ι ℂ)).det) (i : ι) (hGii : RBM.green (D + X) z i i ≠ 0) :
    RBM.green (D + X) z i i =
      (X i i - z -
        ((∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 = b i),
              X i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * X l.1 i) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 ≠ b i),
              X i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * D l.1 i) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 = b i),
              D i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * X l.1 i) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 ≠ b i),
              D i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * D l.1 i)))⁻¹ := by
  refine (RBM.Green.green_diag_paper (H := D + X) hU i hGii).trans (congrArg (fun w => w⁻¹) ?_)
  have e1 : (D + X) i i = X i i := by rw [Matrix.add_apply, hD i i rfl, zero_add]
  have hX' : ∀ k : {a : ι // a ≠ i}, b k.1 = b i → (D + X) i k.1 = X i k.1 := fun k hk => by
    rw [Matrix.add_apply, hD i k.1 hk.symm, zero_add]
  have hD' : ∀ k : {a : ι // a ≠ i}, b k.1 ≠ b i → (D + X) i k.1 = D i k.1 := fun k hk => by
    rw [Matrix.add_apply, hX i k.1 (fun h => hk h.symm), add_zero]
  have hX'' : ∀ l : {a : ι // a ≠ i}, b l.1 = b i → (D + X) l.1 i = X l.1 i := fun l hl => by
    rw [Matrix.add_apply, hD l.1 i hl, zero_add]
  have hD'' : ∀ l : {a : ι // a ≠ i}, b l.1 ≠ b i → (D + X) l.1 i = D l.1 i := fun l hl => by
    rw [Matrix.add_apply, hX l.1 i hl, add_zero]
  rw [GreenSchur_sum_split2 (fun k : {a : ι // a ≠ i} => b k.1 = b i)
    (fun k l => (D + X) i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * (D + X) l.1 i), e1]
  refine congrArg (fun w => X i i - z - w) ?_
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    rw [hX' k (Finset.mem_filter.mp hk).2, hX'' l (Finset.mem_filter.mp hl).2]
  · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    rw [hX' k (Finset.mem_filter.mp hk).2, hD'' l (Finset.mem_filter.mp hl).2]
  · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    rw [hD' k (Finset.mem_filter.mp hk).2, hX'' l (Finset.mem_filter.mp hl).2]
  · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    rw [hD' k (Finset.mem_filter.mp hk).2, hD'' l (Finset.mem_filter.mp hl).2]

/-- **Target 11** (Schur `(4.7)`, the off-diagonal entry, with the same split): one random and one deterministic
row sum. -/
theorem green_off_split {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β)
    (D X : Matrix ι ι ℂ) (z : ℂ) (hD : ∀ i k, b i = b k → D i k = 0) (hX : ∀ i k, b i ≠ b k → X i k = 0)
    (hU : IsUnit (D + X - z • (1 : Matrix ι ι ℂ)).det) (i : ι) (hGii : RBM.green (D + X) z i i ≠ 0)
    (j : {a : ι // a ≠ i}) :
    RBM.green (D + X) z i j.1 = -RBM.green (D + X) z i i *
      ((∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
          X i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k j) +
       (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
          D i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k j)) := by
  refine (RBM.Green.green_off_diag_paper (H := D + X) hU i hGii j).trans (congrArg (fun w => -RBM.green (D + X) z i i * w) ?_)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : {a : ι // a ≠ i} => b k.1 = b i)]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Matrix.add_apply, hD i k.1 (Finset.mem_filter.mp hk).2.symm, zero_add]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Matrix.add_apply, hX i k.1 (fun h => (Finset.mem_filter.mp hk).2 h.symm), add_zero]

/-! ## 5. Compiled nonempty instances (`d = 3`, `L = 4`)

* Targets 3-9: the one-point flow data of the merged `CouplingWindow.lean` (`szP`: `L ≡ 4`, `W ≡ 2`,
  `lam ≡ 10`; the flow point `(g₀, E, m₀) = (g0P, EP, m0P)` of `z_S(4, 10)`, `BAReal 3 4 g0P (Im m_S) EP m0P`).
* Targets 10, 11: `ι = β = Fin 2`, `b = id`, `X = 0`, `D = [[0, 1], [1, 0]]`, `z = i`.
* Targets 1, 2: a `BAFlow` instance at a growing sequence (`L ≡ 4`, `W_n = n + 1`, `lam ≡ 1/100`,
  `z ≡ w - m_w`, `w = 11 i / 10`, `κ = 9/10`, `ε = 1/2`, `𝔠 = 1/9`, `𝔡 = 1/2`), built from `BASelf_subord`. -/

namespace GreenSchurInst

open RBM.BA.CouplingWindowInst RBM.BA.MFixedPointInst

/-- `m(E, g₀)` of the one-point flow data is `m0P`. -/
private theorem GreenSchur_mF : BAmF szP (fun _ => g0P) (fun _ => EP) 0 = m0P :=
  BAm_real_eq_of_self 3 4 g0P EP m0P flowP_data.2.2

private theorem GreenSchur_hr : BAReal 3 (szP.L 0) g0P (mS 4 10).im EP
    (BAmF szP (fun _ => g0P) (fun _ => EP) 0) := by
  rw [GreenSchur_mF]
  exact flowP_real

private theorem GreenSchur_hm : 0 < (BAmF szP (fun _ => g0P) (fun _ => EP) 0).im := by
  rw [GreenSchur_mF]
  exact flowP_data.2.2.1

private theorem GreenSchur_hs : BASelf 3 (szP.L 0) g0P (EP : ℂ) (BAmF szP (fun _ => g0P) (fun _ => EP) 0) := by
  rw [GreenSchur_mF]
  exact flowP_data.2.2

/-- (I1) Target 6 at `k = 1`, `L = 4`, `Λ = g = g₀`, `κ = Im m_S`, the flow datum `flowP_real`. -/
theorem inst_row_l1 (a : Zd (1 + 2) 4) :
    ∑ b : Zd (1 + 2) 4, ‖BAMB (1 + 2) 4 g0P (EP : ℂ) m0P a b‖ ≤
      (BAct_rate (1 + 2) g0P (mS 4 10).im)⁻¹ * expC 1 (BAct_rate (1 + 2) g0P (mS 4 10).im) :=
  BAMB_row_l1 1 4 (by norm_num) g0P g0P (mS 4 10).im EP m0P g0P_pos g0P_pos le_rfl (selfS 4 10).1
    flowP_real a

/-- Target 3 at the one-point sequence, `x ≠ y`. -/
theorem inst_Mfine_eq :
    BAMfine szP (fun _ => g0P) (fun _ => EP) 0 0 (fun _ => 1) =
      if (split 3 4 2 0).2 = (split 3 4 2 (fun _ => 1)).2 then
        BAMB 3 4 g0P (EP : ℂ) m0P (split 3 4 2 0).1 (split 3 4 2 (fun _ => 1)).1 else 0 := by
  have h := BAMfine_eq szP (fun _ => g0P) (fun _ => EP) 0 GreenSchur_hm 0 (fun _ => 1)
  rw [GreenSchur_mF] at h
  exact h

/-- Target 4 at the one-point sequence. -/
theorem inst_Mfine_norm (x y : Idx 3 4 2) : ‖BAMfine szP (fun _ => g0P) (fun _ => EP) 0 x y‖ ≤ 1 :=
  BAMfine_norm_le_one szP (fun _ => g0P) (fun _ => EP) 0 GreenSchur_hs x y

/-- Target 5 at the one-point sequence, `Λ = g₀`, `κ = Im m_S`. -/
theorem inst_Mfine_decay (x y : Idx 3 4 2) :
    ‖BAMfine szP (fun _ => g0P) (fun _ => EP) 0 x y‖ ≤ (BAct_rate 3 g0P (mS 4 10).im)⁻¹ *
      Real.exp (-BAct_rate 3 g0P (mS 4 10).im * (zdistD 3 4 ((split 3 4 2 x).1 - (split 3 4 2 y).1) : ℝ)) :=
  BAMfine_decay 3 (by norm_num) g0P (mS 4 10).im g0P_pos (selfS 4 10).1 szP (fun _ => g0P) (fun _ => EP) 0
    (by norm_num [szP]) g0P_pos le_rfl GreenSchur_hr x y

/-- Target 7 at the one-point sequence (`d = 1 + 2`). -/
theorem inst_Mfine_row_l1 (x : Idx (1 + 2) 4 2) :
    ∑ y : Idx (1 + 2) 4 2, ‖BAMfine szP (fun _ => g0P) (fun _ => EP) 0 x y‖ ≤
      (BAct_rate (1 + 2) g0P (mS 4 10).im)⁻¹ * expC 1 (BAct_rate (1 + 2) g0P (mS 4 10).im) :=
  BAMfine_row_l1 1 szP (fun _ => g0P) (fun _ => EP) 0 g0P (mS 4 10).im (by norm_num [szP]) g0P_pos g0P_pos
    le_rfl (selfS 4 10).1 GreenSchur_hr x

/-- Target 8 at the one-point sequence, `t = 1/2`, `ω ≡ 1`. -/
theorem inst_Gt_sub_Mfine :
    BAGt szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2) (fun _ => 1) - BAMfine szP (fun _ => g0P) (fun _ => EP) 0 =
        -(BAMfine szP (fun _ => g0P) (fun _ => EP) 0 * BAflowPert szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2)
          (fun _ => 1) * BAGt szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2) (fun _ => 1)) ∧
      BAGt szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2) (fun _ => 1) - BAMfine szP (fun _ => g0P) (fun _ => EP) 0 =
        -(BAGt szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2) (fun _ => 1) *
          BAflowPert szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2) (fun _ => 1) *
          BAMfine szP (fun _ => g0P) (fun _ => EP) 0) :=
  BAGt_sub_BAMfine szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2) (fun _ => 1) (by norm_num) GreenSchur_hm

/-- (I2) Target 9 at `d = 3`, `L = 4`, `W = 2`: two lattice points of the same block, different offsets. -/
theorem inst_PsiI_inBlock : PsiI 3 4 2 (0 : Idx 3 4 2) (fun _ => 1) = 0 ∧
    (0 : Idx 3 4 2) ≠ (fun _ => 1) ∧ (split 3 4 2 (0 : Idx 3 4 2)).2 ≠ (split 3 4 2 (fun _ => 1 : Idx 3 4 2)).2 :=
  ⟨BAPsiI_inBlock 3 4 2 0 (fun _ => 1) (by decide), by decide, by decide⟩

/-- (I3) the data `ι = β = Fin 2`, `b = id`, `X = 0`, `D = [[0, 1], [1, 0]]`, `z = i`. -/
private def GreenSchur_D2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

private theorem GreenSchur_D2_det :
    (GreenSchur_D2 + 0 - Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = -2 := by
  simp [GreenSchur_D2, Matrix.det_fin_two]
  norm_num

private theorem GreenSchur_D2_G00 : RBM.green (GreenSchur_D2 + 0) Complex.I 0 0 ≠ 0 := by
  unfold RBM.green
  rw [Matrix.inv_def, GreenSchur_D2_det, Matrix.smul_apply, Matrix.adjugate_fin_two]
  simp [GreenSchur_D2, Ring.inverse_eq_inv']

private theorem GreenSchur_D2_hD : ∀ i k : Fin 2, (id i : Fin 2) = id k → GreenSchur_D2 i k = 0 := by
  intro i k h
  have h' : i = k := h
  subst h'
  fin_cases i <;> simp [GreenSchur_D2]

private theorem GreenSchur_D2_hU :
    IsUnit (GreenSchur_D2 + 0 - Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det := by
  rw [GreenSchur_D2_det]
  norm_num

/-- (I3) Target 10 at the data above (`G_{00} = i/2 ≠ 0`, the minor `G^{(0)}` is `1 × 1`). -/
theorem inst_green_diag :
    RBM.green (GreenSchur_D2 + 0) Complex.I 0 0 =
      ((0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - Complex.I -
        ((∑ k ∈ Finset.univ.filter (fun k : {a : Fin 2 // a ≠ 0} => (id k.1 : Fin 2) = id 0),
            ∑ l ∈ Finset.univ.filter (fun l : {a : Fin 2 // a ≠ 0} => (id l.1 : Fin 2) = id 0),
              (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 k.1 *
                RBM.Green.minorGreen (RBM.green (GreenSchur_D2 + 0) Complex.I) 0 k l *
                (0 : Matrix (Fin 2) (Fin 2) ℂ) l.1 0) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : Fin 2 // a ≠ 0} => (id k.1 : Fin 2) = id 0),
            ∑ l ∈ Finset.univ.filter (fun l : {a : Fin 2 // a ≠ 0} => (id l.1 : Fin 2) ≠ id 0),
              (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 k.1 *
                RBM.Green.minorGreen (RBM.green (GreenSchur_D2 + 0) Complex.I) 0 k l * GreenSchur_D2 l.1 0) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : Fin 2 // a ≠ 0} => (id k.1 : Fin 2) ≠ id 0),
            ∑ l ∈ Finset.univ.filter (fun l : {a : Fin 2 // a ≠ 0} => (id l.1 : Fin 2) = id 0),
              GreenSchur_D2 0 k.1 * RBM.Green.minorGreen (RBM.green (GreenSchur_D2 + 0) Complex.I) 0 k l *
                (0 : Matrix (Fin 2) (Fin 2) ℂ) l.1 0) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : Fin 2 // a ≠ 0} => (id k.1 : Fin 2) ≠ id 0),
            ∑ l ∈ Finset.univ.filter (fun l : {a : Fin 2 // a ≠ 0} => (id l.1 : Fin 2) ≠ id 0),
              GreenSchur_D2 0 k.1 * RBM.Green.minorGreen (RBM.green (GreenSchur_D2 + 0) Complex.I) 0 k l *
                GreenSchur_D2 l.1 0)))⁻¹ :=
  green_diag_split (id : Fin 2 → Fin 2) GreenSchur_D2 0 Complex.I GreenSchur_D2_hD (fun i k _ => rfl)
    GreenSchur_D2_hU 0 GreenSchur_D2_G00

/-- (I3) Target 11 at the same data, `j = 1`. -/
theorem inst_green_off :
    RBM.green (GreenSchur_D2 + 0) Complex.I 0 (⟨1, by decide⟩ : {a : Fin 2 // a ≠ 0}).1 =
      -RBM.green (GreenSchur_D2 + 0) Complex.I 0 0 *
        ((∑ k ∈ Finset.univ.filter (fun k : {a : Fin 2 // a ≠ 0} => (id k.1 : Fin 2) = id 0),
            (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 k.1 *
              RBM.Green.minorGreen (RBM.green (GreenSchur_D2 + 0) Complex.I) 0 k ⟨1, by decide⟩) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : Fin 2 // a ≠ 0} => (id k.1 : Fin 2) ≠ id 0),
            GreenSchur_D2 0 k.1 *
              RBM.Green.minorGreen (RBM.green (GreenSchur_D2 + 0) Complex.I) 0 k ⟨1, by decide⟩)) :=
  green_off_split (id : Fin 2 → Fin 2) GreenSchur_D2 0 Complex.I GreenSchur_D2_hD (fun i k _ => rfl)
    GreenSchur_D2_hU 0 GreenSchur_D2_G00 ⟨1, by decide⟩

/-! ### The chain domain `BAFlow` at a growing sequence (targets 1, 2) -/

/-- The sizes of the `BAFlow` instance: `L ≡ 4`, `W_n = n + 1`, `lam ≡ 1/100` (`N_n = (4 (n + 1))^3 → ∞`). -/
private def GreenSchur_szF : Sizes 3 where
  L := fun _ => 4
  W := fun n => n + 1
  lam := fun _ => 1 / 100
  three_le_L := fun _ => by norm_num
  W_pos := fun n => Nat.succ_pos n

private def GreenSchur_wF : ℂ := ⟨0, 11 / 10⟩

private theorem GreenSchur_wF_norm : ‖GreenSchur_wF‖ = 11 / 10 := by
  have h : GreenSchur_wF = ((11 / 10 : ℝ) : ℂ) * Complex.I := by apply Complex.ext <;> simp [GreenSchur_wF]
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num

private theorem GreenSchur_wF_im : GreenSchur_wF.im = 11 / 10 := rfl

/-- `m_w` at `w = 11i/10`, `g = 1/100`, and `z = w - m_w` (subordination point; constant sequence). -/
private def GreenSchur_mF0 : ℂ := BAmSubord 3 4 (1 / 100) GreenSchur_wF

private def GreenSchur_zF : ℕ → ℂ := fun _ => GreenSchur_wF - GreenSchur_mF0

private theorem GreenSchur_sub :
    BASelf 3 4 (1 / 100) (GreenSchur_wF - GreenSchur_mF0) GreenSchur_mF0 ∧
      GreenSchur_wF.im / (‖GreenSchur_wF‖ ^ 2 + (1 / 100 : ℝ) ^ 2 * ((4 ^ 3 : ℕ) : ℝ)) ≤ GreenSchur_mF0.im ∧
      GreenSchur_mF0.im ≤ GreenSchur_wF.im⁻¹ ∧ 0 < (GreenSchur_wF - GreenSchur_mF0).im :=
  BASelf_subord 3 4 (1 / 100) (w := GreenSchur_wF) (by rw [GreenSchur_wF_im]; norm_num)

private theorem GreenSchur_mim_lo : (9 / 10 : ℝ) ≤ GreenSchur_mF0.im := by
  have h := GreenSchur_sub.2.1
  rw [GreenSchur_wF_norm, GreenSchur_wF_im] at h
  refine le_trans ?_ h
  rw [le_div_iff₀ (by positivity)]
  norm_num

private theorem GreenSchur_mim_hi : GreenSchur_mF0.im ≤ 10 / 11 := by
  have h := GreenSchur_sub.2.2.1
  rw [GreenSchur_wF_im] at h
  refine le_trans h ?_
  norm_num

private theorem GreenSchur_Am : BAm 3 4 (1 / 100) (GreenSchur_wF - GreenSchur_mF0) = GreenSchur_mF0 :=
  BASelf_unique 3 4 (1 / 100) _ _ _ GreenSchur_sub.2.2.2.le
    (BAm_self 3 4 (1 / 100) _ GreenSchur_sub.2.2.2) GreenSchur_sub.1

private theorem GreenSchur_size (n : ℕ) : GreenSchur_szF.size n = ((n + 1) * 4) ^ 3 := rfl

/-- The `BAFlow` instance: `κ = 9/10`, `ε = 1/2`, `𝔠 = 1/9`, `𝔡 = 1/2`, the constant sequence `z ≡ w - m_w`. -/
theorem inst_BAFlow : BAFlow GreenSchur_szF (9 / 10) (1 / 2) (1 / 9) (1 / 2) GreenSchur_zF := by
  refine ⟨⟨by norm_num, by norm_num, ?_, ?_, ?_⟩, fun n => ?_⟩
  · -- `N → ∞`
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    rw [GreenSchur_size]
    have h : n ≤ ((n + 1) * 4) ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    exact_mod_cast h
  · -- `W ≥ N^𝔠`
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : (0 : ℝ) ≤ 4 * ((n : ℝ) + 1) := by positivity
    have e1 : (((GreenSchur_szF.size n : ℕ)) : ℝ) = (4 * ((n : ℝ) + 1)) ^ (3 : ℝ) := by
      rw [GreenSchur_size, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      push_cast
      ring
    have e2 : (((GreenSchur_szF.size n : ℕ)) : ℝ) ^ (1 / 9 : ℝ) = (4 * ((n : ℝ) + 1)) ^ ((3 : ℝ)⁻¹) := by
      rw [e1, ← Real.rpow_mul hx]
      norm_num
    rw [e2, Real.rpow_inv_le_iff_of_pos hx (by positivity) (by norm_num),
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    show 4 * ((n : ℝ) + 1) ≤ (((n + 1 : ℕ) : ℝ)) ^ 3
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) + 1), mul_nonneg (by linarith : (0 : ℝ) ≤ n + 1) (by linarith : (0 : ℝ) ≤ n - 1)]
  · -- `(eq:WO)`
    filter_upwards [eventually_ge_atTop 99] with n hn
    have hexp : (-((3 : ℕ) : ℝ) / 2 + 1 / 2 : ℝ) = -1 := by norm_num
    have hW : (100 : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by
      have : 100 ≤ n + 1 := by omega
      exact_mod_cast this
    show (((n + 1 : ℕ)) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 2 : ℝ) ≤ 1 / 100 ∧ (1 / 100 : ℝ) ≤ (1 / 2 : ℝ)⁻¹
    rw [hexp, Real.rpow_neg_one]
    refine ⟨?_, by norm_num⟩
    calc ((((n + 1 : ℕ)) : ℝ))⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hW
      _ = 1 / 100 := by norm_num
  · -- `BAdom` at every `n`
    refine ⟨?_, ?_, ?_⟩
    · show (9 / 10 : ℝ) ≤ (BAm 3 4 (1 / 100) (GreenSchur_wF - GreenSchur_mF0)).im
      rw [GreenSchur_Am]
      exact GreenSchur_mim_lo
    · have h64 : (64 : ℝ) ≤ ((GreenSchur_szF.size n : ℕ) : ℝ) := by
        rw [GreenSchur_size]
        have : 64 ≤ ((n + 1) * 4) ^ 3 := by
          calc 64 = 4 ^ 3 := by norm_num
            _ ≤ ((n + 1) * 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        exact_mod_cast this
      have h1 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 64) h64
        (by norm_num : (-1 + 1 / 2 : ℝ) ≤ 0)
      have h2 : (64 : ℝ) ^ (-1 + 1 / 2 : ℝ) = 1 / 8 := by
        rw [show (64 : ℝ) = 8 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      refine le_trans h1 ?_
      rw [h2]
      show 1 / 8 ≤ (GreenSchur_wF - GreenSchur_mF0).im
      rw [Complex.sub_im, GreenSchur_wF_im]
      linarith [GreenSchur_mim_hi]
    · show (GreenSchur_wF - GreenSchur_mF0).im ≤ 1
      rw [Complex.sub_im, GreenSchur_wF_im]
      linarith [GreenSchur_mim_lo]

/-- Targets 1 and 2 at the `BAFlow` instance. -/
theorem inst_flow_real (n : ℕ) :
    BAReal 3 (GreenSchur_szF.L n) (BAflowLam0 GreenSchur_szF GreenSchur_zF n) (9 / 10)
      (BAflowEs GreenSchur_szF GreenSchur_zF n)
      (BAmF GreenSchur_szF (BAflowLam0 GreenSchur_szF GreenSchur_zF) (BAflowEs GreenSchur_szF GreenSchur_zF) n) :=
  BAflow_real (9 / 10) (1 / 2) (1 / 9) (1 / 2) GreenSchur_szF GreenSchur_zF inst_BAFlow n

theorem inst_flow_window :
    ∀ᶠ n in atTop, 0 < BAflowLam0 GreenSchur_szF GreenSchur_zF n ∧
      BAflowLam0 GreenSchur_szF GreenSchur_zF n ≤ (1 / 2 : ℝ)⁻¹ :=
  BAflow_lam0_window (9 / 10) (1 / 2) (1 / 9) (1 / 2) GreenSchur_szF GreenSchur_zF inst_BAFlow

end GreenSchurInst

end RBM.BA
