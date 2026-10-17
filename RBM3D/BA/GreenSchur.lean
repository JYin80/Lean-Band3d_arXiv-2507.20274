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
# The Schur structure of the block Anderson resolvent with the deterministic hopping

Paper: Section 8 (the block Anderson extension) and Section 2.  Deterministic part of the block Anderson `G`-chain
(proof of Lemma 8.4 `lem_GbEXP_BA` and of Lemma 8.5 `lem_ConArg_BA`): no
probability, no a.s. block support, no large-deviation estimate.

* Section 1: the chain domain `BAdom` gives the real-axis bulk data at the flow parameters
  (Lemma 8.1 `zztE_BA`), every `n`; (2.10) `eq:WO` gives `0 < g₀ ≤ 𝔡⁻¹` eventually.
* Section 2: `M = M^{(B)} ⊗ I_{W^d}` entrywise ((2.33) `def_G0`), `‖M‖_max ≤ 1`, the
  `ℓ¹` rows, uniform in `L, W`.
* Section 3: `G_t - M = -M (√t V + t m) G_t = -G_t (√t V + t m) M` (`H_t = g₀ Ψ + √t V`,
  `z_t = E + (1 - t) m`, (2.36) `MBM`, (2.37) `eq:zt`).
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

/-! ## 1. The flow data on the chain domain -/

/-- `Im z_n > 0` on the chain domain (`N^{-1+ε} ≤ Im z_n`, `N ≥ 1`). -/
private theorem GreenSchur_zim_pos {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  linarith

/-- **The real-axis datum** (Lemma 8.1 `zztE_BA`): the chain domain gives real-axis bulk data at the flow parameters,
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

/-- **The coupling window** ((2.10) `eq:WO`, at the flow coupling): eventually `0 < g₀_n ≤ 𝔡⁻¹`. -/
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

/-! ## 2. `M = M^{(B)} ⊗ I_{W^d}` and its bounds -/

/-- **The Kronecker form** ((2.33) `def_G0`): `M_{xy} = 1(x, y same offset) M^{(B)}_{[x][y]}`. -/
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

/-- **`‖M‖_max ≤ 1`**: the Ward row identity at the real axis, `∑_b |M^{(B)}_{ab}|² = 1`. -/
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

/-- **The `ℓ¹` row of `M^{(B)}`**, uniform in `L`; `d = k + 2`: `∑_b |M^{(B)}_{ab}| ≤ c⁻¹ expC k c`,
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

/-! ## 3. The resolvent identity with the deterministic hopping -/

/-- The perturbation `√t V + t m`, so that `G_t⁻¹ - M⁻¹ = BAflowPert` (`H_t = g₀ Ψ + √t V`,
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

/-- **The resolvent identity** (`G_t - M = -M (√t V + t m) G_t = -G_t (√t V + t m) M`; `t < 1`, `Im m > 0`): the resolvent
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


end RBM.BA
