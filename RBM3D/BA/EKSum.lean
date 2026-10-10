/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.EKPins
import RBM3D.Evolution.SumDecay

/-!
# Stage E of the block Anderson model (BA-E2): `(sum_res_1)`, `(sum_res_2_NAL)`, `(sum_res_2)`

Ticket T2392.  Paper: `A_deterministic_estimates.tex:111-198` (`(eq:decomp_U2)`, `(sum_res_deriv_red)`,
`(sum_res_2_red)`, `(eq:latticesum_d3)`), `3_5_Loop_Hierarchy.tex:1630-1665`; design
`docs/reports/T2378-design.md` §3.  Band blueprints: `Evolution/SumDecay.lean:253-518`,
`Evolution/SumDecayZero.lean:44-1520` (every `ekSZ_*` there is private, so the generic parts are copied here).

1. `baEKSumDecay1_holds`, `baEKSumDecayNAL_holds`: the anchored window/tail split of `ek_core_bound` with the one-index
   kernel `BAuKer = 1 + BAXi` (`BAuKer_eq_one_add_Xi`), the ball sums `baEKXiBall_holds`, the row sums
   `‖BAuKer‖_{∞→∞} ≤ (1-s)/(1-t)` and, at a same-sign anchor, `baEKSameRow_holds`.  No smallness of `g` or of
   `‖M - m₀ I‖`, no `‖m‖ = 1`: only `BAReal`.
2. `baEKSumDecay2_holds`: the abstract combinatorics (Part I, copied from the band), the lattice estimates with
   the first difference of `Ξ` from `baProp6_holds` through `Ξ = ((t-s)/t)(Θ_t - 1)` (no nearest-neighbour `S^{(B)}`),
   the constants (Part III, copied), the pin.
3. Compiled nonempty instances at `d = 3`, the flow datum `n = 0` of `sz0` (`EKPinsInst`).

Private helpers carry the stem `EKSum_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

noncomputable section

open RBM

namespace RBM.BA

/-! ## 1. The row bounds of the one-index kernel (copies of the private `EKPins_norm_*`, `EKPins.lean:149-208`) -/

section Norms

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- `‖M^{(σ₁σ₂)}‖_{∞→∞} ≤ 1` (`(eq:WardM)`): `BAMss_norm_eq_BAK`, `BAK_row_sum`. -/
private theorem EKSum_norm_Q_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) :
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖ ≤ 1 := by
  have h : ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa [BAMss_norm_eq_BAK] using (BAK_row_sum d L g E m hr.1 a).le
  exact_mod_cast h

/-- `(eq:THETAinftinf)`: `‖Θ_t‖_{∞→∞} ≤ 1/(1 - t)`. -/
private theorem EKSum_norm_Theta_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) : ‖BATheta d L g E m t σ₁ σ₂‖ ≤ (1 - t)⁻¹ := by
  have h := (BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂).1
  have hQ := EKSum_norm_Q_le hr σ₁ σ₂
  set Θ := BATheta d L g E m t σ₁ σ₂
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂
  have h1 : ‖Θ‖ ≤ 1 + t * ‖Θ‖ := by
    calc ‖Θ‖ = ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) + (t : ℂ) • (Q * Θ)‖ := by rw [← h]
      _ ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖ + ‖(t : ℂ) • (Q * Θ)‖ := norm_add_le _ _
      _ ≤ 1 + t * ‖Θ‖ := by
          rw [norm_one]
          refine add_le_add le_rfl ?_
          calc ‖(t : ℂ) • (Q * Θ)‖ ≤ ‖(t : ℂ)‖ * ‖Q * Θ‖ := norm_smul_le _ _
            _ ≤ t * (‖Q‖ * ‖Θ‖) := by
                rw [Complex.norm_real, Real.norm_of_nonneg ht0]
                exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) ht0
            _ ≤ t * (1 * ‖Θ‖) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ (norm_nonneg _)) ht0
            _ = t * ‖Θ‖ := by rw [one_mul]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

/-- `(Xi_infint)`: `‖Ξ‖_{∞→∞} ≤ (t - s)/(1 - t)`. -/
private theorem EKSum_norm_Xi_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (σ₁ σ₂ : Bool) :
    ‖BAXi d L g E m s t σ₁ σ₂‖ ≤ (t - s) / (1 - t) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have h1t : 0 < 1 - t := by linarith
  have hQ := EKSum_norm_Q_le hr σ₁ σ₂
  have hΘ := EKSum_norm_Theta_le hr ht0 ht σ₁ σ₂
  have hc : ‖(t : ℂ) - s‖ = t - s := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  unfold BAXi
  calc ‖((t : ℂ) - s) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂)‖
      ≤ ‖(t : ℂ) - s‖ * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂‖ :=
        norm_smul_le _ _
    _ ≤ (t - s) * (‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖ * ‖BATheta d L g E m t σ₁ σ₂‖) := by
        rw [hc]; exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by linarith)
    _ ≤ (t - s) * (1 * (1 - t)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hQ hΘ (norm_nonneg _) zero_le_one) (by linarith)
    _ = (t - s) / (1 - t) := by rw [one_mul, div_eq_mul_inv]

/-- Each one-index factor `(1 - s M) Θ_t = 1 + Ξ` has `(∞→∞)`-norm at most `(1 - s)/(1 - t)`. -/
private theorem EKSum_norm_uKer_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (σ₁ σ₂ : Bool) :
    ‖BAuKer d L g E m s t σ₁ σ₂‖ ≤ (1 - s) / (1 - t) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have h1t : 0 < 1 - t := by linarith
  rw [BAuKer_eq_one_add_Xi hr ht0 ht σ₁ σ₂]
  calc ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) + BAXi d L g E m s t σ₁ σ₂‖
      ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖ + ‖BAXi d L g E m s t σ₁ σ₂‖ := norm_add_le _ _
    _ ≤ 1 + (t - s) / (1 - t) := by
        rw [norm_one]; exact add_le_add le_rfl (EKSum_norm_Xi_le hr hs hst ht σ₁ σ₂)
    _ = (1 - s) / (1 - t) := by field_simp; ring

end Norms

/-! ## 2. The anchored bound for `U^{(n)}` at BA (twin of `ek_UN_anchor_bound`, `SumDecay.lean:253`) -/

section Anchored

open scoped Matrix.Norms.Operator

/-- The bound of `U^{(n)}_{s,t,σ} ∘ A` at a point `a` from the window sums of `Ξ`: with anchor `k`, anchor row sum `Rk`,
`ρ = W^ε`, `r = (g²+|1-s|)/(g²+|1-t|)`, `P = (1-s)/(1-t)`,
`‖BAUN A a‖ ≤ ‖A‖ Rk (1 + C_X ρ² r)^{n-1} + W^{-D} Rk P^{n-1}`.  The ball sums of `Ξ` enter as the hypothesis `hX`
(`baEKXiBall_holds`); the factor `i` is `BAuKer (σ i) (σ (i+1))`, no scalar `μ`. -/
private theorem EKSum_UN_anchor_bound {d L n : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}
    (hr : BAReal d L g κ E m) (hL : 3 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {W ε D : ℝ}
    (hρ : 1 ≤ W ^ ε) (σ : Fin n → Bool) (A : (Fin n → Zd d L) → ℂ)
    (hA : EKFastDecay g s W ε D A) (hD : 0 ≤ W ^ (-D)) (k : Fin n) {CX Rk : ℝ} (hCX : 0 ≤ CX)
    (hX : ∀ σ₁ σ₂ : Bool, ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
      ∀ (a ctr : Zd d L) (D : Finset (Zd d L)), (∀ b ∈ D, (zdistD d L (ctr - b) : ℝ) ≤ R) →
        ∑ b ∈ D, ‖BAXi d L g E m s t σ₁ σ₂ a b‖
          ≤ CX * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)))
    (a : Fin n → Zd d L)
    (hRk : ∑ y, ‖BAuKer d L g E m s t (σ k) (σ (finRotate n k)) (a k) y‖ ≤ Rk) :
    ‖BAUN d L g E m σ s t A a‖ ≤
      ‖A‖ * (Rk * (1 + CX * (W ^ ε) ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))) ^ (n - 1))
        + W ^ (-D) * (Rk * ((1 - s) / (1 - t)) ^ (n - 1)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have ht0 : 0 ≤ t := hs.trans hst
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  set r : ℝ := (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) with hrdef
  have hr0 : 0 ≤ r := by positivity
  set ρ : ℝ := W ^ ε with hρdef
  have hℓs : 1 ≤ ellT L g s := one_le_ellT hL1
  set R : ℝ := ρ * ellT L g s with hR
  have hR1 : 1 ≤ R := by nlinarith
  have hS0 : 0 ≤ 1 + CX * ρ ^ 2 * r := by positivity
  -- window sums of the one-index kernels
  have hwin : ∀ (i : Fin n) (x ctr : Zd d L) (F : Finset (Zd d L)),
      (∀ b ∈ F, ((zdistD d L (ctr - b) : ℕ) : ℝ) ≤ R) →
      ∑ y ∈ F, ‖BAuKer d L g E m s t (σ i) (σ (finRotate n i)) x y‖ ≤ 1 + CX * ρ ^ 2 * r := by
    intro i x ctr F hF
    have hdec : ∀ y, ‖BAuKer d L g E m s t (σ i) (σ (finRotate n i)) x y‖
        ≤ (if x = y then (1 : ℝ) else 0) + ‖BAXi d L g E m s t (σ i) (σ (finRotate n i)) x y‖ := by
      intro y
      rw [BAuKer_eq_one_add_Xi hr ht0 ht, Matrix.add_apply, Matrix.one_apply]
      refine (norm_add_le _ _).trans ?_
      by_cases h : x = y <;> simp [h]
    have h1 : ∑ y ∈ F, (if x = y then (1 : ℝ) else 0) ≤ 1 := by
      rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
    have h2 := hX (σ i) (σ (finRotate n i)) ρ hρ R hR1 le_rfl x ctr F hF
    calc ∑ y ∈ F, ‖BAuKer d L g E m s t (σ i) (σ (finRotate n i)) x y‖
        ≤ ∑ y ∈ F, ((if x = y then (1 : ℝ) else 0)
            + ‖BAXi d L g E m s t (σ i) (σ (finRotate n i)) x y‖) :=
          Finset.sum_le_sum fun y _ => hdec y
      _ = ∑ y ∈ F, (if x = y then (1 : ℝ) else 0)
            + ∑ y ∈ F, ‖BAXi d L g E m s t (σ i) (σ (finRotate n i)) x y‖ :=
          Finset.sum_add_distrib
      _ ≤ 1 + CX * ρ ^ 2 * r := by linarith
  have hrow : ∀ i : Fin n, ∑ y, ‖BAuKer d L g E m s t (σ i) (σ (finRotate n i)) (a i) y‖
      ≤ (1 - s) / (1 - t) := fun i =>
    (sum_norm_row_le _ (a i)).trans (EKSum_norm_uKer_le hr hs hst ht _ _)
  refine le_trans (ek_core_bound (X := Zd d L) k (fun x y => (zdistD d L (x - y) : ℝ) < R)
    (fun i y => BAuKer d L g E m s t (σ i) (σ (finRotate n i)) (a i) y) A (M := ‖A‖) (δ := W ^ (-D))
    (norm_nonneg _) hD (fun b => norm_le_pi_norm A b) ?_ hS0 ?_ (fun i _ => hrow i) hRk) le_rfl
  · intro b hb
    push Not at hb
    obtain ⟨i, hik, hi⟩ := hb
    exact hA b ⟨k, i, hi⟩
  · intro i hik x
    refine hwin i (a i) x _ ?_
    intro b hb
    exact le_of_lt (Finset.mem_filter.mp hb).2

end Anchored

/-! ## 3. The pins `(sum_res_1)` and `(sum_res_2_NAL)` -/

section Pins12

open scoped Matrix.Norms.Operator

/-- **`(sum_res_1)` of `lem:sum_decay` at BA** (`A:111-153`), every `n ≥ 2`, `d ≥ 3`, uniform in `g ∈ (0, Λ]`.  The constant
is `C = m' + 2n` with `m'` least with `2 (1 + C_X)^{n-1} < 4^{m'}`, `C_X` the constant of `baEKXiBall_holds`. -/
theorem baEKSumDecay1_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecay1 d n Λ κ := by
  intro hd hn hΛ hκ
  obtain ⟨CX, hCX, hX⟩ := baEKXiBall_holds d Λ κ hd hΛ hκ
  obtain ⟨m', hm'⟩ := pow_unbounded_of_one_lt (2 * (1 + CX) ^ (n - 1)) (by norm_num : (1 : ℝ) < 4)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
  refine ⟨(m' : ℝ) + 2 * n, by linarith, ?_⟩
  intro L hL g hg hgΛ W ε D hW1 hε0 hε1 hD hρ s t hs hst ht hWt E m hr σ A hA
  have : NeZero L := ⟨by omega⟩
  have hW0 : 0 < W := by linarith
  have hLge : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t := by linarith
  have hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) := by
    rw [div_le_iff₀ hL0] at hgt; linarith
  have ht1 : t < 1 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
    linarith
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  set r : ℝ := (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) with hrdef
  set q : ℝ := ellT L g t ^ 2 / ellT L g s ^ 2 with hq
  set P : ℝ := (1 - s) / (1 - t) with hP
  set ρ : ℝ := W ^ ε with hρdef
  have hρ4 : 4 ≤ ρ := hρ
  have hℓs : 1 ≤ ellT L g s := one_le_ellT hLge
  have hℓt : ellT L g s ≤ ellT L g t := ellT_mono hg.le hst ht1
  have hℓs0 : 0 < ellT L g s := by linarith
  have hr1 : 1 ≤ r := by
    rw [hrdef, abs_of_pos hu, abs_of_pos hv, le_div_iff₀ (by positivity)]
    linarith
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ (by positivity)]
    have := pow_le_pow_left₀ hℓs0.le hℓt 2
    linarith
  have hP0 : 0 ≤ P := div_nonneg hv.le hu.le
  have hPW : P ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hP2 : P ≤ 2 * q * r := ek_ratio_le hLge hg.le hst ht1 hgL
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  have hW1' : (1 : ℝ) ≤ W := hW1.le
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- the absorption of the constants into `W^{Cε}`
  have habs1 : ρ ^ (m' + 2 * (n - 1)) ≤ W ^ (((m' : ℝ) + 2 * n) * ε) := by
    have h1 : ρ ^ (m' + 2 * (n - 1)) = W ^ (ε * ((m' + 2 * (n - 1) : ℕ) : ℝ)) := by
      rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    rw [h1]
    refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
    push_cast
    rw [hcast]
    nlinarith
  have habs2 : W ^ (-D) * W ^ n ≤ W ^ (-D + ((m' : ℝ) + 2 * n)) := by
    have h1 : W ^ n ≤ W ^ ((m' : ℝ) + 2 * n) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
    calc W ^ (-D) * W ^ n ≤ W ^ (-D) * W ^ ((m' : ℝ) + 2 * n) :=
          mul_le_mul_of_nonneg_left h1 hWD
      _ = W ^ (-D + ((m' : ℝ) + 2 * n)) := (Real.rpow_add hW0 _ _).symm
  have hq0 : 0 ≤ q := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hpos : 0 ≤ W ^ (((m' : ℝ) + 2 * n) * ε) * q * r ^ n * ‖A‖ + W ^ (-D + ((m' : ℝ) + 2 * n)) := by
    positivity
  refine (pi_norm_le_iff_of_nonneg hpos).mpr fun a => ?_
  have hcore := EKSum_UN_anchor_bound (d := d) (n := n) hr hL hs hst ht1 (by linarith : 1 ≤ ρ) σ A
    hA hWD ⟨0, by omega⟩ (CX := CX) (Rk := P) hCX.le
    (fun σ₁ σ₂ Λ' hΛ' R hR hRℓ a ctr F hF =>
      hX L hL g hg hgΛ E m hr s t hs hst ht1 hgt σ₁ σ₂ Λ' hΛ' R hR hRℓ a ctr F hF)
    a ((sum_norm_row_le _ (a _)).trans (EKSum_norm_uKer_le hr hs hst ht1 _ _))
  have hclaim : P * (1 + CX * ρ ^ 2 * r) ^ (n - 1) ≤ ρ ^ (m' + 2 * (n - 1)) * q * r ^ n := by
    have := ek_arith_res1 hCX.le hρ4 hq1 hr1 hP2 hm'
    rwa [hn1] at this
  have hPP : P * P ^ (n - 1) ≤ W ^ n := by
    rw [← pow_succ', hn1]
    exact pow_le_pow_left₀ hP0 hPW n
  calc ‖BAUN d L g E m σ s t A a‖
      ≤ ‖A‖ * (P * (1 + CX * ρ ^ 2 * r) ^ (n - 1)) + W ^ (-D) * (P * P ^ (n - 1)) := hcore
    _ ≤ ‖A‖ * (ρ ^ (m' + 2 * (n - 1)) * q * r ^ n) + W ^ (-D) * W ^ n := by
        gcongr
    _ ≤ ‖A‖ * (W ^ (((m' : ℝ) + 2 * n) * ε) * q * r ^ n) + W ^ (-D + ((m' : ℝ) + 2 * n)) := by
        gcongr
    _ = W ^ (((m' : ℝ) + 2 * n) * ε) * q * r ^ n * ‖A‖ + W ^ (-D + ((m' : ℝ) + 2 * n)) := by ring

/-- **`(sum_res_2_NAL)` of `lem:sum_decay` at BA** (`A:154-158`), every `n ≥ 2`, `d ≥ 3`.  The anchor is an index `k` with
`σ_k = σ_{k+1}`, whose one-index row sum is bounded by `C_s` of `baEKSameRow_holds` instead of `P`.  The constant is
`C = m'' + 2n - 2` with `m''` least with `C_s (1 + C_X)^{n-1} < 4^{m''}`. -/
theorem baEKSumDecayNAL_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecayNAL d n Λ κ := by
  intro hd hn hΛ hκ
  obtain ⟨CX, hCX, hX⟩ := baEKXiBall_holds d Λ κ hd hΛ hκ
  obtain ⟨Cs, hCs, hS⟩ := baEKSameRow_holds d Λ κ hd hΛ hκ
  obtain ⟨m', hm'⟩ := pow_unbounded_of_one_lt (Cs * (1 + CX) ^ (n - 1)) (by norm_num : (1 : ℝ) < 4)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
  refine ⟨(m' : ℝ) + 2 * n - 2, by linarith, ?_⟩
  intro L hL g hg hgΛ W ε D hW1 hε0 hε1 hD hρ s t hs hst ht hWt E m hr σ hσ A hA
  obtain ⟨k, hk⟩ := hσ
  have : NeZero L := ⟨by omega⟩
  have hW0 : 0 < W := by linarith
  have hLge : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t := by linarith
  have ht1 : t < 1 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
    linarith
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  set r : ℝ := (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) with hrdef
  set P : ℝ := (1 - s) / (1 - t) with hP
  set ρ : ℝ := W ^ ε with hρdef
  have hρ4 : 4 ≤ ρ := hρ
  have hr1 : 1 ≤ r := by
    rw [hrdef, abs_of_pos hu, abs_of_pos hv, le_div_iff₀ (by positivity)]
    linarith
  have hP0 : 0 ≤ P := div_nonneg hv.le hu.le
  have hPW : P ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hW4 : 4 ≤ W := by
    have h1 : W ^ ε ≤ W ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1.le hε1.le
    rw [Real.rpow_one] at h1
    linarith
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hW1' : (1 : ℝ) ≤ W := hW1.le
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hr0 : 0 ≤ r := by linarith
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  -- the one-index factor at the anchor `k`: same sign
  have hrowk : ∀ a : Fin n → Zd d L,
      ∑ y, ‖BAuKer d L g E m s t (σ k) (σ (finRotate n k)) (a k) y‖ ≤ Cs := by
    intro a
    refine (sum_norm_row_le _ (a k)).trans ?_
    rw [← hk]
    exact hS L hL g hg hgΛ E m hr (σ k) s t hs hst ht1
  -- the absorption of the constants into `W^{Cε}`
  have habs1 : ρ ^ (m' + 2 * (n - 1)) ≤ W ^ (((m' : ℝ) + 2 * n - 2) * ε) := by
    have h1 : ρ ^ (m' + 2 * (n - 1)) = W ^ (ε * ((m' + 2 * (n - 1) : ℕ) : ℝ)) := by
      rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    rw [h1]
    refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
    push_cast
    rw [hcast]
    nlinarith
  have hCs4 : Cs ≤ W ^ m' := by
    have h1 : (1 : ℝ) ≤ (1 + CX) ^ (n - 1) := one_le_pow₀ (by linarith)
    have h2 : Cs ≤ Cs * (1 + CX) ^ (n - 1) := by nlinarith
    exact (h2.trans hm'.le).trans (pow_le_pow_left₀ (by norm_num) hW4 m')
  have habs2 : W ^ (-D) * (Cs * W ^ (n - 1)) ≤ W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by
    have h1 : W ^ m' * W ^ (n - 1) ≤ W ^ ((m' : ℝ) + 2 * n - 2) := by
      rw [← pow_add, ← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
      push_cast
      rw [hcast]
      linarith
    calc W ^ (-D) * (Cs * W ^ (n - 1)) ≤ W ^ (-D) * (W ^ m' * W ^ (n - 1)) := by
          gcongr
      _ ≤ W ^ (-D) * W ^ ((m' : ℝ) + 2 * n - 2) := mul_le_mul_of_nonneg_left h1 hWD
      _ = W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := (Real.rpow_add hW0 _ _).symm
  have hpos : 0 ≤ W ^ (((m' : ℝ) + 2 * n - 2) * ε) * r ^ (n - 1) * ‖A‖
      + W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by
    positivity
  refine (pi_norm_le_iff_of_nonneg hpos).mpr fun a => ?_
  have hcore := EKSum_UN_anchor_bound (d := d) (n := n) hr hL hs hst ht1 (by linarith : 1 ≤ ρ) σ A
    hA hWD k (CX := CX) (Rk := Cs) hCX.le
    (fun σ₁ σ₂ Λ' hΛ' R hR hRℓ a ctr F hF =>
      hX L hL g hg hgΛ E m hr s t hs hst ht1 hgt σ₁ σ₂ Λ' hΛ' R hR hRℓ a ctr F hF)
    a (hrowk a)
  have hclaim : Cs * (1 + CX * ρ ^ 2 * r) ^ (n - 1) ≤ ρ ^ (m' + 2 * (n - 1)) * r ^ (n - 1) :=
    ek_arith_nal hCX.le hCs.le hρ4 hr1 hm'
  have hPP : P ^ (n - 1) ≤ W ^ (n - 1) := pow_le_pow_left₀ hP0 hPW _
  calc ‖BAUN d L g E m σ s t A a‖
      ≤ ‖A‖ * (Cs * (1 + CX * ρ ^ 2 * r) ^ (n - 1)) + W ^ (-D) * (Cs * P ^ (n - 1)) := hcore
    _ ≤ ‖A‖ * (ρ ^ (m' + 2 * (n - 1)) * r ^ (n - 1)) + W ^ (-D) * (Cs * W ^ (n - 1)) := by
        gcongr
    _ ≤ ‖A‖ * (W ^ (((m' : ℝ) + 2 * n - 2) * ε) * r ^ (n - 1))
          + W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by
        gcongr
    _ = W ^ (((m' : ℝ) + 2 * n - 2) * ε) * r ^ (n - 1) * ‖A‖
          + W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by ring

end Pins12

/-! ## 4. Part I: the combinatorics over an arbitrary finite type (copy of `Evolution/SumDecayZero.lean:44-601`, `ekSZ_` renamed `EKSum_`; the band helpers are private) -/

section Core

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- the one-index kernel row `u_i(a_i, ·) = δ_{a_i ·} + Ξ_i(a_i, ·)` of `(eq:decompUalt)`. -/
private noncomputable def EKSum_U (Ξ : Fin n → X → X → ℂ) (a : Fin n → X) (i : Fin n) (y : X) : ℂ :=
  (if a i = y then 1 else 0) + Ξ i (a i) y

omit [Fintype X] in
/-- a row of `u` over a finite set is at most `1` plus the row of `Ξ`. -/
private theorem EKSum_u_sum_le (Ξ : Fin n → X → X → ℂ) (a : Fin n → X) (i : Fin n) (E : Finset X) :
    ∑ y ∈ E, ‖EKSum_U Ξ a i y‖ ≤ 1 + ∑ y ∈ E, ‖Ξ i (a i) y‖ := by
  have h1 : ∀ y ∈ E, ‖EKSum_U Ξ a i y‖ ≤ (if a i = y then (1 : ℝ) else 0) + ‖Ξ i (a i) y‖ := by
    intro y _
    refine (norm_add_le _ _).trans ?_
    by_cases h : a i = y <;> simp [h]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib]
  have h2 : ∑ y ∈ E, (if a i = y then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
  linarith

/-- the number of `b : Fin n → X` with `b k = x` is `|X|^{n-1}`. -/
private theorem EKSum_fiber_card (k : Fin n) (x : X) :
    (Finset.univ.filter (fun b : Fin n → X => b k = x)).card = Fintype.card X ^ (n - 1) := by
  classical
  have h : Finset.univ.filter (fun b : Fin n → X => b k = x)
      = Fintype.piFinset (fun i => if i = k then ({x} : Finset X) else Finset.univ) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hb i
      by_cases hi : i = k
      · subst hi; simp [hb]
      · simp [hi]
    · intro h
      have := h k
      simpa using this
  rw [h, Fintype.card_piFinset]
  have h2 : ∀ i : Fin n, (if i = k then ({x} : Finset X) else Finset.univ).card
      = if i = k then 1 else Fintype.card X := by
    intro i; by_cases hi : i = k <;> simp [hi]
  simp only [h2]
  have h3 : ∏ i : Fin n, (if i = k then 1 else Fintype.card X) = Fintype.card X ^ (n - 1) := by
    rw [← Finset.prod_erase Finset.univ (f := fun i : Fin n => if i = k then 1 else Fintype.card X)
      (a := k) (by simp)]
    rw [Finset.prod_congr rfl (g := fun _ => Fintype.card X)
      (fun i hi => by simp [Finset.ne_of_mem_erase hi]), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  exact h3

/-- **Anchored sum with anchor-dependent kernels** (equality): over the window
`{b : ∀ i ≠ k, b_i ∈ Win(b_k)}` the sum of `F(b_k) ∏_{i≠k} h_i(b_k, b_i)` is
`Σ_x F(x) ∏_{i≠k} Σ_{y ∈ Win(x)} h_i(x, y)`. -/
private theorem EKSum_anchor_dep (k : Fin n) (Win : X → Finset X) (F : X → ℝ)
    (h : Fin n → X → X → ℝ) :
    ∑ b : Fin n → X, (if ∀ i, i ≠ k → b i ∈ Win (b k) then
        F (b k) * ∏ i ∈ Finset.univ.erase k, h i (b k) (b i) else 0)
      = ∑ x : X, F x * ∏ i ∈ Finset.univ.erase k, ∑ y ∈ Win x, h i x y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin n → X => b k)]
  refine Finset.sum_congr rfl fun x _ => ?_
  set T : ∀ _ : Fin n, Finset X := fun i => if i = k then {x} else Win x with hT
  rw [← Finset.sum_filter, Finset.filter_filter]
  have hset : Finset.univ.filter (fun b : Fin n → X =>
      b k = x ∧ ∀ i, i ≠ k → b i ∈ Win (b k)) = Fintype.piFinset T := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hT]
    constructor
    · rintro ⟨hb, hW⟩ i
      by_cases hi : i = k
      · subst hi; simp [hb]
      · simp only [hi, ite_false]; rw [← hb]; exact hW i hi
    · intro h
      have hk : b k = x := by simpa using h k
      refine ⟨hk, fun i hi => ?_⟩
      have := h i
      simp only [hi, ite_false] at this
      rwa [hk]
  rw [hset]
  have h2 : ∀ b ∈ Fintype.piFinset T, F (b k) * ∏ i ∈ Finset.univ.erase k, h i (b k) (b i)
      = F x * ∏ i ∈ Finset.univ.erase k, h i x (b i) := by
    intro b hb
    have hk : b k = x := by
      have := Fintype.mem_piFinset.mp hb k
      simpa [hT] using this
    rw [hk]
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  congr 1
  set g : Fin n → X → ℝ := fun i y => if i = k then 1 else h i x y with hg
  have h3 : ∀ b : Fin n → X, ∏ i ∈ Finset.univ.erase k, h i x (b i) = ∏ i, g i (b i) := by
    intro b
    rw [← Finset.prod_erase Finset.univ (f := fun i => g i (b i)) (a := k) (by simp [hg])]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [hg, Finset.ne_of_mem_erase hi]
  rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.prod_univ_sum]
  rw [← Finset.prod_erase Finset.univ
    (f := fun i => ∑ y ∈ T i, g i y) (a := k) (by simp [hT, hg])]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp [hT, hg, Finset.ne_of_mem_erase hi]


/-- **The `δ + near` part**: with a row `w` at the index `i₀` (row-sum `≤ Rk`) and the one-index
kernels `u_i(a_i, ·)` at the other indices, `ek_core_bound` gives
`M Rk (1+Sξ)^{n-1} + δ Rk (1+Q)^{n-1}`. -/
private theorem EKSum_UW_bound (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) {M δ Q Sξ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 ≤ δ)
    (hSξ0 : 0 ≤ Sξ) (hM : ∀ b, ‖A b‖ ≤ M)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hrow : ∀ i x, ∑ y, ‖Ξ i x y‖ ≤ Q)
    (hwin : ∀ i, i ≠ i₀ → ∀ x, ∑ y ∈ Win x, ‖Ξ i (a i) y‖ ≤ Sξ)
    (w : X → ℂ) {Rk : ℝ} (hw : ∑ x, ‖w x‖ ≤ Rk) :
    ‖∑ b : Fin n → X, ((w (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b‖
      ≤ M * (Rk * (1 + Sξ) ^ (n - 1)) + δ * (Rk * (1 + Q) ^ (n - 1)) := by
  classical
  set κ : Fin n → X → ℂ := fun i y => if i = i₀ then w y else EKSum_U Ξ a i y with hκ
  have hprod : ∀ b : Fin n → X, ∏ i, κ i (b i)
      = (w (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i) := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ (fun i => κ i (b i)) (Finset.mem_univ i₀)]
    congr 1
    · simp [hκ]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [hκ, Finset.ne_of_mem_erase hi]
  have hbound := ek_core_bound (X := X) i₀ (fun x y => y ∈ Win x) κ A (M := M) (δ := δ)
    (S := 1 + Sξ) (P := 1 + Q) (Rk := Rk) hM0 hδ hM htail (by linarith) ?_ ?_ ?_
  · simpa only [hprod] using hbound
  · intro i hi x
    have hfilt : Finset.univ.filter (fun y => y ∈ Win x) = Win x := by
      ext y; simp
    rw [hfilt]
    have : ∀ y, κ i y = EKSum_U Ξ a i y := fun y => by simp [hκ, hi]
    simp only [this]
    exact (EKSum_u_sum_le Ξ a i (Win x)).trans (by linarith [hwin i hi x])
  · intro i hi
    have : ∀ y, κ i y = EKSum_U Ξ a i y := fun y => by simp [hκ, hi]
    simp only [this]
    exact (EKSum_u_sum_le Ξ a i Finset.univ).trans (by linarith [hrow i (a i)])
  · simpa [hκ] using hw


/-- **The tail part**: off the window `|A_b| ≤ δ`, and the product of the rows is summable. -/
private theorem EKSum_tail_bound (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) (wf : X → ℂ) {δ Q Rk : ℝ} (hδ : 0 ≤ δ)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hrow : ∀ i x, ∑ y, ‖Ξ i x y‖ ≤ Q) (hw : ∑ x, ‖wf x‖ ≤ Rk) :
    ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
        ((wf (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b)‖
      ≤ δ * (Rk * (1 + Q) ^ (n - 1)) := by
  classical
  set K : Fin n → X → ℝ := fun i y => if i = i₀ then ‖wf y‖ else ‖EKSum_U Ξ a i y‖ with hK
  have hK0 : ∀ i x, 0 ≤ K i x := fun i x => by
    simp only [hK]; split_ifs <;> exact norm_nonneg _
  have hprod : ∀ b : Fin n → X, ∏ i, K i (b i)
      = ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖EKSum_U Ξ a i (b i)‖ := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ (fun i => K i (b i)) (Finset.mem_univ i₀)]
    congr 1
    · simp [hK]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [hK, Finset.ne_of_mem_erase hi]
  have hsum := ek_prod_sum_le i₀ K hK0 (P := 1 + Q) (Rk := Rk) ?_ ?_
  · calc ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
          ((wf (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b)‖
        ≤ ∑ b : Fin n → X, ‖(if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
          ((wf (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b)‖ := norm_sum_le _ _
      _ ≤ ∑ b : Fin n → X, δ * ∏ i, K i (b i) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [hprod b]
          have hp0 : 0 ≤ ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖EKSum_U Ξ a i (b i)‖ :=
            mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
          split_ifs with hwb
          · simpa using mul_nonneg hδ hp0
          · rw [norm_mul, norm_mul, norm_prod]
            have := htail b hwb
            have hp1 : 0 ≤ ∏ i ∈ Finset.univ.erase i₀, ‖EKSum_U Ξ a i (b i)‖ :=
              Finset.prod_nonneg fun i _ => norm_nonneg _
            calc ‖wf (b i₀)‖ * (∏ i ∈ Finset.univ.erase i₀, ‖EKSum_U Ξ a i (b i)‖) * ‖A b‖
                ≤ ‖wf (b i₀)‖ * (∏ i ∈ Finset.univ.erase i₀, ‖EKSum_U Ξ a i (b i)‖) * δ :=
                  mul_le_mul_of_nonneg_left this hp0
              _ = δ * (‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖EKSum_U Ξ a i (b i)‖) := by ring
      _ = δ * ∑ b : Fin n → X, ∏ i, K i (b i) := by rw [Finset.mul_sum]
      _ ≤ δ * (Rk * (1 + Q) ^ (n - 1)) := mul_le_mul_of_nonneg_left hsum hδ
  · intro i hi
    have : ∀ y, K i y = ‖EKSum_U Ξ a i y‖ := fun y => by simp [hK, hi]
    simp only [this]
    exact (EKSum_u_sum_le Ξ a i Finset.univ).trans (by linarith [hrow i (a i)])
  · simpa [hK] using hw

/-- **The leading term**: the window part of a function of `b_{i₀}` alone is, by `(sumAzero)`,
minus the off-window part, which is at most `δ` per point (the paper's `W^{-D+n}`, here with the
count `|X|^{n-1}` of the complement). -/
private theorem EKSum_fempty_bound (i₀ : Fin n) (A : (Fin n → X) → ℂ) (Win : X → Finset X)
    (c : X → ℂ) {δ Cc : ℝ} (hδ : 0 ≤ δ)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hsz : ∀ x, ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), A b = 0)
    (hc : ∑ x, ‖c x‖ ≤ Cc) :
    ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖
      ≤ δ * (Cc * (Fintype.card X) ^ (n - 1)) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin n → X => b i₀)]
  have hx : ∀ x : X, ‖∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
      (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖
      ≤ ‖c x‖ * (δ * (Fintype.card X) ^ (n - 1)) := by
    intro x
    have h1 : ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)
        = c x * ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then A b else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hbx : b i₀ = x := (Finset.mem_filter.mp hb).2
      rw [hbx]
      split_ifs <;> simp
    have h2 : ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then A b else 0)
        = - ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else A b) := by
      have h := hsz x
      have h3 : ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), A b
          = ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
              (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then A b else 0)
            + ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
              (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else A b) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      rw [h3] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [h1, h2, norm_mul, norm_neg]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else A b)‖
        ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), δ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          split_ifs with hwb
          · simpa using hδ
          · exact htail b hwb
      _ = δ * (Fintype.card X) ^ (n - 1) := by
          rw [Finset.sum_const, EKSum_fiber_card, nsmul_eq_mul]
          push_cast; ring
  calc ‖∑ x : X, ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖
      ≤ ∑ x : X, ‖∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x),
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then c (b i₀) * A b else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ x : X, ‖c x‖ * (δ * (Fintype.card X) ^ (n - 1)) := Finset.sum_le_sum fun x _ => hx x
    _ = (∑ x : X, ‖c x‖) * (δ * (Fintype.card X) ^ (n - 1)) := (Finset.sum_mul _ _ _).symm
    _ ≤ Cc * (δ * (Fintype.card X) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = δ * (Cc * (Fintype.card X) ^ (n - 1)) := by ring


/-- `∏_{i ∈ S} (if i ∈ B then f i else g i) = ∏_{i ∈ B} f i * ∏_{i ∈ S \ B} g i` for `B ⊆ S`. -/
private theorem EKSum_prod_ite_subset {ι : Type*} [DecidableEq ι] {S B : Finset ι} (hB : B ⊆ S)
    (f g : ι → ℝ) :
    ∏ i ∈ S, (if i ∈ B then f i else g i) = (∏ i ∈ B, f i) * ∏ i ∈ S \ B, g i := by
  rw [Finset.prod_ite]
  congr 2
  · ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hB h, h⟩⟩
  · ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff]

/-- **A term of the first-difference expansion with a non-empty set `B` of differenced indices**:
the sum over the window of `w_far(b_{i₀}) ∏_{i∈B} Δ_i ∏_{i∉B} X_i A_b` is at most
`M Snon^{n-2} Ψ`, where `Ψ` bounds the lattice sum of the distinguished index `j ∈ B`. -/
private theorem EKSum_fB_bound (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) (far : X → Prop) [DecidablePred far]
    (wf : X → ℂ) (hwf : ∀ x, ‖wf x‖ = if far x then ‖Ξ i₀ (a i₀) x‖ else 0)
    {M Snon Ψ : ℝ} (hM0 : 0 ≤ M) (hSnon0 : 0 ≤ Snon) (hM : ∀ b, ‖A b‖ ≤ M)
    (hX : ∀ x, far x → ∀ i, i ≠ i₀ → ((Win x).card : ℝ) * ‖Ξ i (a i) x‖ ≤ Snon)
    (hΔ : ∀ x, far x → ∀ i, i ≠ i₀ → ∑ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖ ≤ Snon)
    (hΨ : ∀ j, j ≠ i₀ → ∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
        ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ ≤ Ψ)
    (B : Finset (Fin n)) (hBS : B ⊆ Finset.univ.erase i₀) (hBne : B.Nonempty) :
    ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ M * (Snon ^ (n - 2) * Ψ) := by
  classical
  obtain ⟨j, hjB⟩ := hBne
  have hjS : j ∈ Finset.univ.erase i₀ := hBS hjB
  have hji : j ≠ i₀ := Finset.ne_of_mem_erase hjS
  set h : Fin n → X → X → ℝ := fun i x y =>
    if i ∈ B then ‖Ξ i (a i) y - Ξ i (a i) x‖ else ‖Ξ i (a i) x‖ with hh
  -- step 1: pointwise
  have hpt : ∀ b : Fin n → X, ‖(if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ M * (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i) else 0) := by
    intro b
    split_ifs with hwb
    · rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod]
      have hprod : ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i)
          = (∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖ :=
        EKSum_prod_ite_subset hBS (fun i => ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
          (fun i => ‖Ξ i (a i) (b i₀)‖)
      rw [hprod]
      have hp0 : 0 ≤ ‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖) :=
        mul_nonneg (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _))
      calc ‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖) * ‖A b‖
          ≤ ‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖) * M :=
            mul_le_mul_of_nonneg_left (hM b) hp0
        _ = M * (‖wf (b i₀)‖ * ((∏ i ∈ B, ‖Ξ i (a i) (b i) - Ξ i (a i) (b i₀)‖)
            * ∏ i ∈ Finset.univ.erase i₀ \ B, ‖Ξ i (a i) (b i₀)‖)) := by ring
    · simp
  -- step 2: the anchored sum
  have hsum : ∑ b : Fin n → X, M * (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i) else 0)
      = M * ∑ x : X, ‖wf x‖ * ∏ i ∈ Finset.univ.erase i₀, ∑ y ∈ Win x, h i x y := by
    rw [← Finset.mul_sum, EKSum_anchor_dep i₀ Win (fun x => ‖wf x‖) h]
  -- step 3: the bound at a point `x`
  have hx : ∀ x : X, ‖wf x‖ * ∏ i ∈ Finset.univ.erase i₀, ∑ y ∈ Win x, h i x y
      ≤ if far x then ‖Ξ i₀ (a i₀) x‖ * (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖) * Snon ^ (n - 2)
        else 0 := by
    intro x
    by_cases hfx : far x
    · have hw := hwf x
      simp only [hfx, ↓reduceIte] at hw ⊢
      rw [hw]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun i => ∑ y ∈ Win x, h i x y) hjS]
      have hj : ∑ y ∈ Win x, h j x y = ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ := by
        simp [hh, hjB]
      rw [hj]
      have hrest : ∏ i ∈ (Finset.univ.erase i₀).erase j, ∑ y ∈ Win x, h i x y ≤ Snon ^ (n - 2) := by
        calc ∏ i ∈ (Finset.univ.erase i₀).erase j, ∑ y ∈ Win x, h i x y
            ≤ ∏ _i ∈ (Finset.univ.erase i₀).erase j, Snon := by
              refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => ?_) ?_
              · simp only [hh]; split_ifs <;> exact norm_nonneg _
              · intro i hi
                have hij : i ≠ j := Finset.ne_of_mem_erase hi
                have hiS : i ∈ Finset.univ.erase i₀ := Finset.mem_of_mem_erase hi
                have hii : i ≠ i₀ := Finset.ne_of_mem_erase hiS
                by_cases hiB : i ∈ B
                · simp only [hh, hiB, ↓reduceIte]
                  exact hΔ x hfx i hii
                · simp only [hh, hiB, ↓reduceIte]
                  rw [Finset.sum_const, nsmul_eq_mul]
                  exact hX x hfx i hii
          _ = Snon ^ (n - 2) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem hjS,
                Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
              congr 1
      have hs0 : 0 ≤ ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ :=
        Finset.sum_nonneg fun y _ => norm_nonneg _
      calc ‖Ξ i₀ (a i₀) x‖ * ((∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖)
            * ∏ i ∈ (Finset.univ.erase i₀).erase j, ∑ y ∈ Win x, h i x y)
          ≤ ‖Ξ i₀ (a i₀) x‖ * ((∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖) * Snon ^ (n - 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrest hs0) (norm_nonneg _)
        _ = ‖Ξ i₀ (a i₀) x‖ * (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖) * Snon ^ (n - 2) := by
            ring
    · have hw := hwf x
      simp only [hfx, ↓reduceIte] at hw ⊢
      rw [hw]
      simp
  -- step 4: the sum over `x`
  calc ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ ∑ b : Fin n → X, ‖(if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
            ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n → X, M * (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
        ‖wf (b i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, h i (b i₀) (b i) else 0) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = M * ∑ x : X, ‖wf x‖ * ∏ i ∈ Finset.univ.erase i₀, ∑ y ∈ Win x, h i x y := hsum
    _ ≤ M * ∑ x : X, (if far x then ‖Ξ i₀ (a i₀) x‖ * (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖)
          * Snon ^ (n - 2) else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hx x) hM0
    _ = M * ((∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
          (∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖)) * Snon ^ (n - 2)) := by
        rw [← Finset.sum_filter, Finset.sum_mul]
    _ ≤ M * (Ψ * Snon ^ (n - 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hΨ j hji) (by positivity)) hM0
    _ = M * (Snon ^ (n - 2) * Ψ) := by ring


/-- **The abstract core of `(sumAzero) ⟹ (sum_res_2)`.**  Over any finite type `X`, with the one-index
rows `u_i = δ + Ξ_i`, the product of `n` rows against a sum-zero tensor `A` (zero sum over all indices
but `i₀`, fast decay `δ` off the window `Win`) is bounded by the five terms below: the part of the
sum with `δ_{a_{i₀} b_{i₀}}` or `b_{i₀}` near an `a_i`, the off-window tail, the leading term killed by
the sum-zero property up to the complement count `|X|^{n-1}`, and the first-difference terms
(`2^{n-1}` subsets, each carrying the lattice sum `Ψ`). -/
private theorem EKSum_core (i₀ : Fin n) (Ξ : Fin n → X → X → ℂ) (a : Fin n → X)
    (A : (Fin n → X) → ℂ) (Win : X → Finset X) (far : X → Prop) [DecidablePred far]
    {M δ Q Sξ Rn Snon Ψ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 ≤ δ) (hQ0 : 0 ≤ Q) (hSξ0 : 0 ≤ Sξ)
    (hSnon0 : 0 ≤ Snon) (hΨ0 : 0 ≤ Ψ) (hM : ∀ b, ‖A b‖ ≤ M)
    (htail : ∀ b : Fin n → X, ¬ (∀ i, i ≠ i₀ → b i ∈ Win (b i₀)) → ‖A b‖ ≤ δ)
    (hsz : ∀ x, ∑ b ∈ Finset.univ.filter (fun b : Fin n → X => b i₀ = x), A b = 0)
    (hrow : ∀ i x, ∑ y, ‖Ξ i x y‖ ≤ Q)
    (hwin : ∀ i, i ≠ i₀ → ∀ x, ∑ y ∈ Win x, ‖Ξ i (a i) y‖ ≤ Sξ)
    (hnear : ∑ x ∈ Finset.univ.filter (fun x => ¬ far x), ‖Ξ i₀ (a i₀) x‖ ≤ Rn)
    (hne : ∀ x, far x → ∀ i, i ≠ i₀ → ∀ y ∈ Win x, a i ≠ y)
    (hX : ∀ x, far x → ∀ i, i ≠ i₀ → ((Win x).card : ℝ) * ‖Ξ i (a i) x‖ ≤ Snon)
    (hΔ : ∀ x, far x → ∀ i, i ≠ i₀ → ∑ y ∈ Win x, ‖Ξ i (a i) y - Ξ i (a i) x‖ ≤ Snon)
    (hΨ : ∀ j, j ≠ i₀ → ∑ x ∈ Finset.univ.filter far, ‖Ξ i₀ (a i₀) x‖ *
        ∑ y ∈ Win x, ‖Ξ j (a j) y - Ξ j (a j) x‖ ≤ Ψ) :
    ‖∑ b : Fin n → X, (∏ i, EKSum_U Ξ a i (b i)) * A b‖ ≤
      (M * ((1 + Rn) * (1 + Sξ) ^ (n - 1)) + δ * ((1 + Rn) * (1 + Q) ^ (n - 1)))
        + δ * (Q * (1 + Q) ^ (n - 1)) + δ * (Q ^ n * (Fintype.card X) ^ (n - 1))
        + 2 ^ (n - 1) * (M * (Snon ^ (n - 2) * Ψ)) := by
  classical
  set ξ0 : X → ℂ := fun x => Ξ i₀ (a i₀) x with hξ0
  set δa : X → ℂ := fun x => if a i₀ = x then 1 else 0 with hδa
  set wn : X → ℂ := fun x => if far x then 0 else ξ0 x with hwn
  set wf : X → ℂ := fun x => if far x then ξ0 x else 0 with hwf'
  have hwf : ∀ x, ‖wf x‖ = if far x then ‖Ξ i₀ (a i₀) x‖ else 0 := by
    intro x; simp only [hwf', hξ0]; split_ifs <;> simp
  -- Step 1: `u_{i₀} = δ + w_near + w_far`
  have hpt : ∀ b : Fin n → X, (∏ i, EKSum_U Ξ a i (b i)) * A b
      = ((δa (b i₀) + wn (b i₀)) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b
        + (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ (fun i => EKSum_U Ξ a i (b i)) (Finset.mem_univ i₀)]
    have h0 : EKSum_U Ξ a i₀ (b i₀) = (δa (b i₀) + wn (b i₀)) + wf (b i₀) := by
      simp only [EKSum_U, hδa, hwn, hwf', hξ0]
      split_ifs <;> ring
    rw [h0]; ring
  have hsplit : ∑ b : Fin n → X, (∏ i, EKSum_U Ξ a i (b i)) * A b
      = ∑ b : Fin n → X, ((δa (b i₀) + wn (b i₀)) *
            ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b
        + ∑ b : Fin n → X, (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => hpt b
  -- Step 2: the `δ + near` part
  have hw1 : ∑ x, ‖δa x + wn x‖ ≤ 1 + Rn := by
    calc ∑ x, ‖δa x + wn x‖ ≤ ∑ x, (‖δa x‖ + ‖wn x‖) :=
          Finset.sum_le_sum fun x _ => norm_add_le _ _
      _ = ∑ x, ‖δa x‖ + ∑ x, ‖wn x‖ := Finset.sum_add_distrib
      _ ≤ 1 + Rn := by
          have h1 : ∑ x, ‖δa x‖ = 1 := by
            have : ∀ x, ‖δa x‖ = if a i₀ = x then (1 : ℝ) else 0 := by
              intro x; simp only [hδa]; split_ifs <;> simp
            simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          have h2 : ∑ x, ‖wn x‖ = ∑ x ∈ Finset.univ.filter (fun x => ¬ far x), ‖Ξ i₀ (a i₀) x‖ := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [hwn, hξ0]
            split_ifs <;> simp_all
          rw [h1, h2]; linarith
  have hP1 := EKSum_UW_bound i₀ Ξ a A Win hM0 hδ hSξ0 hM htail hrow hwin (fun x => δa x + wn x) hw1
  -- the far weight: `‖w_far‖ ≤ ‖Ξ‖`, total at most `Q`
  have hwfQ : ∑ x, ‖wf x‖ ≤ Q := by
    calc ∑ x, ‖wf x‖ ≤ ∑ x, ‖Ξ i₀ (a i₀) x‖ := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [hwf x]; split_ifs <;> simp
      _ ≤ Q := hrow i₀ (a i₀)
  -- Step 3: window / tail
  have hWT : ∑ b : Fin n → X, (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b
      = ∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b else 0)
        + ∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then 0 else
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have hP3 := EKSum_tail_bound i₀ Ξ a A Win wf hδ htail hrow hwfQ
  -- Step 4: the first-difference expansion of the window part
  have hexp : ∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b else 0)
      = ∑ B ∈ (Finset.univ.erase i₀).powerset, ∑ b : Fin n → X,
          (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hwb : ∀ i, i ≠ i₀ → b i ∈ Win (b i₀)
    · simp only [eq_true hwb, ↓reduceIte]
      have hQ : wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)
          = wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀,
              ((Ξ i (a i) (b i) - Ξ i (a i) (b i₀)) + Ξ i (a i) (b i₀)) := by
        by_cases hfb : far (b i₀)
        · congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi
          have hna := hne (b i₀) hfb i hii (b i) (hwb i hii)
          simp only [EKSum_U, hna, ↓reduceIte, zero_add, sub_add_cancel]
        · have : wf (b i₀) = 0 := by simp [hwf', hfb]
          rw [this]; simp
      rw [hQ, Finset.prod_add, Finset.mul_sum, Finset.sum_mul]
    · simp [hwb]
  -- Step 5: the bounds
  have hempty : ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ (∅ : Finset (Fin n)), (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ ∅, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ δ * (Q ^ n * (Fintype.card X) ^ (n - 1)) := by
    have hn1 : n - 1 + 1 = n := by have := i₀.pos; omega
    set c : X → ℂ := fun x => wf x * ∏ i ∈ Finset.univ.erase i₀, Ξ i (a i) x with hc
    have hcsum : ∑ x, ‖c x‖ ≤ Q ^ n := by
      have hent : ∀ i x, ‖Ξ i (a i) x‖ ≤ Q := fun i x =>
        (Finset.single_le_sum (f := fun y => ‖Ξ i (a i) y‖) (fun y _ => norm_nonneg _)
          (Finset.mem_univ x)).trans (hrow i (a i))
      calc ∑ x, ‖c x‖ ≤ ∑ x, ‖wf x‖ * Q ^ (n - 1) := by
            refine Finset.sum_le_sum fun x _ => ?_
            simp only [hc]
            rw [norm_mul, norm_prod]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            calc ∏ i ∈ Finset.univ.erase i₀, ‖Ξ i (a i) x‖ ≤ ∏ _i ∈ Finset.univ.erase i₀, Q :=
                  Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hent i x
              _ = Q ^ (n - 1) := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
                    Finset.card_univ, Fintype.card_fin]
        _ = (∑ x, ‖wf x‖) * Q ^ (n - 1) := (Finset.sum_mul _ _ _).symm
        _ ≤ Q * Q ^ (n - 1) := mul_le_mul_of_nonneg_right hwfQ (pow_nonneg hQ0 _)
        _ = Q ^ n := by rw [← pow_succ', hn1]
    have := EKSum_fempty_bound i₀ A Win c hδ htail hsz hcsum
    simpa only [Finset.prod_empty, Finset.sdiff_empty, one_mul, hc] using this
  have hterms : ∀ B ∈ (Finset.univ.erase i₀).powerset.erase ∅,
      ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
        ≤ M * (Snon ^ (n - 2) * Ψ) := by
    intro B hB
    have hBS : B ⊆ Finset.univ.erase i₀ := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hB)
    have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hB)
    exact EKSum_fB_bound i₀ Ξ a A Win far wf hwf hM0 hSnon0 hM hX hΔ hΨ B hBS hBne
  have hsumB : ‖∑ B ∈ (Finset.univ.erase i₀).powerset.erase ∅, ∑ b : Fin n → X,
        (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
            (wf (b i₀) * ((∏ i ∈ B, (Ξ i (a i) (b i) - Ξ i (a i) (b i₀))) *
              ∏ i ∈ Finset.univ.erase i₀ \ B, Ξ i (a i) (b i₀))) * A b else 0)‖
      ≤ 2 ^ (n - 1) * (M * (Snon ^ (n - 2) * Ψ)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hterms).trans ?_
    rw [nsmul_eq_mul]
    have hcard : (((Finset.univ.erase i₀).powerset.erase ∅).card : ℝ) ≤ 2 ^ (n - 1) := by
      have h1 : ((Finset.univ.erase i₀).powerset.erase ∅).card ≤ 2 ^ (n - 1) := by
        calc ((Finset.univ.erase i₀).powerset.erase ∅).card
            ≤ (Finset.univ.erase i₀).powerset.card := Finset.card_erase_le
          _ = 2 ^ (n - 1) := by
              rw [Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ i₀),
                Finset.card_univ, Fintype.card_fin]
      exact_mod_cast h1
    exact mul_le_mul_of_nonneg_right hcard
      (mul_nonneg hM0 (mul_nonneg (pow_nonneg hSnon0 _) hΨ0))
  -- Step 6: assemble
  have hP2 : ‖∑ b : Fin n → X, (if ∀ i, i ≠ i₀ → b i ∈ Win (b i₀) then
          (wf (b i₀) * ∏ i ∈ Finset.univ.erase i₀, EKSum_U Ξ a i (b i)) * A b else 0)‖
      ≤ δ * (Q ^ n * (Fintype.card X) ^ (n - 1)) + 2 ^ (n - 1) * (M * (Snon ^ (n - 2) * Ψ)) := by
    rw [hexp, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset (Finset.univ.erase i₀))]
    refine (norm_add_le _ _).trans ?_
    exact add_le_add hempty hsumB
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [hWT]
  refine le_trans (add_le_add hP1 ((norm_add_le _ _).trans (add_le_add hP2 hP3))) ?_
  linarith


end Core

end RBM.BA

end
