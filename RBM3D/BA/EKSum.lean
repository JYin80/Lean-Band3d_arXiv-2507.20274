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

end RBM.BA

end
