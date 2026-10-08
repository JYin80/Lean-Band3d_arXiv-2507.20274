/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QtXiRoundLift
import RBM3D.Induction.IterationsB

/-!
# S3-25 (ticket T2320): Step 3 of `lem:main_ind` at the three regimes of the main-induction assembly

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (`1_2:line`) and
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): Step 3 `1_2:1359-1366`, its proof `3_5:1366-1431`
(case `1 - t ≥ ilambda²/L²`) and `3_5:1572-1601` (case `1 - s ≤ ilambda²/L²`).

The pin `STStep3R d R` (`Step34Pins.lean:250`) is `(Eq:LGxb)` uniformly in `u ∈ [s,t]` (`STLmaxU`)
under a regime predicate `R`.  Three targets (DECISIONS §132 (2)), each for every `d`:

* `stStep3RegIII_holds : STStep3R d STReg5III` (`ilambda² ≤ 1 - t`, `3_5:1384`: `(Eq:LGxb)`
  "follows directly from `(lRB1)`");
* `stStep3RegI_holds : STStep3R d STReg5I` (`ilambda²/L² ≤ 1 - t`, `1 - s ≤ ilambda²`,
  `3_5:1407-1431`: `lem:iterations` with `A = ilambda² W^d`);
* `stStep3II_holds : STStep3II d` (`1 - s ≤ ilambda²/L²`, `3_5:1575-1595`: `lem:iterations` with
  `A = (W^{-d}B_{s,0})⁻¹`).

`STStep3I` (case (i) with a straddling `[s,t]`) is not a target (it stays owed until S3-26).

## Contents

* §1 regime (iii): `step3_xB` (`(1-s) B_s ≤ 2 (1-u) B_u` when `ilambda² ≤ 1 - u`);
* §2 the skeleton (port of the probe `st_step3_skeleton`,
  `3c58211:RBM3D/Probe/T2041Pins.lean:1087-1160`, with the case `k = 1` added): `step3_finish`,
  `step3_skeleton`; `step3_hbase` (the a priori level
  `l = 0` of `(eq:iteration_induc)` from `(sef8w483r324)` and `(eq:bcal_k)`); `step3_K_pairs` (the
  pair-uniform `𝒦`-loop bound, rebuilt from `stKbound_timeIcc` as in the private
  `iterationsB_K_pairs`, `IterationsB.lean:525`);
* §3 `step3_assemble` (everything of the iteration case except the three scale facts);
* §4 the targets 1-3;
* §5 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.Step3Inst`).

Helpers are `private` and prefixed `step3_`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ## 1. Regime (iii): `ilambda² ≤ 1 - t`, directly from `(lRB1)` -/

/-- `(1-s) W^{-d}B_{s,0} ≤ 2 (1-u) W^{-d}B_{u,0}` for `s ≤ u < 1` and `ilambda² ≤ 1 - u` (`3_5:1384`: `B_{u,0} ≍ |1-u|⁻¹`):
with `x = 1 - u`, `y = 1 - s`, `a = L^{-d}`, `y B_s = W^{-d}(y/(ilambda² + y) + a) ≤ W^{-d}(1 + a)` and
`x B_u = W^{-d}(x/(ilambda² + x) + a) ≥ W^{-d}(1/2 + a)` because `ilambda² ≤ x`. -/
private theorem step3_xB {n : ℕ} {s u : ℝ} (hsu : s ≤ u) (hu1 : u < 1) (hg : sz.lam n ^ 2 ≤ 1 - u) :
    (1 - s) * sz.Bctl n s ≤ 2 * ((1 - u) * sz.Bctl n u) := by
  unfold Sizes.Bctl Bparam
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  rw [abs_of_pos hxu, abs_of_pos hxs]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hg0 : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (1 - s) * (sz.lam n ^ 2 + (1 - s))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
  have h2 : (1 - s) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ = (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by
    field_simp
  have h2' : (1 - u) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by
    field_simp
  have h3 : 1 ≤ 2 * ((1 - u) * (sz.lam n ^ 2 + (1 - u))⁻¹) := by
    rw [← div_eq_mul_inv, ← mul_div_assoc, le_div_iff₀ (by linarith)]; linarith
  have e1 : (1 - s) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - s))⁻¹ +
      (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹)) =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) * (sz.lam n ^ 2 + (1 - s))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d)⁻¹) := by
    rw [← h2]; ring
  have e2 : 2 * ((1 - u) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ +
      (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹))) =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ((1 - u) * (sz.lam n ^ 2 + (1 - u))⁻¹) + 2 * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹) := by
    rw [← h2']; ring
  rw [e1, e2]
  have hLi : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.2 hLd.le
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hWd.le)


/-! ## 2. The skeleton (probe `st_step3_skeleton`) and its inputs -/

/-- The last step of the skeleton, for a control `Z` of `Ξ̂^{(𝓛-𝒦)}_k`: `Ξ̂^{(𝓛-𝒦)}_{v,k} ≺ Z`, `W^{-d}B_{v,0} Z ≤ c` and
`(rela_XILXILK)` (`3_5:1387`) give `Ξ̂^{(𝓛)}_{v,k} ≺ 1 + B Z ≲ 1`, i.e. `(Eq:LGxb)` at the loop length `k`
(probe `3c58211:RBM3D/Probe/T2041Pins.lean:1087-1160`, with `A^{3/4}` replaced by `Z`). -/
private theorem step3_finish {E s t : ℕ → ℝ} {Z : ℕ → ℝ} (hsize : Tendsto sz.size atTop atTop)
    (ht1 : ∀ n, t n < 1) {k : ℕ}
    (hX : Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 k ω) (fun n _ _ => Z n))
    (hBZ : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n, sz.Bctl n (v : ℝ) * Z n ≤ c)
    (hrela : Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 k ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 k ω)) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1)) := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  let ψ : ∀ n, TimeIcc s t n → STPair s t n := fun n v => ⟨((v : ℝ), (v : ℝ)), (v.2).1, le_rfl, (v.2).2⟩
  have hBpos : ∀ n (v : TimeIcc s t n), 0 < sz.Bctl n (v : ℝ) := fun n v =>
    st_Bctl_pos sz (lt_of_le_of_lt (v.2).2 (ht1 n))
  obtain ⟨cB, hcB0, hcB⟩ := hBZ
  have hB0 : ∀ n (q : STPair s t n), 0 ≤ sz.Bctl n q.1.1 := fun n q => (hBpos n (φ n q)).le
  -- `1 + B Ξ̂^{𝓛-𝒦}_k ≺ 1 + B Z`
  have h4 : Prec sz (U := STPair s t) (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 k ω)
      (fun n q _ => 1 + sz.Bctl n q.1.1 * Z n) := by
    have hm := StochDomAt.mul (P := sz.seqP) (size := sz.size)
      (ξ₁ := fun n (q : STPair s t n) (_ : sz.SeqΩ) => sz.Bctl n q.1.1)
      (ξ₂ := fun n q ω => STXiLK sz n (E n) q.1.1 k ω)
      (ζ₁ := fun n (q : STPair s t n) (_ : sz.SeqΩ) => sz.Bctl n q.1.1)
      (ζ₂ := fun n q _ => Z n) hsize
      (fun n q ω => zero_le_one.trans (st_one_le_XiLK sz k ω (hBpos n (φ n q)))) (fun n q _ => hB0 n q)
      (StochDomAt.refl hsize (fun n q _ => hB0 n q)) hX
    have h1 := StochDomAt.refl (P := sz.seqP) (size := sz.size) (U := STPair s t)
      (ζ := fun _ _ _ => (1 : ℝ)) hsize (fun _ _ _ => zero_le_one)
    exact StochDomAt.add hsize h1 hm
  -- `1 + B Z ≺ 1`
  have hc1 : Prec sz (U := STPair s t) (fun n q ω => (1 + cB) * (1 : ℝ)) (fun _ _ _ => 1) :=
    StochDomAt.const_mul_left hsize (by linarith) (fun _ _ _ => zero_le_one)
      (StochDomAt.refl hsize (fun _ _ _ => zero_le_one))
  have h6 : Prec sz (U := STPair s t) (fun n q _ => 1 + sz.Bctl n q.1.1 * Z n) (fun _ _ _ => 1) := by
    refine StochDomAt.of_subset hc1 fun τ hτ => ⟨τ, hτ, ?_⟩
    filter_upwards [hcB] with n hn ω hω
    obtain ⟨q, hq⟩ := hω
    refine ⟨q, lt_of_lt_of_le hq ?_⟩
    have := hn (φ n q)
    change 1 + sz.Bctl n q.1.1 * Z n ≤ (1 + cB) * 1
    linarith
  have h7 : Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 k ω) (fun _ _ _ => 1) :=
    StochDomAt.trans hsize hrela (StochDomAt.trans hsize h4 h6)
  exact st_prec_of_xi sz (U := fun n => TimeIcc s t n) (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n v p ω => ‖Lloop sz n (E n) (v : ℝ) p.1 p.2 ω‖) (fun n v => (sz.Bctl n (v : ℝ)) ^ (k - 1))
    (fun n v => pow_pos (hBpos n v) _) (StochDomAt.precomp_param h7 ψ)

/-- **Step 3 from `lem:iterations`, both cases** (`3_5:1422-1431` with `A = ilambda² W^d`; `3_5:1575-1595` with
`A = (W^{-d}B_{s,0})⁻¹`): the probe's `st_step3_skeleton` (`3c58211:RBM3D/Probe/T2041Pins.lean:1087-1160`), for every loop
length `k ≥ 1`.  `k ≥ 2`: the one-step statement `hIter` (the conclusion of `STIterations'`/`STIterationsII'`), the
a priori level `hbase`, the depth `hscale` (`Ψ(r,k';s,u) ≤ c A^{3/4}`, `k' > 2 + 8𝔠_d(r-1)`) give
`Ξ̂^{(𝓛-𝒦)}_k ≺ A^{3/4}`; `hBA` (`W^{-d}B_{v,0} A^{3/4} ≤ c`) and `hrela` (`(rela_XILXILK)`) give `(Eq:LGxb)`.
`k = 1`: the averaged law `havg` (`Ξ̂^{(𝓛-𝒦)}_1 ≺ 1`, `3_5:1385`) and `B ≤ B A^{3/4} ≤ c` (`A ≥ 1`). -/
private theorem step3_skeleton {E s t : ℕ → ℝ} {A : ℕ → ℝ} (hsize : Tendsto sz.size atTop atTop)
    (hA : ∀ n, 0 ≤ A n) (hA1 : ∀ᶠ n in atTop, 1 ≤ A n) (ht1 : ∀ n, t n < 1)
    (hIter : ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz E s t A r k) →
      (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz E s t A r (k - 1)) → STIterHyp sz E s t A n_ k)
    (hbase : ∀ r, 2 ≤ r → STIterHyp sz E s t A r 0)
    (hscale : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) r k ≤ c * A n ^ (3 / 4 : ℝ))
    (hBA : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      sz.Bctl n (v : ℝ) * A n ^ (3 / 4 : ℝ) ≤ c)
    (havg : Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
    (hrela : ∀ r, 1 ≤ r → Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 r ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 r ω)) :
    STLmaxU sz E s t := by
  intro k hk
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨cB, hcB0, hcB⟩ := hBA
    refine step3_finish sz (Z := fun _ => (1 : ℝ)) hsize ht1 havg ⟨cB, hcB0, ?_⟩
      (hrela 1 le_rfl)
    filter_upwards [hcB, hA1] with n hn hA1n v
    have h34 : 1 ≤ A n ^ (3 / 4 : ℝ) := Real.one_le_rpow hA1n (by norm_num)
    have hBv : 0 ≤ sz.Bctl n (v : ℝ) := (st_Bctl_pos sz (lt_of_le_of_lt (v.2).2 (ht1 n))).le
    calc sz.Bctl n (v : ℝ) * 1 ≤ sz.Bctl n (v : ℝ) * A n ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left h34 hBv
      _ ≤ cB := hn v
  · have hk2 : 2 ≤ k := by omega
    have hall := st_iterate (S := fun r l => STIterHyp sz E s t A r l) hbase hIter
    obtain ⟨kk, c, hc, hΨ⟩ := hscale k hk2
    have hAA : ∀ n (q : STPair s t n), 0 ≤ A n ^ (3 / 4 : ℝ) := fun n q => Real.rpow_nonneg (hA n) _
    -- `Ξ̂^{𝓛-𝒦}_k ≺ A^{3/4}`
    have h2 : Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 k ω)
        (fun n q _ => c * A n ^ (3 / 4 : ℝ)) := by
      refine StochDomAt.of_subset (hall kk k hk2) fun τ hτ => ⟨τ, hτ, ?_⟩
      filter_upwards [hΨ] with n hn ω hω
      obtain ⟨q, hq⟩ := hω
      refine ⟨q, lt_of_le_of_lt ?_ hq⟩
      exact mul_le_mul_of_nonneg_left (hn q) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h3 : Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 k ω)
        (fun n q _ => A n ^ (3 / 4 : ℝ)) :=
      StochDomAt.trans hsize h2
        (StochDomAt.const_mul_left hsize hc.le (fun n q _ => hAA n q)
          (StochDomAt.refl hsize (fun n q _ => hAA n q)))
    exact step3_finish sz (Z := fun n => A n ^ (3 / 4 : ℝ)) hsize ht1 h3 hBA (hrela k hk)

/-- The real inequality of the a priori level: `1 + cv A (ρ^{r-1} + 1) ≤ (1 + 2 cv) Ψ(r,0)`, `Ψ(r,0) = A^{3/4} + ρ^{r-1} A`
(`A ≥ 1`, `ρ ≥ 1`, `cv ≥ 0`). -/
private theorem step3_psi0_le {A ρ cv : ℝ} {r : ℕ} (hA : 1 ≤ A) (hρ : 1 ≤ ρ) (hcv : 0 ≤ cv) :
    1 + cv * A * (ρ ^ (r - 1) + 1) ≤ (1 + 2 * cv) * STPsi A ρ r 0 := by
  have hA0 : 0 < A := by linarith
  have hρr : 1 ≤ ρ ^ (r - 1) := one_le_pow₀ hρ
  have h34 : 0 ≤ A ^ (3 / 4 : ℝ) := Real.rpow_nonneg hA0.le _
  have hP : STPsi A ρ r 0 = A ^ (3 / 4 : ℝ) + ρ ^ (r - 1) * A := by
    unfold STPsi; simp
  rw [hP]
  have h1 : A ≤ ρ ^ (r - 1) * A := le_mul_of_one_le_left hA0.le hρr
  have h2 : cv * A ≤ cv * (ρ ^ (r - 1) * A) := mul_le_mul_of_nonneg_left h1 hcv
  have h3 : 0 ≤ (1 + 2 * cv) * A ^ (3 / 4 : ℝ) := by positivity
  nlinarith

/-- **The a priori level `l = 0` of `(eq:iteration_induc)`** (`3_5:1391`, `(sef8w483r324)`: `Ξ̂^{(𝓛-𝒦)}_{u,n} ≺ (η_s/η_u)^{n-1}
(ilambda² W^d)`), for `A` with `(cv A)⁻¹ ≤ W^{-d}B_{v,0}` (the scale facts `IterationsAScale`): `Ξ̂^{(𝓛-𝒦)}_{v,r} ≤ 1 +
cv A (Ξ̂^{(𝓛)}_{v,r} + (1 + max|𝒦|/B^{r-1}))`, `Ξ̂^{(𝓛)}_{v,r} ≺ ρ^{r-1}` (`(lRB1)`, `iterationsA_apriori_of_lRB1`) and
`max|𝒦|/B^{r-1} ≺ 1` (`(eq:bcal_k)`), so `Ξ̂^{(𝓛-𝒦)}_{v,r} ≺ 1 + cv A (ρ^{r-1} + 1) ≤ (1 + 2 cv) Ψ(r,0)`
(`ρ ≥ 1`, `A ≥ 1`). -/
private theorem step3_hbase (hsize : Tendsto sz.size atTop atTop) {E s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScale sz E s t A T cB cv K)
    (hapri : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1)))
    (hK : ∀ m, 1 ≤ m → sz.Prec (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖STKloop sz n (E n) p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)))
    {r : ℕ} (hr : 1 ≤ r) :
    STIterHyp sz E s t A r 0 := by
  have hBpos : ∀ n (q : STPair s t n), 0 < sz.Bctl n q.1.1 := fun n q =>
    st_Bctl_pos sz (lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (hS.t_lt_one n))
  have hY := st_prec_one_add_sup sz hsize (U := STPair s t)
    (V := fun n => (Fin r → Bool) × (Fin r → Zd d (sz.L n)))
    (fun n q p ω => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) (fun n q => sz.Bctl n q.1.1 ^ (r - 1))
    (fun n q => pow_pos (hBpos n q) _) (hK r hr)
  have hXY := StochDomAt.add hsize (hapri r hr) hY
  have hcv0 : 0 ≤ cv := by linarith [hS.one_le_cv]
  have hnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ),
      0 ≤ STXiL sz n (E n) q.1.1 r ω + (1 + Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) /
          sz.Bctl n q.1.1 ^ (r - 1)) := fun n q ω => by
    have h1 := st_one_le_XiL sz (n := n) (E := E n) (v := q.1.1) r ω (hBpos n q)
    have h2 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) :=
      le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
        ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
    have h3 := div_nonneg h2 (pow_pos (hBpos n q) (r - 1)).le
    linarith
  have hone := iterationsA_prec_one_add_mul sz hsize (U := STPair s t)
    (c := fun n _ => cv * A n) (fun n _ => mul_nonneg hcv0 (hS.A_nonneg n)) hnn hXY
  have hΨ : sz.Prec (U := STPair s t)
      (fun n q ω => 1 + cv * A n * (STXiL sz n (E n) q.1.1 r ω + (1 + Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) /
          sz.Bctl n q.1.1 ^ (r - 1))))
      (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) r 0) := by
    refine iterationsA_prec_absorb sz hsize (c := 1 + 2 * cv) ?_ ?_
    · filter_upwards [hS.rho] with n hρ q ω
      exact iterationsA_STPsi_nonneg (hS.A_nonneg n) (by linarith [(hρ q).1]) r 0
    · refine iterationsA_prec_mono_right sz hone ?_
      filter_upwards [hS.one_le_A, hS.rho] with n hA1 hρ q ω
      exact step3_psi0_le hA1 (hρ q).1 hcv0
  refine iterationsA_prec_mono_left sz ?_ hΨ
  filter_upwards [hS.Bctl, hS.one_le_A] with n hBn hA1 q ω
  have hB0 := hBpos n q
  have hcvA : 0 < cv * A n := by have := hS.one_le_cv; positivity
  have hlow : (sz.Bctl n q.1.1)⁻¹ ≤ cv * A n := by
    have h := (hBn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).1
    have := inv_anti₀ (inv_pos.2 hcvA) h
    rwa [inv_inv] at this
  set SK : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) with hSK
  have hSL0 : 0 ≤ STmaxL sz n (E n) q.1.1 r ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
      ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have hSK0 : 0 ≤ SK :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
      ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have hSLK : STmaxLK sz n (E n) q.1.1 r ω ≤ STmaxL sz n (E n) q.1.1 r ω + SK := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have h1 : ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω - STKloop sz n (E n) q.1.1 p.1 p.2‖ ≤
        ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω‖ + ‖STKloop sz n (E n) q.1.1 p.1 p.2‖ := norm_sub_le _ _
    have h2 : ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω‖ ≤ STmaxL sz n (E n) q.1.1 r ω :=
      Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
        ‖Lloop sz n (E n) q.1.1 p.1 p.2 ω‖) (Finset.mem_univ p)
    have h3 : ‖STKloop sz n (E n) q.1.1 p.1 p.2‖ ≤ SK :=
      Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
        ‖STKloop sz n (E n) q.1.1 p.1 p.2‖) (Finset.mem_univ p)
    linarith
  have hBr : sz.Bctl n q.1.1 ^ r = sz.Bctl n q.1.1 * sz.Bctl n q.1.1 ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hC : 0 < sz.Bctl n q.1.1 ^ (r - 1) := pow_pos hB0 _
  have hdiv : (STmaxL sz n (E n) q.1.1 r ω + SK) / sz.Bctl n q.1.1 ^ r =
      (STmaxL sz n (E n) q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1) + SK / sz.Bctl n q.1.1 ^ (r - 1)) *
        (sz.Bctl n q.1.1)⁻¹ := by
    rw [hBr]; field_simp
  have hu0 : 0 ≤ STmaxL sz n (E n) q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1) := div_nonneg hSL0 hC.le
  have hv0 : 0 ≤ SK / sz.Bctl n q.1.1 ^ (r - 1) := div_nonneg hSK0 hC.le
  have hstep : STmaxLK sz n (E n) q.1.1 r ω / sz.Bctl n q.1.1 ^ r ≤
      (STmaxL sz n (E n) q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1) + SK / sz.Bctl n q.1.1 ^ (r - 1)) * (cv * A n) := by
    calc STmaxLK sz n (E n) q.1.1 r ω / sz.Bctl n q.1.1 ^ r
        ≤ (STmaxL sz n (E n) q.1.1 r ω + SK) / sz.Bctl n q.1.1 ^ r :=
          div_le_div_of_nonneg_right hSLK (pow_pos hB0 r).le
      _ = _ := hdiv
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (add_nonneg hu0 hv0)
  change 1 + STmaxLK sz n (E n) q.1.1 r ω / sz.Bctl n q.1.1 ^ r ≤
    1 + cv * A n * ((1 + STmaxL sz n (E n) q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1)) + (1 + SK / sz.Bctl n q.1.1 ^ (r - 1)))
  nlinarith [mul_nonneg hcvA.le (add_nonneg hu0 hv0)]

/-- The pair-uniform `𝒦`-loop bound `(eq:bcal_k)` (the hypothesis `hK` of `iterationsA_rela_of_K`): `stKbound_timeIcc`
(uniform in `u ∈ [s,t]`) reindexed along `(q, p) ↦ (⟨q.1.1, _⟩, p)`; copy of the private `iterationsB_K_pairs`
(`IterationsB.lean:525`). -/
private theorem step3_K_pairs (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (m : ℕ) (hm : 1 ≤ m) :
    sz.Prec (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖STKloop sz n (E n) p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)) := by
  have h := stKbound_timeIcc sz hd hκ hg hN hE hlam hs0 hst ht1 m hm
  let φ : ∀ n, STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) →
      TimeIcc s t n × (Fin m → Bool) × (Fin m → Zd d (sz.L n)) :=
    fun n p => (⟨p.1.1.1, p.1.2.1, p.1.2.2.1.trans p.1.2.2.2⟩, p.2)
  exact StochDomAt.precomp_param h φ

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually (copy of the private `iterationsB_flowLam`, `IterationsB.lean:517`). -/
private theorem step3_flowLam {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-! ## 3. The assembly at a `lem:iterations` regime -/

/-- **Step 3 from the premises of `lem:iterations`**: the flow supplies `Admissible`, `|E_n| < 2`, `t_n < 1`
(`v3_premises_of_stFlow`); `(lRB1)` is the a priori bound `iterationsA_apriori_of_lRB1`, `STAvgU` (a part of
`STStep2Concl`) is the averaged law, the uniform `𝒦` bound `step3_K_pairs` gives `(rela_XILXILK)` and, with the scale
facts `hS`, the a priori level `step3_hbase`; `hIter` is the conclusion of `STIterations'`/`STIterationsII'` and
`hscale`, `hBA` the deterministic scale facts of `ScaleFacts3`.  The scale facts are arguments depending on the
derived facts `t_n < 1`, `|E_n| < 2`, `(eq:WO)` (as in `iterationsB_setting`). -/
private theorem step3_assemble (hd : 3 ≤ d) {κ ε 𝔠 𝔡 Cd : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) {A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : (∀ n, t n < 1) → (∀ n, |STflowE z n| < 2) → sz.WO 𝔡 →
      IterationsAScale sz (STflowE z) s t A T cB cv K)
    (hscale : (∀ n, t n < 1) → (∀ n, |STflowE z n| < 2) → sz.WO 𝔡 →
      ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
        STPsi (A n) (etaT (STflowE z n) (s n) / etaT (STflowE z n) q.1.2) r k ≤ c * A n ^ (3 / 4 : ℝ))
    (hBA : (∀ n, t n < 1) → sz.WO 𝔡 → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      sz.Bctl n (v : ℝ) * A n ^ (3 / 4 : ℝ) ≤ c)
    (hIter : ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
      (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz (STflowE z) s t A r k) →
      (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz (STflowE z) s t A r (k - 1)) →
      STIterHyp sz (STflowE z) s t A n_ k)
    (hStep1 : STStep1Loop sz (STflowE z) s t) (hStep2 : STStep2Concl sz (STflowE z) s t Cd) :
    STLmaxU sz (STflowE z) s t := by
  obtain ⟨hAd, hE', ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hE : ∀ n, |STflowE z n| < 2 := fun n => by linarith [hE' n]
  have hsize := tendsto_size sz hAd.2.2.1
  have hWO := hAd.2.2.2.2
  have hK : ∀ m, 1 ≤ m → sz.Prec (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖STKloop sz n (STflowE z n) p.1.1.1 p.2.1 p.2.2‖)
      (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)) := fun m hm =>
    step3_K_pairs sz hd (half_pos hκ) (inv_pos.2 hAd.2.1) hAd.2.2.1
      (Eventually.of_forall fun n => (hE' n).le) (step3_flowLam sz hflow) hs0 (fun n => (hst n).le) ht1 m hm
  have hS' := hS ht1 hE hWO
  have hapri := iterationsA_apriori_of_lRB1 sz hsize ht1 hE hStep1
  exact step3_skeleton sz hsize hS'.A_nonneg hS'.one_le_A ht1 hIter
    (fun r hr => step3_hbase sz hsize hS' hapri hK (by omega)) (hscale ht1 hE hWO) (hBA ht1 hWO)
    (iterationsA_avg_of_STAvgU sz hsize ht1 hStep2.2.1)
    (fun r hr => iterationsA_rela_of_K sz hsize ht1 r hr (hK r hr))

end RBM.Gauss.Sizes

/-! ## 4. The targets -/

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Step 3 at regime (iii)** `ilambda² ≤ 1 - t` (`3_5:1384`: `(Eq:LGxb)` follows directly from `(lRB1)`), every `d`,
`𝔠_d = 1/100` (not used by the proof).  `((1-s)/(1-u)) W^{-d}B_{s,0} ≤ 2 W^{-d}B_{u,0}` for `u ∈ [s,t]`
(`step3_xB`), so `(lRB1)` gives `|𝓛^{(k)}_u| ≺ 2^{k-1} (W^{-d}B_{u,0})^{k-1}`, and the constant is absorbed. -/
theorem stStep3RegIII_holds : ∀ d : ℕ, STStep3R d STReg5III := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg _hK _hKw _hLK _hcon hStep1 _hStep2 k hk
  obtain ⟨hA, -, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hsize := tendsto_size sz hA.2.2.1
  have hB : ∀ n (p : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))),
      0 ≤ sz.Bctl n (p.1 : ℝ) ^ (k - 1) := fun n p =>
    (pow_pos (st_Bctl_pos sz (lt_of_le_of_lt (p.1.2).2 (ht1 n))) _).le
  refine iterationsA_prec_absorb sz hsize (c := 2 ^ (k - 1)) (Eventually.of_forall fun n p _ => hB n p) ?_
  refine iterationsA_prec_mono_right sz (hStep1 k hk) (Eventually.of_forall fun n p _ => ?_)
  have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt (p.1.2).2 (ht1 n)
  have hx : 0 < 1 - (p.1 : ℝ) := by linarith
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (lt_of_le_of_lt (p.1.2).1 hu1)
  have hgu : sz.lam n ^ 2 ≤ 1 - (p.1 : ℝ) := (hreg n).trans (by linarith [(p.1.2).2])
  have hxB := step3_xB sz (n := n) (p.1.2).1 hu1 hgu
  have hq : (1 - s n) / (1 - (p.1 : ℝ)) * sz.Bctl n (s n) ≤ 2 * sz.Bctl n (p.1 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx]; linarith
  have hq0 : 0 ≤ (1 - s n) / (1 - (p.1 : ℝ)) * sz.Bctl n (s n) := by
    have : 0 < 1 - s n := by linarith [(p.1.2).1, hs0 n]
    positivity
  calc ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * sz.Bctl n (s n) ^ (k - 1)
      = ((1 - s n) / (1 - (p.1 : ℝ)) * sz.Bctl n (s n)) ^ (k - 1) := (mul_pow _ _ _).symm
    _ ≤ (2 * sz.Bctl n (p.1 : ℝ)) ^ (k - 1) := pow_le_pow_left₀ hq0 hq _
    _ = 2 ^ (k - 1) * sz.Bctl n (p.1 : ℝ) ^ (k - 1) := mul_pow _ _ _

/-- **Step 3 at regime (i)** `ilambda²/L² ≤ 1 - t`, `1 - s ≤ ilambda²` (`3_5:1407-1431`), every `d`.  The constant is
`𝔠_d = min(𝔠_d^{Qt}, 𝔠_d^{It})`, the constants of `stOeqQt'_holds` (`STXiBoot'`, `3_5:1366`) and
`stIterations'_holds` (`lem:iterations` case (i)); `(con_st_ind)` at the minimum gives it at each of them
(`st5_conStInd_mono`).  The iteration `st_iterate` over `stIterations'_holds` (`A = ilambda² W^d`), the scale facts
`st_hscale_I'`, `st_hBA_I`, the a priori level `step3_hbase` and `(rela_XILXILK)` give `(Eq:LGxb)`. -/
theorem stStep3RegI_holds : ∀ d : ℕ, STStep3R d STReg5I := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := stOeqQt'_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := stIterations'_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hcle : min c₁ c₂ ≤ 1 / 100 := (min_le_left _ _).trans hc₁'
  refine ⟨min c₁ c₂, hcpos, hcle, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg hK hKw hLK hcon hStep1 hStep2
  obtain ⟨hAd, hE', ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hregI : STRegIterI sz s t := ⟨fun n => (hreg n).1, fun n => (hreg n).2⟩
  have m : ∀ c', min c₁ c₂ ≤ c' → STConStInd sz c' s t := fun c' hcc =>
    st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hboot : STXiBoot' sz (STflowE z) s t :=
    H₁ 𝔠 sz z hflow s t hs0 hst htT hregI.1 hK hKw hLK (m c₁ (min_le_left _ _)) hStep2
  have hIter := H₂ 𝔠 sz z hflow s t hs0 hst htT hregI hK hLK (m c₂ (min_le_right _ _)) hStep1 hStep2 hboot
  exact step3_assemble sz hd hκ hε hflow hs0 hst htT (A := fun n => sz.STAI n)
    (fun ht1 hE hWO => iterationsA_scale_I sz (by omega) hcpos (hcle.trans (by norm_num)) hregI hcon hWO ht1 hE)
    (fun ht1 hE hWO => st_hscale_I' sz hcpos hregI hcon hWO ht1 hE)
    (fun _ hWO => st_hBA_I sz (by omega) hregI.1 hWO) hIter hStep1 hStep2

/-- **Step 3, case (ii)** `1 - s ≤ ilambda²/L²` (`3_5:1575-1595`), every `d`.  The constant is
`𝔠_d = min(𝔠_d^{NZ}, 𝔠_d^{It'})`, the constants of `stOeqQtNZ'_holds` (`STXiBoot'`, `3_5:1561`) and
`stIterationsII'_holds` (`A = (W^{-d}B_{s,0})⁻¹`, `3_5:1575-1595`); scale facts `st_hscale_II'`, `st_hBA_II`
(`𝔠_d ≤ 1/4`), `iterationsA_scale_II` (`𝔠_d ≤ 1/24`). -/
theorem stStep3II_holds : ∀ d : ℕ, STStep3II d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := stOeqQtNZ'_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := stIterationsII'_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hcle : min c₁ c₂ ≤ 1 / 100 := (min_le_left _ _).trans hc₁'
  refine ⟨min c₁ c₂, hcpos, hcle, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg hK hKw hLK hcon hStep1 hStep2
  obtain ⟨hAd, hE', ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have m : ∀ c', min c₁ c₂ ≤ c' → STConStInd sz c' s t := fun c' hcc =>
    st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hboot : STXiBoot' sz (STflowE z) s t :=
    H₁ 𝔠 sz z hflow s t hs0 hst htT hreg hK hKw hLK (m c₁ (min_le_left _ _)) hStep2
  have hIter := H₂ 𝔠 sz z hflow s t hs0 hst htT hreg hK hLK (m c₂ (min_le_right _ _)) hStep1 hStep2 hboot
  exact step3_assemble sz hd hκ hε hflow hs0 hst htT (A := fun n => sz.STAII s n)
    (fun ht1 hE _ => iterationsA_scale_II sz hcpos (hcle.trans (by norm_num)) hcon ht1 hE)
    (fun ht1 hE _ => st_hscale_II' sz hcpos hcon ht1 hE)
    (fun ht1 _ => st_hBA_II sz hcpos (hcle.trans (by norm_num)) hcon ht1) hIter hStep1 hStep2


/-! ## 5. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.Step3Inst`.  Data, all from the merged instance files (`Step34Pins.lean`, `Induction/Defs.lean`):
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `C_d` arbitrary positive, and

* regime (iii): `sz0` (`d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, `ilambda = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`,
  `ilambda = 1/64`), the flow `z0`, `s ≡ 0`, `t ≡ 1/16` (`t ≤ lemT z0`: `sz0_ht`), `ilambda² ≤ 1/4096 ≤ 15/16 = 1 - t`
  (`sz0_regIII`), `(con_st_ind)` for every `𝔠_d > 0` (`sz0_con`);
* regime (i): `szB` (`L = 4`, `W = n + 4`, `ilambda = 1`), the flow `zB` (`z_n = 1/2 + i/64`), `(s,t) = (7/8, 15/16)`:
  `1 - s = 1/8 ≤ ilambda² = 1` and `ilambda²/L² = 1/16 = 1 - t` (`szB_regIterI`), `(con_st_ind)` by `conStInd_const`;
* case (ii): `szB`, `zB`, `(s,t) = (15/16, 31/32)`: `1 - s = ilambda²/L² = 1/16` (`szB_caseII`).

`STKbound` and `STKward` are theorems of the flow (`stKbound_of_flow`, `stKward_of_flow`) and are discharged; what stays a
hypothesis of an instance is a stochastic premise that is another gate's pin: `STLK s`, `(lRB1)` (`STStep1Loop`), the
Step-2 conclusions (`STStep2Concl`). -/

namespace Step3Inst

open RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Gauss.SizesInst

/-- Regime (iii) at `sz0`, `t ≡ 1/16`: `ilambda_n² ≤ (1/64)² ≤ 15/16 = 1 - t`. -/
theorem sz0_regIII : STReg5III sz0 sInst tInst := by
  intro n
  have h64 : (64 : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ 6 := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ (2 * ((n : ℝ) + 1)) ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) 6
  have hl : sz0.lam n ≤ 1 / 64 := by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
    rw [one_div]; exact inv_anti₀ (by norm_num) h64
  have hl0 : 0 ≤ sz0.lam n := by
    change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
    positivity
  change sz0.lam n ^ 2 ≤ 1 - 1 / 16
  nlinarith

/-- **Instance (1): `stStep3RegIII_holds`** at `d = 3`, `(sz0, z0, s ≡ 0, t ≡ 1/16)`: the constant `𝔠_d ∈ (0, 1/100]`, then
the stochastic premises `STLK`, `(lRB1)`, `STStep2Concl`, then `(Eq:LGxb)` uniformly in `u ∈ [0, 1/16]`.  Every deterministic
hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the regime, `(con_st_ind)`, `STKbound`, `STKward`) is discharged. -/
theorem inst_regIII (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd → STLmaxU sz0 (STflowE z0) sInst tInst) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_step3R STReg5III (stStep3RegIII_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_regIII sz0_con Cd hCd
  exact ⟨𝔠d, h0, h1, H (stKbound_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0)⟩

/-- **Instance (2): `stStep3RegI_holds`** at `d = 3`, `(szB, zB, s ≡ 7/8, t ≡ 15/16)`. -/
theorem inst_regI (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK szB (STflowE zB) (fun _ => 7 / 8) →
        STStep1Loop szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
        STStep2Concl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd →
        STLmaxU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_step3R STReg5I (stStep3RegI_holds 3) szB zB flow_zB
    (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun n => ⟨szB_regIterI.1 n, szB_regIterI.2 n⟩)
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd
  exact ⟨𝔠d, h0, h1, H (stKbound_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB)
    (stKward_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB)⟩

/-- **Instance (3): `stStep3II_holds`** at `d = 3`, `(szB, zB, s ≡ 15/16, t ≡ 31/32)`. -/
theorem inst_II (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK szB (STflowE zB) (fun _ => 15 / 16) →
        STStep1Loop szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
        STStep2Concl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) Cd →
        STLmaxU szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_step3R STCaseII (stStep3II_holds 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd
  exact ⟨𝔠d, h0, h1, H (stKbound_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB)
    (stKward_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB)⟩

/-- **The `(R3)` comparison at concrete numbers** (`sz0`, `n = 0`: `L = 4`, `W = 32`, `ilambda = 1/64`; `s = 0`, `u = 1/32`,
`ilambda² = 1/4096 ≤ 1 - u`): `((1-s)/(1-u)) W^{-d}B_{s,0} ≤ 4 W^{-d}B_{u,0}` (the proof of regime (iii) gives the constant
`2`, `step3_xB`). -/
example : (1 - (0 : ℝ)) / (1 - 1 / 32) * sz0.Bctl 0 0 ≤ 4 * sz0.Bctl 0 (1 / 32) := by
  obtain ⟨hL, hW, -, hlam⟩ := sz0_values
  unfold Sizes.Bctl Bparam
  rw [hL, hW, hlam]
  norm_num [abs_of_pos]

/-- The same with the constant `2` of `step3_xB` (`n = 0`, `s = 0`, `u = 1/32`). -/
example : (1 - (0 : ℝ)) / (1 - 1 / 32) * sz0.Bctl 0 0 ≤ 2 * sz0.Bctl 0 (1 / 32) := by
  obtain ⟨hL, hW, -, hlam⟩ := sz0_values
  unfold Sizes.Bctl Bparam
  rw [hL, hW, hlam]
  norm_num [abs_of_pos]

end Step3Inst

end RBM.Ind

#print axioms RBM.Ind.stStep3RegIII_holds
#print axioms RBM.Ind.stStep3RegI_holds
#print axioms RBM.Ind.stStep3II_holds
#print axioms RBM.Ind.Step3Inst.inst_regIII
#print axioms RBM.Ind.Step3Inst.inst_regI
#print axioms RBM.Ind.Step3Inst.inst_II
