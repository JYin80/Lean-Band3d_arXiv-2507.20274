/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.ScaleFacts

/-!
# S3-23 (ticket T2058): the deterministic scale facts of Steps 3 and 4 at `d ≥ 3`

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (`1_2:line`) and
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`).  Everything here is real-variable algebra on the
merged `Sizes.Bctl`, `Gauss.etaT`, `STPsi`, `STConStInd`; no random variable occurs.  No RBM2D
source (portmap row S3-23: "new (paper lines)"); the three helpers of section 1 are copied
verbatim from the T2041 probe `3c58211:RBM3D/Probe/T2041Pins.lean` (`st_Bctl_ge` :887-925,
`st_bootRHS_one` :940-945, `st_iterate` :1049-1065).

* §1 `st_Bctl_ge`, `st_bootRHS_one`, `st_iterate` (probe text, now public);
* §2 `st_kmin` (the iteration depth `k > 2 + 8 𝔠d (r - 1)`, `3_5:1422-1431`) and
  `st_hscale_I/II`, `st_hscale_I'/II'` (the hypothesis `hscale` of the probe's
  `st_step3_skeleton`): `Ψ(r,k;s,u) ≤ c A^{3/4}`, `(adsyzz0s8d6)` `3_5:1396` (case (i),
  `A = ilambda² W^d`) and `(eq:psipara_smalletacase)` `3_5:1577` (case (ii),
  `A = (W^{-d}B_{s,0})⁻¹`);
* §3 `st_hBA_I/II` (the hypothesis `hBA`: `W^{-d}B_{v,0} A^{3/4} ≤ c`);
* §4 `st_window`, `st_EKWin` (`(1-t)/(1-s) ≥ W⁻¹`, the window of `lem:sum_decay`,
  `3_5:1633-1637`);
* §5 `st_conStInd_sub` and the split at the middle time `u = 1 - ilambda²/L²`
  (`3_5:1104-1105`): `st_split_I`, `st_split_II`;
* §6 the compiled instances (`d = 3`).

Statement-level differences from the ticket (each is a real condition of the mathematics, none
weakens a conclusion; paper-delta candidates in the prove report): `hBA` case (i) needs `2 ≤ d`
(`L^d ≥ L²`, `T2058c`); `hBA` case (ii) needs `𝔠d ≤ 1/4` and no range hypothesis (`B_s < 1`
follows from `(con_st_ind)`, `T2058a`); `st_window` needs `(eq:WO)` and `W → ∞` besides
`d 𝔠d < 1` (`T2058b`); `st_hscale_II` does not use `STCaseII` (the regime enters only through
`A = STAII`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ## 1. The deterministic helpers of the probe skeletons (verbatim from the probe) -/

/-- `W^{-d} B_{u,0} ≥ (W^d)⁻¹ (ilambda² + 1)⁻¹ ≥ N^{-2}`, eventually, for `u ∈ [0,1]` (`0 < ilambda ≤ Λ`). -/
theorem st_Bctl_ge {Λ : ℝ} (hsize : Tendsto sz.size atTop atTop)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) :
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ sz.Bctl n u := by
  have hΛ : ∀ᶠ n in atTop, Λ ^ 2 + 1 ≤ ((sz.size n : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_iff.2 hsize).eventually (eventually_ge_atTop (Λ ^ 2 + 1))
  filter_upwards [hlam, hΛ] with n hn hN u hu0 hu1
  obtain ⟨hlam0, hlamΛ⟩ := hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by nlinarith [sq_nonneg Λ]
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    exact_mod_cast h
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hg2 : sz.lam n ^ 2 ≤ Λ ^ 2 := by nlinarith
  have hB : (sz.lam n ^ 2 + 1)⁻¹ ≤ Bparam d (sz.L n) (sz.lam n) u 0 := by
    unfold Bparam
    have h1 : (sz.lam n ^ 2 + |1 - u|)⁻¹ ≥ (sz.lam n ^ 2 + 1)⁻¹ := by
      apply inv_anti₀ (by positivity)
      have : |1 - u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have h2 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
    have h3 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
    rw [h2]; simp only [inv_one, mul_one]
    linarith
  have hlow : ((sz.size n : ℕ) : ℝ)⁻¹ * (Λ ^ 2 + 1)⁻¹ ≤ sz.Bctl n u := by
    unfold Sizes.Bctl
    calc ((sz.size n : ℕ) : ℝ)⁻¹ * (Λ ^ 2 + 1)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ := by
          apply mul_le_mul (inv_anti₀ hWpos hWd) (inv_anti₀ (by positivity) (by linarith)) (by positivity)
            (by positivity)
      _ ≤ _ := by gcongr
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  calc ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) = ((sz.size n : ℕ) : ℝ)⁻¹ * ((sz.size n : ℕ) : ℝ)⁻¹ := by
        rw [Real.rpow_neg hNpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    _ ≤ ((sz.size n : ℕ) : ℝ)⁻¹ * (Λ ^ 2 + 1)⁻¹ := by
        gcongr
    _ ≤ _ := hlow


/-- `STbootRHS` with all control parameters `1`: `B^{-1/(4p)} + c_n`, `c_n` independent of `B` and `p`. -/
theorem st_bootRHS_one (lo : ℕ) (B : ℝ) (n_ p : ℕ) :
    STbootRHS lo (fun _ => 1) (fun _ => 1) B n_ p = B ^ (-(1 : ℝ) / (4 * (p : ℝ))) +
      (((Finset.Icc lo (n_ - 1)).card + (Finset.Icc (n_ - 1) (n_ + 1)).card +
        (Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1)).card : ℕ) : ℝ) := by
  simp [STbootRHS, Real.one_rpow]

/-- The double induction of `3_5:1422-1426`: from the a priori level `l = 0` for every `r ≥ 2` and the one-step
statement of `lem:iterations` (`(r,k)`, `r < n`, and `(r,k-1)`, `r ≤ n+2` give `(n,k)`), every `(r,k)`,
`r ≥ 2`, `k ≥ 0` (outer induction on `k`, inner on `r`). -/
theorem st_iterate {S : ℕ → ℕ → Prop} (hbase : ∀ r, 2 ≤ r → S r 0)
    (hstep : ∀ n k, 2 ≤ n → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n → S r k) →
      (∀ r, 2 ≤ r → r ≤ n + 2 → S r (k - 1)) → S n k) :
    ∀ k r, 2 ≤ r → S r k := by
  intro k
  induction k with
  | zero => exact hbase
  | succ k ih =>
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ihr =>
      intro hr
      exact hstep r (k + 1) hr (Nat.succ_pos k) (fun r' hr' hlt => ihr r' (by omega) hr')
        (fun r' hr' _ => by simpa using ih r' hr')

/-! ## 2. The `Ψ`-bounds `hscale` and the iteration depth `k_min` -/

/-- The iteration depth of `3_5:1422-1431`: `k_min = ⌊2 + 8 𝔠d (r - 1)⌋ + 1`, the least natural number with
`k > 2 + 8 𝔠d (r - 1)`, i.e. with `𝔠d (r - 1) + 1 - k/8 < 3/4` (the exponent count `r^{r-1} A^{1-k/8} ≤ C A^{3/4}`
for `r ≤ A^{𝔠d}`). -/
def st_kmin (𝔠d : ℝ) (r : ℕ) : ℕ := ⌊2 + 8 * 𝔠d * ((r : ℝ) - 1)⌋₊ + 1

private theorem st_kmin_gt (𝔠d : ℝ) (r : ℕ) : 2 + 8 * 𝔠d * ((r : ℝ) - 1) < (st_kmin 𝔠d r : ℝ) := by
  unfold st_kmin
  push_cast
  exact Nat.lt_floor_add_one _

/-- `(eq:WO)` forces `𝔡 > 0`: otherwise `𝔡⁻¹ ≤ 0 < W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡⁻¹`. -/
private theorem st_WO_pos {𝔡 : ℝ} (hWO : sz.WO 𝔡) : 0 < 𝔡 := by
  obtain ⟨n, h1, h2⟩ := hWO.exists
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact inv_pos.1 (lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) (h1.trans h2))

/-- From `(eq:WO)`: `ilambda > 0` and `A_I = ilambda² W^d ≥ W^{2𝔡} ≥ 1`, eventually. -/
private theorem st_WO_AI {𝔡 : ℝ} (hWO : sz.WO 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ 1 ≤ sz.STAI n := by
  have h𝔡 := st_WO_pos sz hWO
  filter_upwards [hWO] with n hn
  obtain ⟨h1, -⟩ := hn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  refine ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) h1, ?_⟩
  have h2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.one_le_rpow hW1 (by linarith)
  exact h2.trans (Sizes.lam_sq_mul_pow_ge sz n h1)

/-- `(con_st_ind)` gives `s < t` and `W^{-d} B_{t,0} < 1`, eventually (`t < 1`, `𝔠d > 0`). -/
private theorem st_con_aux {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) : ∀ᶠ n in atTop, s n < t n ∧ sz.Bctl n (t n) < 1 := by
  filter_upwards [hcon] with n hn
  obtain ⟨h1, h2⟩ := hn
  have hBt : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
  have hpos : 0 < sz.Bctl n (t n) ^ 𝔠d := Real.rpow_pos_of_pos hBt _
  have hxt : 0 < 1 - t n := by linarith [ht1 n]
  have hr0 : 0 < (1 - t n) / (1 - s n) := lt_of_lt_of_le hpos h1
  have hxs : 0 < 1 - s n := by
    rcases (div_pos_iff.1 hr0) with h | h
    · exact h.2
    · linarith [h.1]
  refine ⟨?_, ?_⟩
  · have := (div_lt_one hxs).1 h2
    linarith
  · by_contra h
    have := Real.one_le_rpow (not_lt.1 h) h𝔠d.le
    linarith

/-- `η_s/η_v = (1-s)/(1-v) ≤ (W^{-d}B_{t,0})^{-𝔠d}` for `s ≤ v ≤ t < 1` from `(con_st_ind)` at `n`. -/
private theorem st_rho_le {n : ℕ} {c s v t : ℝ} (hsv : s ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    (hB : sz.Bctl n t ^ c ≤ (1 - t) / (1 - s)) :
    (1 - s) / (1 - v) ≤ (sz.Bctl n t) ^ (-c) := by
  have hBt : 0 < sz.Bctl n t := STBctl_pos sz n ht1
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  calc (1 - s) / (1 - v) ≤ (1 - s) / (1 - t) := div_le_div_of_nonneg_left hxs.le hxt (by linarith)
    _ = ((1 - t) / (1 - s))⁻¹ := (inv_div _ _).symm
    _ ≤ (sz.Bctl n t ^ c)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hBt c) hB
    _ = sz.Bctl n t ^ (-c) := (Real.rpow_neg hBt.le c).symm

/-- Case (i): `W^{-d} B_{t,0} ≥ (2 A_I)⁻¹` when `1 - t ≤ 1 - s ≤ ilambda²` (`s ≤ t < 1`, `ilambda > 0`):
`(ilambda² + 1 - t)⁻¹ ≥ (2 ilambda²)⁻¹`. -/
private theorem st_BI_lower {n : ℕ} {s t : ℝ} (hst : s ≤ t) (ht1 : t < 1) (hs : 1 - s ≤ sz.lam n ^ 2)
    (hlam : 0 < sz.lam n) : 1 / (2 * sz.STAI n) ≤ sz.Bctl n t := by
  unfold Sizes.Bctl Bparam STAI
  have hx : 0 < 1 - t := by linarith
  rw [abs_of_pos hx]
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
  simp only [hz, inv_one, mul_one]
  have hg : 0 < sz.lam n ^ 2 := by positivity
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have h1 : (2 * sz.lam n ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + (1 - t))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ := by positivity
  calc 1 / (2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d))
      = ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (2 * sz.lam n ^ 2)⁻¹ := by field_simp
    _ ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ((sz.lam n ^ 2 + (1 - t))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The real-variable core of `hscale`: `ρ ≤ a A^{𝔠d}`, `A ≥ 1`, `r ≥ 2` give
`Ψ(r, k_min; ρ) = A^{3/4} + ρ^{r-1} A^{1-k/8} ≤ (1 + a^{r-1}) A^{3/4}`:
`ρ^{r-1} A^{1-k/8} ≤ a^{r-1} A^{𝔠d (r-1) + 1 - k/8} ≤ a^{r-1} A^{3/4}` since `k > 2 + 8 𝔠d (r - 1)`. -/
private theorem st_psi_core {A ρ a c : ℝ} {r : ℕ} (hr : 2 ≤ r) (hA : 1 ≤ A) (hρ0 : 0 ≤ ρ)
    (ha : 0 ≤ a) (hρ : ρ ≤ a * A ^ c) :
    STPsi A ρ r (st_kmin c r) ≤ (1 + a ^ (r - 1)) * A ^ (3 / 4 : ℝ) := by
  unfold STPsi
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hk := st_kmin_gt c r
  have hpow : ρ ^ (r - 1) ≤ a ^ (r - 1) * A ^ (c * ((r - 1 : ℕ) : ℝ)) := by
    calc ρ ^ (r - 1) ≤ (a * A ^ c) ^ (r - 1) := pow_le_pow_left₀ hρ0 hρ _
      _ = a ^ (r - 1) * (A ^ c) ^ (r - 1) := mul_pow _ _ _
      _ = a ^ (r - 1) * A ^ (c * ((r - 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_mul hA0.le, Real.rpow_natCast]
  have hexp : A ^ (c * ((r - 1 : ℕ) : ℝ)) * A ^ (1 - (st_kmin c r : ℝ) / 8) ≤ A ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hA0]
    apply Real.rpow_le_rpow_of_exponent_le hA
    rw [hr1]; linarith
  have hA1 : 0 ≤ A ^ (1 - (st_kmin c r : ℝ) / 8) := Real.rpow_nonneg hA0.le _
  have ha1 : 0 ≤ a ^ (r - 1) := pow_nonneg ha _
  calc A ^ (3 / 4 : ℝ) + ρ ^ (r - 1) * A ^ (1 - (st_kmin c r : ℝ) / 8)
      ≤ A ^ (3 / 4 : ℝ) + (a ^ (r - 1) * A ^ (c * ((r - 1 : ℕ) : ℝ))) *
          A ^ (1 - (st_kmin c r : ℝ) / 8) := by gcongr
    _ = A ^ (3 / 4 : ℝ) + a ^ (r - 1) *
          (A ^ (c * ((r - 1 : ℕ) : ℝ)) * A ^ (1 - (st_kmin c r : ℝ) / 8)) := by ring
    _ ≤ A ^ (3 / 4 : ℝ) + a ^ (r - 1) * A ^ (3 / 4 : ℝ) := by gcongr
    _ = (1 + a ^ (r - 1)) * A ^ (3 / 4 : ℝ) := by ring

/-- **The `Ψ`-bound `hscale`, case (i)** (`(adsyzz0s8d6)` `3_5:1396`, depth `3_5:1422-1431`): under `STRegIterI`
(`1 - s ≤ ilambda²`, `1 - t ≥ ilambda²/L²`), `(con_st_ind)`, `(eq:WO)`, `t < 1`, `|E| < 2`, `𝔠d > 0`: for every `r ≥ 2`
there is `c > 0` with `Ψ(r, k_min; s, u) ≤ c A^{3/4}`, `A = ilambda² W^d`, uniformly in `q = (v,u) ∈ STPair`, eventually.
Proof: `η_s/η_u = (1-s)/(1-u) ≤ (1-s)/(1-t) ≤ B_t^{-𝔠d} ≤ (2A)^{𝔠d}` (`B_t ≥ (2A)⁻¹` since `1 - t ≤ ilambda²`),
and `A ≥ W^{2𝔡} ≥ 1`; `c = 1 + (2^{𝔠d})^{r-1}`. -/
theorem st_hscale_I {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ} (h𝔠d : 0 < 𝔠d) (hreg : STRegIterI sz s t)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAI n) (etaT (E n) (s n) / etaT (E n) q.1.2) r (st_kmin 𝔠d r) ≤
        c * sz.STAI n ^ (3 / 4 : ℝ) := by
  refine ⟨1 + ((2 : ℝ) ^ 𝔠d) ^ (r - 1), by positivity, ?_⟩
  filter_upwards [hcon, st_WO_AI sz hWO] with n hn hW q
  obtain ⟨hlam, hA⟩ := hW
  have hsq : s n ≤ q.1.2 := q.2.1.trans q.2.2.1
  have hst : s n ≤ t n := hsq.trans q.2.2.2
  have hxt := ht1 n
  rw [RBM.Ind.scaleFacts_etaT_div_etaT (hE n)]
  have hρ0 : 0 ≤ (1 - s n) / (1 - q.1.2) :=
    div_nonneg (by linarith [q.2.2.2]) (by linarith [q.2.2.2])
  have hρ := st_rho_le sz hsq q.2.2.2 hxt hn.1
  have hBt : 0 < sz.Bctl n (t n) := STBctl_pos sz n hxt
  have hlow := st_BI_lower sz hst hxt (hreg.2 n) hlam
  have hA0 : 0 < sz.STAI n := lt_of_lt_of_le one_pos hA
  have h2A : 0 < 2 * sz.STAI n := by positivity
  have hB : sz.Bctl n (t n) ^ (-𝔠d) ≤ (2 * sz.STAI n) ^ 𝔠d := by
    calc sz.Bctl n (t n) ^ (-𝔠d) ≤ (1 / (2 * sz.STAI n)) ^ (-𝔠d) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
      _ = (2 * sz.STAI n) ^ 𝔠d := by
          rw [one_div, Real.inv_rpow h2A.le, Real.rpow_neg h2A.le, inv_inv]
  refine st_psi_core hr hA hρ0 (by positivity) (hρ.trans (hB.trans_eq ?_))
  rw [Real.mul_rpow (by norm_num) hA0.le]

/-- **The `Ψ`-bound `hscale`, case (ii)** (`(eq:psipara_smalletacase)` `3_5:1577`), `A = (W^{-d}B_{s,0})⁻¹`: from
`(con_st_ind)`, `t < 1`, `|E| < 2`, `𝔠d > 0` (the regime `STCaseII` is not used: it enters through `A` only).
`η_s/η_u ≤ B_t^{-𝔠d} ≤ B_s^{-𝔠d} = A^{𝔠d}` (`STBctl_mono`), and `A ≥ 1` because `B_s ≤ B_t < 1`; `c = 2`. -/
theorem st_hscale_II {E s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAII s n) (etaT (E n) (s n) / etaT (E n) q.1.2) r (st_kmin 𝔠d r) ≤
        c * sz.STAII s n ^ (3 / 4 : ℝ) := by
  refine ⟨1 + (1 : ℝ) ^ (r - 1), by positivity, ?_⟩
  filter_upwards [hcon, st_con_aux sz h𝔠d hcon ht1] with n hn hW q
  obtain ⟨-, hBt1⟩ := hW
  have hsq : s n ≤ q.1.2 := q.2.1.trans q.2.2.1
  have hst : s n ≤ t n := hsq.trans q.2.2.2
  have hxt := ht1 n
  rw [RBM.Ind.scaleFacts_etaT_div_etaT (hE n)]
  have hρ0 : 0 ≤ (1 - s n) / (1 - q.1.2) :=
    div_nonneg (by linarith [q.2.2.2]) (by linarith [q.2.2.2])
  have hρ := st_rho_le sz hsq q.2.2.2 hxt hn.1
  have hBs : 0 < sz.Bctl n (s n) := STBctl_pos sz n (by linarith)
  have hmono : sz.Bctl n (s n) ≤ sz.Bctl n (t n) := STBctl_mono sz n hst hxt
  have hA : 1 ≤ sz.STAII s n := by
    unfold STAII
    exact (one_le_inv₀ hBs).2 (hmono.trans hBt1.le)
  have hB : sz.Bctl n (t n) ^ (-𝔠d) ≤ 1 * sz.STAII s n ^ 𝔠d := by
    rw [one_mul]
    calc sz.Bctl n (t n) ^ (-𝔠d) ≤ sz.Bctl n (s n) ^ (-𝔠d) :=
          Real.rpow_le_rpow_of_nonpos hBs hmono (by linarith)
      _ = sz.STAII s n ^ 𝔠d := by
          unfold STAII
          rw [Real.inv_rpow hBs.le, Real.rpow_neg hBs.le]
  exact st_psi_core hr hA hρ0 zero_le_one (hρ.trans hB)

/-- **`hscale` of `st_step3_skeleton`, case (i)**, in the exact form of the skeleton's hypothesis (`∃ k` before `∃ c`;
`A = fun n => STAI sz n`): `k = st_kmin 𝔠d r`. -/
theorem st_hscale_I' {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ} (h𝔠d : 0 < 𝔠d) (hreg : STRegIterI sz s t)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡) (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) :
    ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAI n) (etaT (E n) (s n) / etaT (E n) q.1.2) r k ≤ c * sz.STAI n ^ (3 / 4 : ℝ) :=
  fun r hr => ⟨st_kmin 𝔠d r, st_hscale_I sz h𝔠d hreg hcon hWO ht1 hE r hr⟩

/-- **`hscale` of `st_step3_skeleton`, case (ii)** (`A = fun n => STAII sz s n`), in the skeleton's exact form. -/
theorem st_hscale_II' {E s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hE : ∀ n, |E n| < 2) :
    ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAII s n) (etaT (E n) (s n) / etaT (E n) q.1.2) r k ≤ c * sz.STAII s n ^ (3 / 4 : ℝ) :=
  fun r hr => ⟨st_kmin 𝔠d r, st_hscale_II sz h𝔠d hcon ht1 hE r hr⟩

/-! ## 3. The bounds `hBA`: `W^{-d} B_{v,0} A^{3/4} ≤ c` -/

/-- **`hBA`, case (i)** (`A = ilambda² W^d`): under `STCaseI` (`1 - t ≥ ilambda²/L²`), `(eq:WO)` and `2 ≤ d`,
`W^{-d} B_{v,0} A^{3/4} ≤ 2` for all `v ∈ [s,t]`, eventually.
Proof: `1 - v ≥ 1 - t ≥ ilambda²/L² > 0`; `(ilambda² + 1 - v)⁻¹ ≤ ilambda⁻²` and
`(L^d (1-v))⁻¹ ≤ (L^{d-2} ilambda²)⁻¹ ≤ ilambda⁻²` (`L^d ≥ L²`, this is where `2 ≤ d` is used), so `B_v ≤ 2/A`;
`A ≥ 1` (`(eq:WO)`) gives `A^{3/4} ≤ A` and `B_v A^{3/4} ≤ 2`. -/
theorem st_hBA_I {s t : ℕ → ℝ} {𝔡 : ℝ} (hd : 2 ≤ d) (hcase : STCaseI sz s t) (hWO : sz.WO 𝔡) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      sz.Bctl n (v : ℝ) * sz.STAI n ^ (3 / 4 : ℝ) ≤ c := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [st_WO_AI sz hWO] with n hW v
  obtain ⟨hlam, hA⟩ := hW
  have hvt : (v : ℝ) ≤ t n := (v.2).2
  have hcn := hcase n
  have hg : 0 < sz.lam n ^ 2 := by positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hLd2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have hq : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have hxv : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - (v : ℝ) := by linarith
  have hx : 0 < 1 - (v : ℝ) := lt_of_lt_of_le hq hxv
  -- `g² ≤ L^d (1 - v)`
  have hgL : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (1 - (v : ℝ)) := by
    have h1 : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - (v : ℝ)) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2)).1 hxv
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hLd2 hx.le)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hBv : sz.Bctl n (v : ℝ) ≤ 2 * (sz.STAI n)⁻¹ := by
    unfold Sizes.Bctl Bparam STAI
    rw [abs_of_pos hx]
    have hz : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by norm_num
    simp only [hz, inv_one, mul_one]
    have h1 : (sz.lam n ^ 2 + (1 - (v : ℝ)))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ :=
      inv_anti₀ hg (by linarith)
    have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - (v : ℝ)))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ :=
      inv_anti₀ hg hgL
    calc ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ((sz.lam n ^ 2 + (1 - (v : ℝ)))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - (v : ℝ)))⁻¹)
        ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ((sz.lam n ^ 2)⁻¹ + (sz.lam n ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
      _ = 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
          rw [mul_inv]; ring
  have hA0 : 0 < sz.STAI n := lt_of_lt_of_le one_pos hA
  have hAle : sz.STAI n ^ (3 / 4 : ℝ) ≤ sz.STAI n := by
    calc sz.STAI n ^ (3 / 4 : ℝ) ≤ sz.STAI n ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
      _ = sz.STAI n := Real.rpow_one _
  calc sz.Bctl n (v : ℝ) * sz.STAI n ^ (3 / 4 : ℝ)
      ≤ (2 * (sz.STAI n)⁻¹) * sz.STAI n ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hBv (Real.rpow_nonneg hA0.le _)
    _ ≤ (2 * (sz.STAI n)⁻¹) * sz.STAI n :=
        mul_le_mul_of_nonneg_left hAle (by positivity)
    _ = 2 := by field_simp

/-- **`hBA`, case (ii)** (`A = (W^{-d}B_{s,0})⁻¹`): from `(con_st_ind)`, `t < 1` and `0 < 𝔠d ≤ 1/4`,
`W^{-d} B_{v,0} A^{3/4} ≤ 1` for all `v ∈ [s,t]`, eventually.
Proof: `scaleFacts_R2` gives `B_v ≤ B_s^{1-𝔠d}`; `A^{3/4} = B_s^{-3/4}`, so the product is `≤ B_s^{1/4-𝔠d} ≤ 1`
because `B_s ≤ B_t < 1` (`(con_st_ind)`: `B_t^{𝔠d} ≤ (1-t)/(1-s) < 1`) and `1/4 - 𝔠d ≥ 0`.  No range hypothesis
`N^{-1+τ} ≤ 1 - t` of `scaleFacts_R1` is needed: `Bctl < 1` comes from `(con_st_ind)`. -/
theorem st_hBA_II {s t : ℕ → ℝ} {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 4)
    (hcon : sz.STConStInd 𝔠d s t) (ht1 : ∀ n, t n < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n,
      sz.Bctl n (v : ℝ) * sz.STAII s n ^ (3 / 4 : ℝ) ≤ c := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [RBM.Ind.scaleFacts_R2 sz h𝔠d hcon (Eventually.of_forall ht1),
    st_con_aux sz h𝔠d hcon ht1] with n hR2 hW v
  obtain ⟨-, hBt1⟩ := hW
  have hsv : s n ≤ (v : ℝ) := (v.2).1
  have hvt : (v : ℝ) ≤ t n := (v.2).2
  have hst : s n ≤ t n := hsv.trans hvt
  have hBs : 0 < sz.Bctl n (s n) := STBctl_pos sz n (by linarith [ht1 n])
  have hBs1 : sz.Bctl n (s n) ≤ 1 :=
    (STBctl_mono sz n hst (ht1 n)).trans hBt1.le
  have hBv := hR2 (v : ℝ) hsv hvt
  have hA34 : sz.STAII s n ^ (3 / 4 : ℝ) = sz.Bctl n (s n) ^ (-(3 / 4 : ℝ)) := by
    unfold STAII
    rw [Real.inv_rpow hBs.le, Real.rpow_neg hBs.le]
  rw [hA34]
  calc sz.Bctl n (v : ℝ) * sz.Bctl n (s n) ^ (-(3 / 4 : ℝ))
      ≤ sz.Bctl n (s n) ^ (1 - 𝔠d) * sz.Bctl n (s n) ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hBv (Real.rpow_nonneg hBs.le _)
    _ = sz.Bctl n (s n) ^ (1 / 4 - 𝔠d) := by
        rw [← Real.rpow_add hBs]; congr 1; ring
    _ ≤ 1 := Real.rpow_le_one hBs.le hBs1 (by linarith)

/-! ## 4. The window `(1-t)/(1-s) ≥ W⁻¹` of `lem:sum_decay` -/

/-- `W → ∞` along an admissible sequence (`W ≥ N^𝔠` and `N → ∞`): the form in which the first component of the
composers' `STFlow sz κ ε 𝔠 𝔡 z` (`Admissible 𝔠 𝔡`) feeds `st_window`. -/
theorem scaleFacts3_W_tendsto {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hN, hB, -⟩ := hA
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  exact tendsto_atTop_mono' atTop hB h1

/-- **The window of `lem:sum_decay`** (`3_5:1633-1637`): `(con_st_ind)` with `d 𝔠d < 1` gives `(1-t)/(1-s) ≥ W⁻¹`,
eventually.  Proof: `(1-t)/(1-s) ≥ B_t^{𝔠d}` (`(con_st_ind)`) `≥ ((W^d)⁻¹ (ilambda²+1)⁻¹)^{𝔠d}` (`STBctl_ge`, `0 ≤ t`)
`= (W^{d𝔠d} (ilambda²+1)^{𝔠d})⁻¹ ≥ W⁻¹` iff `(ilambda²+1)^{𝔠d} ≤ W^{1-d𝔠d}`; the left side is `≤ (1 + 𝔡^{-2})^{𝔠d}` by
`(eq:WO)` (`ilambda ≤ 𝔡⁻¹`) and the right side tends to `∞` with `W` (`d 𝔠d < 1`).  Needs, besides the ticket's list,
`(eq:WO)` and `W → ∞` (`scaleFacts3_W_tendsto` from `Admissible`): without them the statement is false
(`W ≡ 1`, `(1-t)/(1-s) < 1`). -/
theorem st_window {𝔠d 𝔡 : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡)
    (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ)⁻¹ ≤ (1 - t n) / (1 - s n) := by
  have h𝔡 := st_WO_pos sz hWO
  have hexp : 0 < 1 - (d : ℝ) * 𝔠d := by linarith
  have hKev : ∀ᶠ n in atTop,
      (1 + (𝔡⁻¹) ^ 2) ^ 𝔠d ≤ ((sz.W n : ℕ) : ℝ) ^ (1 - (d : ℝ) * 𝔠d) :=
    ((tendsto_rpow_atTop hexp).comp hW).eventually_ge_atTop _
  filter_upwards [hcon, st_con_aux sz h𝔠d hcon ht1, hWO, hKev] with n hn hst hwo hK
  obtain ⟨h1, -⟩ := hn
  obtain ⟨hst', -⟩ := hst
  obtain ⟨hw1, hw2⟩ := hwo
  have hP0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlam0 : 0 ≤ sz.lam n := le_trans (Real.rpow_nonneg hP0.le _) hw1
  have hg2 : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ hlam0 hw2 2
  have hQ : (sz.lam n ^ 2 + 1) ^ 𝔠d ≤ (1 + (𝔡⁻¹) ^ 2) ^ 𝔠d :=
    Real.rpow_le_rpow (by positivity) (by linarith) h𝔠d.le
  have ht0 : 0 ≤ t n := (hs0 n).trans hst'.le
  have hBlow := STBctl_ge sz n ht0 (ht1 n)
  have hℓ0 : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ := by positivity
  have hpow := Real.rpow_le_rpow hℓ0 hBlow h𝔠d.le
  have hPd : (((sz.W n : ℕ) : ℝ) ^ d) ^ 𝔠d = ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * 𝔠d) := by
    rw [← Real.rpow_natCast ((sz.W n : ℕ) : ℝ) d, ← Real.rpow_mul hP0.le]
  have hℓc : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹) ^ 𝔠d =
      (((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * 𝔠d) * (sz.lam n ^ 2 + 1) ^ 𝔠d)⁻¹ := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
      Real.inv_rpow (by positivity), hPd, mul_inv]
  have hPQ : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * 𝔠d) * (sz.lam n ^ 2 + 1) ^ 𝔠d ≤ ((sz.W n : ℕ) : ℝ) := by
    calc ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * 𝔠d) * (sz.lam n ^ 2 + 1) ^ 𝔠d
        ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * 𝔠d) * ((sz.W n : ℕ) : ℝ) ^ (1 - (d : ℝ) * 𝔠d) :=
          mul_le_mul_of_nonneg_left (hQ.trans hK) (Real.rpow_nonneg hP0.le _)
      _ = ((sz.W n : ℕ) : ℝ) := by rw [← Real.rpow_add hP0]; simp
  calc ((sz.W n : ℕ) : ℝ)⁻¹
      ≤ (((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * 𝔠d) * (sz.lam n ^ 2 + 1) ^ 𝔠d)⁻¹ :=
        inv_anti₀ (by positivity) hPQ
    _ = ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹) ^ 𝔠d := hℓc.symm
    _ ≤ sz.Bctl n (t n) ^ 𝔠d := hpow
    _ ≤ (1 - t n) / (1 - s n) := h1

/-- **The merged `STEKWin`** (`lem:sum_decay` window, `3_5:1633`): `0 ≤ s ≤ t`, case (i) (`STCaseI`, i.e.
`t ≤ 1 - ilambda²/L²`), `t < 1` and `(1-t)/(1-s) ≥ W⁻¹` (`st_window`). -/
theorem st_EKWin {𝔠d 𝔡 : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1)
    (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡)
    (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hcase : STCaseI sz s t) (ht1 : ∀ n, t n < 1) :
    STEKWin sz s t :=
  ⟨hs0, hst, fun n => by linarith [hcase n], ht1, st_window sz h𝔠d hdc hcon hWO hW hs0 ht1⟩

/-! ## 5. Regimes: sub-intervals and the split at the middle time `u = 1 - ilambda²/L²` -/

/-- **`(con_st_ind)` passes to a sub-interval**: from `[s,t]` to `[s',t']`, `s ≤ s' < t' ≤ t < 1`
(`B_{t'} ≤ B_t` by `STBctl_mono`, and `(1-t)/(1-s) ≤ (1-t')/(1-s')` because `1-t ≤ 1-t'`, `1-s' ≤ 1-s`).
The strict `s' < t'` is what keeps `(1-t')/(1-s') < 1`: an empty sub-interval has ratio `1`. -/
theorem st_conStInd_sub {𝔠d : ℝ} {s t s' t' : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (hs : ∀ n, s n ≤ s' n) (hst : ∀ n, s' n < t' n) (ht : ∀ n, t' n ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.STConStInd 𝔠d s' t' := by
  filter_upwards [hcon] with n hn
  obtain ⟨h1, -⟩ := hn
  have hxt : 0 < 1 - t n := by linarith [ht1 n]
  have hxt' : 0 < 1 - t' n := by linarith [ht n]
  have hxs' : 0 < 1 - s' n := by linarith [hst n]
  have hxs : 0 < 1 - s n := by linarith [hs n]
  have hmono : sz.Bctl n (t' n) ≤ sz.Bctl n (t n) := STBctl_mono sz n (ht n) (ht1 n)
  have hB' : 0 ≤ sz.Bctl n (t' n) := (STBctl_pos sz n (by linarith [ht1 n, ht n])).le
  refine ⟨?_, (div_lt_one hxs').2 (by linarith [hst n])⟩
  calc sz.Bctl n (t' n) ^ 𝔠d ≤ sz.Bctl n (t n) ^ 𝔠d := Real.rpow_le_rpow hB' hmono h𝔠d.le
    _ ≤ (1 - t n) / (1 - s n) := h1
    _ ≤ (1 - t' n) / (1 - s' n) := by
        rw [div_le_div_iff₀ hxs hxs']
        nlinarith [hs n, ht n]

/-- **The split at `u = 1 - ilambda²/L²`, first part** (`3_5:1104-1105`): on `[s, min(t,u)]` the regime is `STCaseI`
(`1 - min(t,u) ≥ 1 - u = ilambda²/L²`) and `(con_st_ind)` holds, for the sequences `n ↦ min (t n) (u n)`.
`s_n < t_n` and `s_n < u_n` for all `n` keep the window `[s_n, min(t_n,u_n)]` nonempty (at `s_n = u_n` it would be a
point and `(con_st_ind)`, which needs `(1-t')/(1-s') < 1`, would fail; the statement does not cover that endpoint). -/
theorem st_split_I {𝔠d : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hst : ∀ n, s n < t n)
    (hsu : ∀ n, s n < 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) :
    STCaseI sz s (fun n => min (t n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) ∧
      sz.STConStInd 𝔠d s (fun n => min (t n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) := by
  refine ⟨fun n => ?_, st_conStInd_sub sz h𝔠d hcon (fun n => le_rfl)
    (fun n => lt_min (hst n) (hsu n)) (fun n => min_le_left _ _) ht1⟩
  have := min_le_right (t n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
  dsimp only
  linarith

/-- **The split at `u = 1 - ilambda²/L²`, second part** (`3_5:1104-1105`): on `[max(s,u), t]` the regime is `STCaseII`
(`1 - max(s,u) ≤ 1 - u = ilambda²/L²`) and `(con_st_ind)` holds, for the sequences `n ↦ max (s n) (u n)`.
`s_n < t_n` and `u_n < t_n` for all `n` keep the window nonempty (at `u_n = t_n` it would be a point). -/
theorem st_split_II {𝔠d : ℝ} {s t : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ n, t n < 1) (hst : ∀ n, s n < t n)
    (hut : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < t n) :
    STCaseII sz (fun n => max (s n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) t ∧
      sz.STConStInd 𝔠d (fun n => max (s n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)) t := by
  refine ⟨fun n => ?_, st_conStInd_sub sz h𝔠d hcon (fun n => le_max_left _ _)
    (fun n => max_lt (hst n) (hut n)) (fun n => le_rfl) ht1⟩
  have := le_max_right (s n) (1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
  dsimp only
  linarith

end RBM.Gauss.Sizes

/-! ## 6. Instances at `d = 3`

Every deterministic hypothesis is discharged.  `szB` is the merged second size sequence (`L = 4`, `W_n = n + 4`,
`ilambda = 1`, `RBM.Gauss.Step34Inst.szB`) with the flow `zB` (`E n = lemE (zB n)`, `|E n| < 2`); case (i) at
`(s,t) = (7/8, 15/16)` (`STRegIterI szB`: `1 - s = 1/8 ≤ ilambda² = 1`, `1 - t = ilambda²/L² = 1/16`), case (ii) at
`(15/16, 31/32)` (`STCaseII`: `1 - s = ilambda²/L² = 1/16`), `𝔠d = 1/100` (`(con_st_ind)` holds eventually for every
`𝔠d > 0`, `conStInd_const`).  The window instances are at `sz0` with the merged `sInst = 0`, `tInst = 1/16`. -/

namespace RBM.Gauss.ScaleFacts3Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Path Filter

private theorem zB_abs_E (n : ℕ) : |STflowE zB n| < 2 := abs_lemE_lt_two (by simp [zB])

private theorem szB_conI {𝔠d : ℝ} (h : 0 < 𝔠d) :
    szB.STConStInd 𝔠d (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h

private theorem szB_conII {𝔠d : ℝ} (h : 0 < 𝔠d) :
    szB.STConStInd 𝔠d (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h

/-- The depths `k_min` at `𝔠d = 1/100` (`r = 2, 3, 10, 50, 100`; `2 + 8 𝔠d (r-1) = 2.08, 2.16, 2.72, 5.92, 9.92`). -/
example : st_kmin (1 / 100) 2 = 3 ∧ st_kmin (1 / 100) 3 = 3 ∧ st_kmin (1 / 100) 10 = 3 ∧
    st_kmin (1 / 100) 50 = 6 ∧ st_kmin (1 / 100) 100 = 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [st_kmin, Nat.floor_eq_iff]

/-- Item 1, case (i): `st_hscale_I` and `st_hscale_I'` at `(szB, zB, 7/8, 15/16)`, `𝔠d = 1/100`, `𝔡 = 1/10`. -/
example (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n,
      STPsi (szB.STAI n) (etaT (STflowE zB n) (7 / 8) / etaT (STflowE zB n) q.1.2) r
          (st_kmin (1 / 100) r) ≤ c * szB.STAI n ^ (3 / 4 : ℝ) :=
  st_hscale_I szB (E := STflowE zB) (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) szB_regIterI
    (szB_conI (by norm_num)) szB_WO (fun _ => by norm_num) zB_abs_E r hr

example : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
    ∀ q : STPair (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n,
      STPsi (szB.STAI n) (etaT (STflowE zB n) (7 / 8) / etaT (STflowE zB n) q.1.2) r k ≤
        c * szB.STAI n ^ (3 / 4 : ℝ) :=
  st_hscale_I' szB (E := STflowE zB) (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) szB_regIterI
    (szB_conI (by norm_num)) szB_WO (fun _ => by norm_num) zB_abs_E

/-- Item 2, case (ii): `st_hscale_II` and `st_hscale_II'` at `(szB, zB, 15/16, 31/32)`, `𝔠d = 1/100`. -/
example (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair (fun _ => (15 / 16 : ℝ)) (fun _ => 31 / 32) n,
      STPsi (szB.STAII (fun _ => 15 / 16) n)
          (etaT (STflowE zB n) (15 / 16) / etaT (STflowE zB n) q.1.2) r (st_kmin (1 / 100) r) ≤
        c * szB.STAII (fun _ => 15 / 16) n ^ (3 / 4 : ℝ) :=
  st_hscale_II szB (E := STflowE zB) (𝔠d := 1 / 100) (by norm_num) (szB_conII (by norm_num))
    (fun _ => by norm_num) zB_abs_E r hr

example : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
    ∀ q : STPair (fun _ => (15 / 16 : ℝ)) (fun _ => 31 / 32) n,
      STPsi (szB.STAII (fun _ => 15 / 16) n)
          (etaT (STflowE zB n) (15 / 16) / etaT (STflowE zB n) q.1.2) r k ≤
        c * szB.STAII (fun _ => 15 / 16) n ^ (3 / 4 : ℝ) :=
  st_hscale_II' szB (E := STflowE zB) (𝔠d := 1 / 100) (by norm_num) (szB_conII (by norm_num))
    (fun _ => by norm_num) zB_abs_E

/-- Item 3: `st_hBA_I` at `(szB, 7/8, 15/16)` (`d = 3 ≥ 2`) and `st_hBA_II` at `(szB, 15/16, 31/32)`, `𝔠d = 1/100 ≤ 1/4`. -/
example : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
    ∀ v : TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n,
      szB.Bctl n (v : ℝ) * szB.STAI n ^ (3 / 4 : ℝ) ≤ c :=
  st_hBA_I szB (𝔡 := 1 / 10) (by norm_num) szB_regIterI.1 szB_WO

example : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
    ∀ v : TimeIcc (fun _ => (15 / 16 : ℝ)) (fun _ => 31 / 32) n,
      szB.Bctl n (v : ℝ) * szB.STAII (fun _ => 15 / 16) n ^ (3 / 4 : ℝ) ≤ c :=
  st_hBA_II szB (𝔠d := 1 / 100) (by norm_num) (by norm_num) (szB_conII (by norm_num))
    (fun _ => by norm_num)

/-- Item 4: `st_window` and `st_EKWin` at `sz0` with the merged `sInst = 0`, `tInst = 1/16` (`d = 3`, `𝔠d = 1/100`,
`d 𝔠d = 3/100 < 1`, `W → ∞`, `(eq:WO)` at `𝔡 = 1/10`); `W → ∞` also from `Admissible` (`scaleFacts3_W_tendsto`). -/
example : ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ)⁻¹ ≤ (1 - tInst n) / (1 - sInst n) :=
  st_window sz0 (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) (by norm_num) (sz0_con _ (by norm_num)) sz0_WO
    W_tendsto_sz0 sz0_hs0 (fun n => by simp only [tInst]; norm_num)

example : STEKWin sz0 sInst tInst :=
  st_EKWin sz0 (𝔠d := 1 / 100) (𝔡 := 1 / 10) (by norm_num) (by norm_num) (sz0_con _ (by norm_num)) sz0_WO
    (scaleFacts3_W_tendsto sz0 sz0_admissible) sz0_hs0 (fun n => (sz0_hst n).le) sz0_caseI
    (fun n => by simp only [tInst]; norm_num)

/-- Item 5: `st_conStInd_sub` from `[7/8, 15/16]` to `[29/32, 59/64]`; the split at `u = 1 - 1/16 = 15/16` of the
interval `[7/8, 31/32]` (`7/8 < u < 31/32`): `[7/8, min(31/32,u)] = [7/8, 15/16]` is case (i) and
`[max(7/8,u), 31/32] = [15/16, 31/32]` is case (ii), both with `(con_st_ind)`. -/
example : szB.STConStInd (1 / 100) (fun _ => 29 / 32) (fun _ => 59 / 64) :=
  st_conStInd_sub szB (by norm_num) (szB_conI (by norm_num)) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)

private theorem szB_con_wide : szB.STConStInd (1 / 100) (fun _ => 7 / 8) (fun _ => 31 / 32) :=
  conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)

example :=
  st_split_I szB (𝔠d := 1 / 100) (s := fun _ => 7 / 8) (t := fun _ => 31 / 32) (by norm_num) szB_con_wide
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => by simp [szB]; norm_num)

example :=
  st_split_II szB (𝔠d := 1 / 100) (s := fun _ => 7 / 8) (t := fun _ => 31 / 32) (by norm_num) szB_con_wide
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => by simp [szB]; norm_num)

/-- Item 6: the copied helpers at `szB`. -/
example : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((szB.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ szB.Bctl n u :=
  st_Bctl_ge szB (Λ := 1) (tendsto_size szB szB_tendsto)
    (Eventually.of_forall fun n => ⟨by simp [szB], by simp [szB]⟩)

example : STbootRHS 1 (fun _ => 1) (fun _ => 1) (1 / 2) 3 2 =
    (1 / 2 : ℝ) ^ (-(1 : ℝ) / (4 * ((2 : ℕ) : ℝ))) +
      (((Finset.Icc 1 (3 - 1)).card + (Finset.Icc (3 - 1) (3 + 1)).card +
        (Finset.Icc ((3 + 1) / 2 + 1) (3 - 1)).card : ℕ) : ℝ) :=
  st_bootRHS_one 1 (1 / 2) 3 2

example : ∀ k r, 2 ≤ r → 2 ≤ r + k :=
  st_iterate (S := fun r k => 2 ≤ r + k) (fun r hr => by omega) (fun n k hn _ _ _ => by omega)

end RBM.Gauss.ScaleFacts3Inst
