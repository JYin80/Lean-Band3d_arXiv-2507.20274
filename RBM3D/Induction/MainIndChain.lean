/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.MainIndBase
import RBM3D.Induction.LocalAvg1

/-!
# ST-6 R2 (ticket T2340): the chain of times from `lem:main_ind` to every `t_n > 0`

Design `docs/reports/T2338-design.md` §3, §4 (probe `RBM3D/Probe/T2338Pins.lean` on `t/T2338`, lines
61-67, 78-79, 175-254, 262-287, 319-336).  Paper `1_2:1194-1243`, `(con_st_ind)` `1_2:1296-1298`.

* `STHorizonG`: what the chain needs of a flow and its horizon `T0` (admissible sizes, `0 < T0 < 1`,
  `N^{-1+ε/2} ≤ 1 - T0` eventually); `stHorizon_band`: the band instance (`T0 = lemT z`);
* `stChainTime t K k`: `1 - p_k = (1 - t)^{k/K}` (`p_0 = 0`, `p_K = t`; RBM2D `chainTime`), with
  `stChainTime_zero`, `stChainTime_top` and the strict steps `stChainTime_facts` for `0 < t < 1`;
* `stChainSteps`: `(con_st_ind)` eventually at every step of the chain, for `K` fixed with
  `K 𝔠_d min(2𝔠𝔡, τ) ≥ 2` (`K` never depends on `n` or `t`);
* `STLocalMaxgL_of_STLocalEntrygL`: the closure of the induction (`‖G-M‖² ≺ W^{-d}B_{τ,K} ≤ Bctl`);
* `stPosConclG_of_mainIndG`: the six conclusions at every `0 < t_n ≤ T0`, by induction over the
  `K` steps.  `STBaseG` (R1) is the base of the induction.

Imports: `Induction.ScaleFacts` (`scaleFacts_R1`) and `Induction.Step2Iterate`
(`ST_one_sub_lemT`) are transitive through `Induction.MainIndBase` and are not repeated.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Ind

namespace RBM.BA

variable {d : ℕ}

/-! ## 1. The pins -/

/-- **R2 (horizon)**: what the chain needs of the flow and its horizon `T0`: admissible sizes,
`0 < T0 < 1`, and `N^{-1+ε/2} ≤ 1 - T0` eventually (band: `T0 = lemT z`, `1 - lemT z ≥ Im z/(1+|z|)`). -/
def STHorizonG (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
    sz.Admissible 𝔠 𝔡 ∧ (∀ n, 0 < T0 sz z n ∧ T0 sz z n < 1) ∧
      ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ 1 - T0 sz z n

/-- The geometric chain `1 - p_k = (1 - t)^{k/K}`: `p_0 = 0`, `p_K = t`
(RBM2D `chainTime`, `Induction/Defs.lean:318` at `c9a24cf`). -/
noncomputable def stChainTime (t : ℕ → ℝ) (K k : ℕ) : ℕ → ℝ := fun n => 1 - (1 - t n) ^ ((k : ℝ) / K)

/-! ## 2. The chain times and `(con_st_ind)` at every step (the exponent count) -/

theorem stChainTime_zero (t : ℕ → ℝ) (K : ℕ) : stChainTime t K 0 = fun _ => 0 := by
  funext n; simp [stChainTime]

theorem stChainTime_top (t : ℕ → ℝ) {K : ℕ} (hK : 0 < K) : stChainTime t K K = t := by
  funext n; simp [stChainTime, div_self (Nat.cast_ne_zero.2 hK.ne' : (K : ℝ) ≠ 0)]

/-- `0 ≤ p_k < p_{k+1} ≤ t` for `k < K`, `0 < t < 1`: the steps are strict exactly because `t_n > 0`. -/
theorem stChainTime_facts {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n) (ht1 : ∀ n, t n < 1) {K k : ℕ} (hK : 0 < K)
    (hk : k < K) (n : ℕ) : 0 ≤ stChainTime t K k n ∧ stChainTime t K k n < stChainTime t K (k + 1) n ∧
      stChainTime t K (k + 1) n ≤ t n := by
  have hx0 : 0 < 1 - t n := by linarith [ht1 n]
  have hx1 : 1 - t n < 1 := by linarith [ht0 n]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hle : ((k + 1 : ℕ) : ℝ) / K ≤ 1 := by rw [div_le_one hK0]; exact_mod_cast hk
  have hlt : (k : ℝ) / K < ((k + 1 : ℕ) : ℝ) / K := div_lt_div_of_pos_right (by push_cast; linarith) hK0
  have a := Real.rpow_le_one hx0.le hx1.le (div_nonneg (Nat.cast_nonneg k) hK0.le)
  have b := Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hlt
  have c := Real.self_le_rpow_of_le_one hx0.le hx1.le hle
  simp only [stChainTime]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **The chain-step count**: if `K · 𝔠_d · min(2𝔠𝔡, τ) ≥ 2`, then `(con_st_ind)` holds eventually at every
step `(p_k, p_{k+1})` of the chain to any `0 < t_n ≤ T_n`, where `N^{-1+τ} ≤ 1 - T_n`.  Proof:
`W^{-d}B_{u,0} ≤ 2N^{-μ}` (`scaleFacts_R1`, `μ = min(2𝔠𝔡, τ)`) and
`(1-p_{k+1})/(1-p_k) = (1-t)^{1/K} ≥ N^{-1/K}`; `K` does not depend on `n`. -/
theorem stChainSteps (sz : Sizes d) {𝔠 𝔡 τ 𝔠d : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (hτ : 0 < τ) (h𝔠d : 0 < 𝔠d)
    {K : ℕ} (hK : 2 ≤ (K : ℝ) * (𝔠d * min (2 * 𝔠 * 𝔡) τ)) (hB : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hsz : sz.SizeTendsto) {T : ℕ → ℝ} (hT1 : ∀ n, T n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - T n)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n) (htT : ∀ n, t n ≤ T n) {k : ℕ} (hk : k < K) :
    sz.STConStInd 𝔠d (stChainTime t K k) (stChainTime t K (k + 1)) := by
  set μ : ℝ := min (2 * 𝔠 * 𝔡) τ
  have hμ : 0 < μ := lt_min (by positivity) hτ
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hN : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsz
  filter_upwards [scaleFacts_R1 sz 𝔠 𝔡 τ T h𝔡 hB hWO hrange, hrange,
    ((tendsto_rpow_atTop (by positivity : 0 < 𝔠d * μ / 2)).comp hN).eventually_ge_atTop ((2 : ℝ) ^ 𝔠d),
    hN.eventually_ge_atTop 1] with n hR hr hb hN1
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hx0 : 0 < 1 - t n := by linarith [htT n, hT1 n]
  have hx1 : 1 - t n < 1 := by linarith [ht0 n]
  have e1 : ∀ j : ℕ, 1 - stChainTime t K j n = (1 - t n) ^ ((j : ℝ) / K) := fun j => by simp [stChainTime]
  have hratio : (1 - stChainTime t K (k + 1) n) / (1 - stChainTime t K k n) = (1 - t n) ^ ((1 : ℝ) / K) := by
    rw [e1, e1, ← Real.rpow_sub hx0]; congr 1; push_cast; ring
  have hp := (stChainTime_facts ht0 (fun n => (htT n).trans_lt (hT1 n)) (by omega) hk n).2.2
  refine ⟨?_, by rw [hratio]; exact Real.rpow_lt_one hx0.le hx1 (by positivity)⟩
  rw [hratio]
  have h1 : (sz.Bctl n (stChainTime t K (k + 1) n)) ^ 𝔠d ≤ (2 * ((sz.size n : ℕ) : ℝ) ^ (-μ)) ^ 𝔠d :=
    Real.rpow_le_rpow (mainIndBase_bctl_nonneg n _) (hR _ (hp.trans (htT n))) h𝔠d.le
  have h2 : (2 * ((sz.size n : ℕ) : ℝ) ^ (-μ)) ^ 𝔠d = 2 ^ 𝔠d * ((sz.size n : ℕ) : ℝ) ^ (-(μ * 𝔠d)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0.le _), ← Real.rpow_mul hN0.le]; congr 2; ring
  have h3 : 2 ^ 𝔠d * ((sz.size n : ℕ) : ℝ) ^ (-(μ * 𝔠d)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ) / K) := by
    have hb' : (2 : ℝ) ^ 𝔠d ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠d * μ / 2) := hb
    have h4 := mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hN0.le (-(μ * 𝔠d)))
    rw [← Real.rpow_add hN0] at h4
    refine h4.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
    have : (1 : ℝ) / K ≤ 𝔠d * μ / 2 := by rw [div_le_iff₀ hK0]; nlinarith
    have e : (-1 : ℝ) / K = -(1 / K) := by ring
    rw [e]; linarith
  have h5 : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ) / K) ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 + τ)) ^ ((1 : ℝ) / K) := by
    rw [← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : 0 ≤ τ / (K : ℝ) := by positivity
    have e : (-1 + τ) * (1 / (K : ℝ)) = -1 / K + τ / K := by ring
    rw [e]; linarith
  exact h1.trans (h2 ▸ h3.trans (h5.trans (Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _)
    (hr.trans (by linarith [htT n])) (by positivity))))

/-- **R2 (closure of the induction), generic**: `‖G-M‖² ≺ W^{-d}B_{τ,K} ≤ Bctl` (`(Gt_bound)`), so
`‖G-M‖ ≺ Bctl^{1/2}` (`(Gt_bound+IND)`): the twin of the merged band theorem
`STLocalMax_of_STLocalEntry` (`MainIndRegimes.lean:244`). -/
theorem STLocalMaxgL_of_STLocalEntrygL {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ)
    (h : STLocalEntrygL C μ τ) : STLocalMaxgL C μ τ :=
  StochDomAt.of_subset h fun σ hσ => ⟨2 * σ, by positivity, Eventually.of_forall fun n ω ⟨p, hp⟩ => ⟨p, by
    have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hB := mainIndBase_bctl_nonneg (sz := sz) n (τ n)
    have e : (((sz.size n : ℕ) : ℝ) ^ σ * sz.Bctl n (τ n) ^ (1 / 2 : ℝ)) ^ 2 =
        ((sz.size n : ℕ) : ℝ) ^ (2 * σ) * sz.Bctl n (τ n) := by
      rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hB, ← Real.rpow_natCast, ← Real.rpow_mul hN,
        Nat.cast_ofNat, mul_comm σ 2, mul_comm]
    calc ((sz.size n : ℕ) : ℝ) ^ (2 * σ) * STWB sz n (τ n) _ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * σ) * sz.Bctl n (τ n) :=
          mul_le_mul_of_nonneg_left (localAvg1_STWB_le sz n (τ n) _) (Real.rpow_nonneg hN _)
      _ = _ := e.symm
      _ < _ := pow_lt_pow_left₀ hp (mul_nonneg (Real.rpow_nonneg hN _) (Real.rpow_nonneg hB _)) two_ne_zero⟩⟩

/-! ## 3. The conclusions at every `t_n > 0` (induction over the chain) -/

section Assembly
variable {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
  {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}

/-- **R2**: the conclusions at every strictly positive `t_n ≤ T0`, by induction over the `K` chain steps
(`K` fixed by `𝔠_d`, `𝔠`, `𝔡`, `ε`; the base of the induction is `STBaseG`). -/
theorem stPosConclG_of_mainIndG (hmain : STMainIndG d law Flow mk T0) (hhor : STHorizonG d Flow T0)
    (hbase : STBaseG d law Flow mk) :
    3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → (∀ n, t n ≤ T0 sz z n) → STConclgL (mk sz z) (law sz) t := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf t ht0 htT
  obtain ⟨𝔠d, h𝔠d, -, H⟩ := hmain hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨⟨h𝔠, -, hsz, hbw, hWO⟩, hT, hr⟩ := hhor κ ε 𝔠 𝔡 sz z hκ hε hf
  have hμ : 0 < 𝔠d * min (2 * 𝔠 * 𝔡) (ε / 2) := mul_pos h𝔠d (lt_min (by have := h𝔡; positivity) (half_pos hε))
  obtain ⟨K, hK⟩ := exists_nat_ge (2 / (𝔠d * min (2 * 𝔠 * 𝔡) (ε / 2)))
  rw [div_le_iff₀ hμ] at hK
  have hK0 : 0 < K := Nat.pos_of_ne_zero fun h0 => by subst h0; norm_num at hK
  have key : ∀ k ≤ K, STConclgL (mk sz z) (law sz) (stChainTime t K k) := by
    intro k
    induction k with
    | zero => intro _; rw [stChainTime_zero]; exact hbase hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hf' := stChainTime_facts ht0 (fun n => (htT n).trans_lt (hT n).2) hK0 (by omega : k < K)
      exact H 𝔠 sz z hf _ _ (fun n => (hf' n).1) (fun n => ((hf' n).2.1.le.trans (hf' n).2.2).trans (htT n))
        (fun n => (hf' n).2.1) (fun n => (hf' n).2.2.trans (htT n))
        ⟨ih'.1, ih'.2.2.1, ih'.2.2.2.2.2, STLocalMaxgL_of_STLocalEntrygL _ _ _ ih'.2.2.2.2.1, ih'.2.2.2.1⟩
        (stChainSteps sz h𝔠 h𝔡 (half_pos hε) h𝔠d hK hbw hWO hsz (fun n => (hT n).2) hr ht0 htT (by omega))
  rw [← stChainTime_top t hK0]
  exact key K le_rfl

end Assembly

/-! ## 4. The band horizon -/

/-- Band horizon: `0 < lemT z < 1` and
`1 - lemT z ≥ Im z/(1+|z|) ≥ Im z/4 ≥ N^{-1+ε}/4 ≥ N^{-1+ε/2}`. -/
theorem stHorizon_band (d : ℕ) :
    STHorizonG d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n)) := by
  intro κ ε 𝔠 𝔡 sz z hκ hε hf
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hf.2 n).2.1
  refine ⟨hf.1, fun n => ⟨lemT_pos (him n), lemT_lt_one (him n)⟩, ?_⟩
  have hN : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hf.1.2.2.1
  filter_upwards [((tendsto_rpow_atTop (half_pos hε)).comp hN).eventually_ge_atTop 4,
    hN.eventually_ge_atTop 1] with n h4 hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hnorm : ‖z n‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im (z n); rw [abs_of_pos (him n)] at this
    linarith [(hf.2 n).1, (hf.2 n).2.2]
  have h2 : (z n).im / 4 ≤ (z n).im / (1 + ‖z n‖) :=
    div_le_div_of_nonneg_left (him n).le (by positivity) (by linarith)
  have e : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) =
      ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) * ((sz.size n : ℕ) : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have h3 := mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) from h4)
    (Real.rpow_nonneg hN0.le (-1 + ε / 2))
  change _ ≤ 1 - lemT (z n)
  linarith [(hf.2 n).2.1, ST_one_sub_lemT (him n)]

end RBM.BA

/-! ## 5. Compiled nonempty instances (`d = 3`, merged data `sz0`, `z0`) -/

namespace RBM.Gauss.MainIndInst

open RBM.BA RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `stChainTime_zero`, `stChainTime_top`, `stChainTime_facts` at `t = 1/2`, `K = 2`, `k = 1`: `p_0 = 0 < p_1 < p_2 = t`. -/
example : stChainTime (fun _ => 1 / 2) 2 0 = fun _ => 0 := stChainTime_zero _ 2

example : stChainTime (fun _ => 1 / 2) 2 2 = fun _ => 1 / 2 := stChainTime_top _ (by norm_num)

example (n : ℕ) : 0 ≤ stChainTime (fun _ => (1 / 2 : ℝ)) 2 1 n ∧
    stChainTime (fun _ => (1 / 2 : ℝ)) 2 1 n < stChainTime (fun _ => (1 / 2 : ℝ)) 2 2 n ∧
      stChainTime (fun _ => (1 / 2 : ℝ)) 2 2 n ≤ 1 / 2 :=
  stChainTime_facts (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num) (by norm_num) n

/-- `stHorizon_band` at the merged data `sz0`, `z0` (`d = 3`, `𝔠 = 1/6`, `κ = ε = 𝔡 = 1/10`). -/
example : sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, 0 < lemT (z0 n) ∧ lemT (z0 n) < 1) ∧
    ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-1 + (1 / 10 : ℝ) / 2) ≤ 1 - lemT (z0 n) :=
  stHorizon_band 3 (1 / 10) (1 / 10) (1 / 6) (1 / 10) sz0 z0 (by norm_num) (by norm_num) flow_z0

/-- `stChainSteps` at `sz0`, `z0` (`d = 3`, `𝔠 = 1/6`, `𝔡 = ε = 1/10`, `𝔠_d = 1/100`, `τ = ε/2`), `K = 6000`
(`K 𝔠_d min(2𝔠𝔡, τ) = 2`), `t = lemT z/2`, the last step `k = 5999`: every hypothesis is discharged. -/
example : sz0.STConStInd (1 / 100) (stChainTime (fun n => lemT (z0 n) / 2) 6000 5999)
    (stChainTime (fun n => lemT (z0 n) / 2) 6000 6000) := by
  obtain ⟨⟨-, -, hsz, hbw, hWO⟩, hT, hr⟩ :=
    stHorizon_band 3 (1 / 10) (1 / 10) (1 / 6) (1 / 10) sz0 z0 (by norm_num) (by norm_num) flow_z0
  exact stChainSteps sz0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (K := 6000)
    (by norm_num [min_def]) hbw hWO hsz (fun n => (hT n).2) hr (fun n => half_pos (hT n).1)
    (fun n => by linarith [(hT n).1]) (by norm_num)

/-- `STLocalMaxgL_of_STLocalEntrygL` at the band data and the zero sequence (the base case `stBase_band` supplies
`STLocalEntrygL`). -/
example : STLocalMaxgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) :=
  STLocalMaxgL_of_STLocalEntrygL _ _ _
    (stBase_band 3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num)
      sz0 z0 flow_z0).2.2.2.2.1

/-- `stPosConclG_of_mainIndG` at the band data and `t = lemT z/2 > 0`: the pin `STMainInd 3` (`lem:main_ind`, owed) is
a hypothesis; the horizon and the base case are proved (`stHorizon_band`, `stBase_band`). -/
example (hmain : STMainInd 3) :
    STConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun n => lemT (z0 n) / 2) :=
  stPosConclG_of_mainIndG ((STMainInd_iff 3).1 hmain) (stHorizon_band 3) (stBase_band 3) (by norm_num)
    (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 z0 flow_z0 _
    (fun n => half_pos (lemT_pos (z0_im_pos n))) (fun n => by linarith [lemT_pos (z0_im_pos n)])

end RBM.Gauss.MainIndInst
