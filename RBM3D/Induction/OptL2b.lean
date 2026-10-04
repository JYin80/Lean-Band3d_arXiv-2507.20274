/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.OptL2a

/-!
# ST2-15 (ticket T2116): `(eq:opt_L2)`, part 2: the linear Grönwall step and the pin `STOptL2`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `(eq:opt_L2)` `3_5:470`,
`(eq:Gronwall_2L_max)` `3_5:481`, `(eq:L-K2max)` `3_5:504–509`.  New; no port.

Target: `stOptL2_of_pins (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d`, the pin
`Induction/Step2Defs.lean:667` unchanged.  The Grönwall inequality on the grid is the merged
`stOptL2a_gronwall` (T2110); this file

1. restricts the premises of `STOptL2` on `[s,t]` to the window `[s,T]`, `T ≤ t` a time section
   (`OptL2b_loop_restrict`, `OptL2b_weak_restrict`, `OptL2b_con_restrict`; `STLK` is at `s` only);
2. runs `ST_gronwall` with `ST_prod_le_rpow` (`J_K ≤ α ρ_T^{C₀}`), compares with `B_T`
   (`OptL2b_arith`, the explicit `𝔠₀ = 1/(8 C₀ + 10)`), transfers the endpoint `k = K` from the grid
   walk to the single-time model (`ST_model_le_path`, `OptL2b_J_model_bad`) and passes to `PrecPT`
   (`ST_PT_of_sections`);
3. states the pin as written (`∃ 𝔠₀ > 0` before `𝔠_d`, the sequences, and `∀ᶠ n` inside).

`𝔠₀` depends on `C₀` only (`C₀` of `stOptL2a_gronwall`, a function of `d, κ, ε, 𝔡`).  The final
section holds compiled `example`s at `d = 3` (`sz0`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The arithmetic of `(eq:L-K2max)` -/

namespace RBM.Gauss.Sizes

/-- `ρ^p B^e ≤ B` from `ρ ≤ B^{-𝔠_d}`, `0 < B ≤ 1`, `p ≥ 0` and `1 + 𝔠_d p ≤ e`. -/
theorem OptL2b_rho_pow_mul {ρ B 𝔠d p e : ℝ} (hB0 : 0 < B) (hB1 : B ≤ 1) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ B ^ (-𝔠d)) (hp : 0 ≤ p) (he : 1 + 𝔠d * p ≤ e) : ρ ^ p * B ^ e ≤ B := by
  have h1 : ρ ^ p ≤ B ^ (-𝔠d * p) := by
    calc ρ ^ p ≤ (B ^ (-𝔠d)) ^ p := Real.rpow_le_rpow hρ0 hρ hp
      _ = B ^ (-𝔠d * p) := (Real.rpow_mul hB0.le _ _).symm
  calc ρ ^ p * B ^ e ≤ B ^ (-𝔠d * p) * B ^ e :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB0.le _)
    _ = B ^ (-𝔠d * p + e) := (Real.rpow_add hB0 _ _).symm
    _ ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hB0 hB1 (by linarith)
    _ = B := Real.rpow_one B

/-- **`(eq:L-K2max)` with the explicit `𝔠₀ = 1/(8C₀+10)`** (`3_5:504–509`): with `ρ = (1-s)/(1-T)`,
`λ = ρ B_T` and `ρ ≤ B_T^{-𝔠_d}` (the first conjunct of `(con_st_ind)`),
`M (B_s² + λ^{5/4}) ρ^{C₀} ≤ M² B_T` for `M ≥ 2`, `0 < B_s ≤ B_T ≤ 1`.  Terms: `ρ^{C₀} B_s² ≤ B_T`
(`C₀ 𝔠_d ≤ 1`) and `ρ^{C₀} λ^{5/4} ≤ B_T` (`𝔠_d (C₀ + 5/4) ≤ 1/4`). -/
theorem OptL2b_arith {C₀ 𝔠d ρ Bs BT M : ℝ} (hC₀ : 0 < C₀) (h𝔠d0 : 0 < 𝔠d)
    (h𝔠d : 𝔠d ≤ 1 / (8 * C₀ + 10)) (hBT0 : 0 < BT) (hBT1 : BT ≤ 1) (hBs0 : 0 ≤ Bs)
    (hBs : Bs ≤ BT) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ BT ^ (-𝔠d)) (hM : 2 ≤ M) :
    M * (Bs ^ 2 + (ρ * BT) ^ (5 / 4 : ℝ)) * ρ ^ C₀ ≤ M * M * BT := by
  have hρ0 : 0 < ρ := by linarith
  have hden : (0 : ℝ) < 8 * C₀ + 10 := by linarith
  have h8 : 𝔠d * (8 * C₀ + 10) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h𝔠d hden.le
    rwa [one_div, inv_mul_cancel₀ hden.ne'] at this
  have e1 : 𝔠d * C₀ ≤ 1 := by nlinarith
  have e2 : 1 + 𝔠d * (C₀ + 5 / 4) ≤ 5 / 4 := by nlinarith
  -- term 1: `ρ^{C₀} B_s² ≤ B_T`
  have t1 : ρ ^ C₀ * Bs ^ 2 ≤ BT := by
    have hB2 : Bs ^ 2 ≤ BT ^ (2 : ℝ) := by
      rw [Real.rpow_two]; exact pow_le_pow_left₀ hBs0 hBs 2
    calc ρ ^ C₀ * Bs ^ 2 ≤ ρ ^ C₀ * BT ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left hB2 (Real.rpow_nonneg hρ0.le _)
      _ ≤ BT := OptL2b_rho_pow_mul hBT0 hBT1 hρ0.le hρ hC₀.le (by linarith)
  -- term 2: `ρ^{C₀} λ^{5/4} ≤ B_T`
  have t2 : ρ ^ C₀ * (ρ * BT) ^ (5 / 4 : ℝ) ≤ BT := by
    have e : ρ ^ C₀ * (ρ * BT) ^ (5 / 4 : ℝ) = ρ ^ (C₀ + 5 / 4) * BT ^ (5 / 4 : ℝ) := by
      rw [Real.mul_rpow hρ0.le hBT0.le, ← mul_assoc, ← Real.rpow_add hρ0]
    rw [e]
    exact OptL2b_rho_pow_mul hBT0 hBT1 hρ0.le hρ (by linarith) e2
  have hM0 : 0 ≤ M := by linarith
  calc M * (Bs ^ 2 + (ρ * BT) ^ (5 / 4 : ℝ)) * ρ ^ C₀
      = M * (ρ ^ C₀ * Bs ^ 2 + ρ ^ C₀ * (ρ * BT) ^ (5 / 4 : ℝ)) := by ring
    _ ≤ M * (BT + BT) := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hM0
    _ ≤ M * M * BT := by nlinarith [mul_nonneg (mul_nonneg hM0 hBT0.le) (sub_nonneg.2 hM)]

end RBM.Gauss.Sizes

/-! ## 2. Restriction of the premises from `[s,t]` to `[s,T]`, `T ≤ t` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Restrict

variable {d : ℕ} (sz : Sizes d)

/-- `(lRB1)` on `[s,t]` gives `(lRB1)` on `[s,T]` for a pointwise smaller end `T ≤ t`:
`TimeIcc s T n ⊆ TimeIcc s t n`, the control does not depend on the end. -/
theorem OptL2b_loop_restrict {E s t T : ℕ → ℝ} (hTt : ∀ n, T n ≤ t n)
    (h : STStep1Loop sz E s t) : STStep1Loop sz E s T := by
  intro k hk
  have h' := h k hk
  unfold Prec at h' ⊢
  exact StochDomAt.precomp_param h'
    (fun n (p : TimeIcc s T n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) =>
      ((⟨p.1.1, p.1.2.1, (p.1.2.2).trans (hTt n)⟩ : TimeIcc s t n), p.2))

/-- `(Gtmwc)` on `[s,t]` gives `(Gtmwc)` on `[s,T]`, `T ≤ t`. -/
theorem OptL2b_weak_restrict {E s t T : ℕ → ℝ} (hTt : ∀ n, T n ≤ t n)
    (h : STStep1Weak sz E s t) : STStep1Weak sz E s T := by
  unfold STStep1Weak Prec at h ⊢
  exact StochDomAt.precomp_param h
    (fun n (p : TimeIcc s T n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      ((⟨p.1.1, p.1.2.1, (p.1.2.2).trans (hTt n)⟩ : TimeIcc s t n), p.2))

/-- The first conjunct of `(con_st_ind)` on `[s,t]` gives it on `[s,T]`, `s ≤ T ≤ t`, `𝔠_d > 0`
(`STBctl_mono`; the second conjunct fails at `T = s`). -/
theorem OptL2b_con_restrict {𝔠d : ℝ} {s t T : ℕ → ℝ} (h𝔠d : 0 < 𝔠d) (hsT : ∀ n, s n ≤ T n)
    (hTt : ∀ n, T n ≤ t n) (ht1 : ∀ n, t n < 1) (h : STConStInd sz 𝔠d s t) :
    ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n) := by
  filter_upwards [h] with n hn
  have hs1 : 0 < 1 - s n := by linarith [hsT n, hTt n, ht1 n]
  calc (sz.Bctl n (T n)) ^ 𝔠d ≤ (sz.Bctl n (t n)) ^ 𝔠d :=
        Real.rpow_le_rpow (STBctl_pos sz n (lt_of_le_of_lt (hTt n) (ht1 n))).le
          (STBctl_mono sz n (hTt n) (ht1 n)) h𝔠d.le
    _ ≤ (1 - t n) / (1 - s n) := hn.1
    _ ≤ (1 - T n) / (1 - s n) := div_le_div_of_nonneg_right (by linarith [hTt n]) hs1.le

end Restrict

end RBM.Gauss.Sizes

/-! ## 3. The maximum `J` and the failure event of the model -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section JModel

variable {d : ℕ} (sz : Sizes d)

/-- `J = max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}|` is a measurable function of the fine matrix. -/
theorem OptL2b_J_measurable (n : ℕ) (E u : ℝ) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      OptL2aJ sz n E u H) := by
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset (STLab sz n)))
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (f := fun (i : STLab sz n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖STLKM sz n E u H i.1 i.2‖) (fun i _ => (STLKM_measurable sz n E u i.1 i.2).norm)
  convert h using 1
  ext H
  have := Finset.sup'_apply (s := (Finset.univ : Finset (STLab sz n)))
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun (i : STLab sz n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖STLKM sz n E u H i.1 i.2‖) H
  exact this.symm

/-- The failure event of `Prec` at the section `T` (union over the labels inside) is the event
`N^τ B < J` of the single-time model. -/
theorem OptL2b_badSet_eq (n : ℕ) (E T τ B : ℝ) :
    {ω : sz.SeqΩ | ∃ v : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ τ * B <
        ‖Lloop sz n E T v.1 v.2 ω - STKloop sz n E T v.1 v.2‖} =
      {ω : sz.SeqΩ | ((sz.size n : ℕ) : ℝ) ^ τ * B < OptL2aJ sz n E T (sz.seqHflow n T ω)} := by
  ext ω
  change (∃ v : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ τ * B <
      ‖Lloop sz n E T v.1 v.2 ω - STKloop sz n E T v.1 v.2‖) ↔
    ((sz.size n : ℕ) : ℝ) ^ τ * B < OptL2aJ sz n E T (sz.seqHflow n T ω)
  unfold OptL2aJ
  refine Iff.trans ?_ (Finset.lt_sup'_iff (s := (Finset.univ : Finset (STLab sz n))) _).symm
  simp only [Finset.mem_univ, true_and]
  rfl

end JModel

end RBM.Gauss.Sizes

/-! ## 4. The pin `STOptL2` conditional on `STLWB`, `STGridMart` -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- **`(eq:opt_L2)`** (`3_5:470`, proof `3_5:466–512`), the pin `STOptL2`, from the light-weight pin
`STLWB` (`lem:LWterm`) and the grid martingale pin `STGridMart` (`lem:DIfREP`, `m = 2`); `lem:newKLK`
(`stNewKLK_holds`) and `lem: EMn2_N` (`stEMn2Poly_holds`) enter through `stOptL2a_gronwall` (T2110).
`𝔠₀ = 1/(8 C₀ + 10)`, `C₀` the constant of `stOptL2a_gronwall` (a function of `d, κ, ε, 𝔡`).  For every
time section `T_n ∈ [s_n, t_n]`: the Grönwall inequality on the grid `[s_n, T_n]`
(`stOptL2a_gronwall`, premises restricted to `[s,T]`), `ST_gronwall` with `ST_prod_le_rpow`
(`J_K ≤ α ρ_T^{C₀}`), the comparison `(eq:L-K2max)` (`OptL2b_arith`), the transfer of the endpoint to
the single-time model (`ST_model_le_path`), and `ST_PT_of_sections`.  `hd : 3 ≤ d` because
`STNewKLK d` starts with `3 ≤ d` (T2110f). -/
theorem stOptL2_of_pins {d : ℕ} (hd : 3 ≤ d) : STLWB d → STGridMart d → STOptL2 d := by
  classical
  intro hLWB hGM κ ε 𝔡 hκ hε h𝔡
  obtain ⟨C₀, hC₀, hG⟩ := stOptL2a_gronwall hd hLWB hGM κ ε 𝔡 hκ hε h𝔡
  have hd0 : 0 < d := by omega
  have hden : (0 : ℝ) < 8 * C₀ + 10 := by linarith
  refine ⟨1 / (8 * C₀ + 10), by positivity, ?_⟩
  intro 𝔠d h𝔠d0 h𝔠d 𝔠 sz z hflow s t hs hst htl hLK hcon hS1L hS1W
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hc12 : 𝔠d ≤ 1 / 2 := by
    refine h𝔠d.trans ?_
    rw [div_le_div_iff₀ hden (by norm_num)]
    linarith
  have ht1 : ∀ n, t n < 1 := fun n =>
    lt_of_le_of_lt (htl n) (lemT_lt_one (ST_flow_im_pos sz hflow n))
  obtain ⟨cB, hcB, hcd⟩ := OptL2a_sizedata hd0 hκ hε h𝔡
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  refine ST_PT_of_sections sz (V := fun n => STLab sz n) hst _ _ ?_
  intro tt
  -- the time section `T_n = tt n ∈ [s_n, t_n]`
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℝ, T = fun n => ((tt n : TimeIcc s t n) : ℝ) := ⟨_, rfl⟩
  have hsT : ∀ n, s n ≤ T n := fun n => by rw [hTdef]; exact (tt n).2.1
  have hTt : ∀ n, T n ≤ t n := fun n => by rw [hTdef]; exact (tt n).2.2
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hTl : ∀ n, T n ≤ lemT (z n) := fun n => (hTt n).trans (htl n)
  have hT1 : ∀ n, T n < 1 := fun n => lt_of_le_of_lt (hTt n) (ht1 n)
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  have hconT := OptL2b_con_restrict sz h𝔠d0 hsT hTt ht1 hcon
  have hS1LT := OptL2b_loop_restrict sz hTt hS1L
  have hS1WT := OptL2b_weak_restrict sz hTt hS1W
  have hBd := hBd0 sz z hflow T hT0 hTl
  intro τ' hτ' D hD
  obtain ⟨CK, hCK0, hK⟩ := hG 𝔠 sz z hflow s T hs hsT hTl hLK 𝔠d hc12 hconT hS1LT hS1WT (τ' / 2)
    (by positivity) D hD
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → ℕ, K = fun n => ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊ := ⟨_, rfl⟩
  have hKn : ∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊ := fun n => by rw [hKdef]
  have hK0 := (OptL2a_grid sz K hKn).1
  have hh := hK K hKn
  filter_upwards [hh, hsize.eventually (eventually_ge_atTop 1), hBd, hconT,
    ST_size_pow_big sz hsize (a := τ' / 2) (M := 2) (by positivity)] with n hn hN1 hbdn hconn hM
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hBT0 : 0 < sz.Bctl n (T n) := STBctl_pos sz n (hT1 n)
  have hBT1 : sz.Bctl n (T n) ≤ 1 :=
    (hbdn (T n) (hT0 n) le_rfl).2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  have hBs0 : 0 ≤ sz.Bctl n (s n) := (STBctl_pos sz n (hs1 n)).le
  have hBs : sz.Bctl n (s n) ≤ sz.Bctl n (T n) := STBctl_mono sz n (hsT n) (hT1 n)
  have hρ1 : 1 ≤ (1 - s n) / (1 - T n) := by
    rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
  have hρ : (1 - s n) / (1 - T n) ≤ (sz.Bctl n (T n)) ^ (-𝔠d) := by
    calc (1 - s n) / (1 - T n) = ((1 - T n) / (1 - s n))⁻¹ := (inv_div _ _).symm
      _ ≤ ((sz.Bctl n (T n)) ^ 𝔠d)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hBT0 _) hconn
      _ = (sz.Bctl n (T n)) ^ (-𝔠d) := (Real.rpow_neg hBT0.le _).symm
  have hΔ : 0 ≤ gridStep s T K n := ST_gridStep_nonneg s T K n (hsT n)
  have hMM : ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ' := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  -- the grid event is contained in the failure event of the grid inequality
  have hBad : {ω : PathΩ sz | ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n (T n) <
        OptL2aJ sz n (STflowE z n) (T n) (pathH sz s T K n (K n) ω)} ⊆
      {ω | ¬ ∀ k, k ≤ K n →
        OptL2aJ sz n (STflowE z n) (gridTime s T K n k) (pathH sz s T K n k ω) ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
              ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) +
            gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
              OptL2aJ sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω)} := by
    intro ω hω hall
    have hβ : ∀ j, j < K n → 0 ≤ C₀ / (1 - gridTime s T K n j) := fun j hj => by
      have hm := ST_gridTime_mem s T K n j (hsT n) (hK0 n) hj.le
      exact div_nonneg hC₀.le (by linarith [hm.2, hT1 n])
    have hGr := ST_gronwall (m := K n) (Δ := gridStep s T K n) hΔ
      (α := fun _ => ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
        ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)))
      (β := fun j => C₀ / (1 - gridTime s T K n j))
      (J := fun j => OptL2aJ sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω))
      monotoneOn_const hβ (fun k hk => hall k hk) (K n) le_rfl
    have hprod : ∏ j ∈ Finset.range (K n), (1 + gridStep s T K n * (C₀ / (1 - gridTime s T K n j))) ≤
        ((1 - s n) / (1 - T n)) ^ C₀ := by
      have hlast : s n + (K n : ℝ) * gridStep s T K n = T n := gridTime_last s T K n (hK0 n)
      have h := ST_prod_le_rpow (s := s n) (Δ := gridStep s T K n) (c := C₀) hΔ hC₀.le (k := K n)
        (by rw [hlast]; exact hT1 n)
      rw [hlast] at h
      refine le_trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)) h
      simp only [gridTime, div_eq_mul_inv]
    have hJK : OptL2aJ sz n (STflowE z n) (T n) (pathH sz s T K n (K n) ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
          ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) *
            ((1 - s n) / (1 - T n)) ^ C₀ := by
      have h1 : OptL2aJ sz n (STflowE z n) (gridTime s T K n (K n)) (pathH sz s T K n (K n) ω) ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
            ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) *
              ∏ j ∈ Finset.range (K n), (1 + gridStep s T K n * (C₀ / (1 - gridTime s T K n j))) :=
        hGr
      rw [gridTime_last s T K n (hK0 n)] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left hprod ?_)
      have : 0 ≤ OptL2alam sz s T n := mul_nonneg (by linarith) hBT0.le
      positivity
    have hA := OptL2b_arith (C₀ := C₀) (𝔠d := 𝔠d) hC₀ h𝔠d0 h𝔠d hBT0 hBT1 hBs0 hBs hρ1 hρ hM
    have hlam : OptL2alam sz s T n = (1 - s n) / (1 - T n) * sz.Bctl n (T n) := rfl
    rw [hlam] at hJK
    have hlt : ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n (T n) <
        OptL2aJ sz n (STflowE z n) (T n) (pathH sz s T K n (K n) ω) := hω
    rw [← hMM] at hlt
    exact absurd (hlt.trans_le (hJK.trans hA)) (lt_irrefl _)
  -- the transfer to the single-time model
  refine le_trans ?_ hn
  have hmodel := ST_model_le_path sz s T K hs hsT hK0 n
    (fun n u H => OptL2aJ sz n (STflowE z n) u H) (fun n u _ => sz.Bctl n u)
    (fun n u => OptL2b_J_measurable sz n (STflowE z n) u) (fun n u => measurable_const) τ'
    {ω | ¬ ∀ k, k ≤ K n →
      OptL2aJ sz n (STflowE z n) (gridTime s T K n k) (pathH sz s T K n k ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
            ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) +
          gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
            OptL2aJ sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω)} hBad
  have hset := OptL2b_badSet_eq sz n (STflowE z n) (T n) τ' (sz.Bctl n (T n))
  convert hmodel using 2
  rw [hTdef] at hset ⊢
  exact hset

end RBM.Gauss.Sizes

/-! ## Instances: every endpoint theorem at `d = 3`

The data are the merged `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`), the flow `z0` (`flow_z0`, `κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`, `Im z_n = N_n^{-4/5}`), the window `s ≡ 0`, `t ≡ 1/16 ≤ lemT z_n` (`sInst`, `tInst`),
every `0 < 𝔠_d ≤ 𝔠₀`.  Discharged: `3 ≤ d`, `STFlow`, the time ranges, and `(con_st_ind)`
(`conStInd_inst`).  What stays a hypothesis of an example is a pin of another gate (`STLWB`,
`STGridMart`) or a stochastic premise of the induction and of Step 1 (`STLK`, `STStep1Loop`,
`STStep1Weak`). -/

namespace RBM.Gauss.OptL2bInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2DefsInst RBM.Path Filter

/-- **`stOptL2_of_pins` at `d = 3`, read through the merged `inst_optL2`**. -/
example (hLWB : STLWB 3) (hGM : STGridMart 3) :
    ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep1Weak sz0 (STflowE z0) sInst tInst →
        PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => sz0.Bctl n (p.1 : ℝ))) :=
  inst_optL2 (stOptL2_of_pins (d := 3) (by norm_num) hLWB hGM)

/-- **`stOptL2_of_pins` at `d = 3`, applied directly** to `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`,
`s ≡ 0`, `t ≡ 1/16` (a window with `s < t`): `𝔠₀` is the constant of the pin, and for every
`0 < 𝔠_d ≤ 𝔠₀` the per-time bound `(eq:opt_L2)`
`max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| ≺ W^{-d} B_{u,0}` holds on the window, from `(con_st_ind)`
(discharged) and the three stochastic premises. -/
example (hLWB : STLWB 3) (hGM : STGridMart 3) :
    ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep1Weak sz0 (STflowE z0) sInst tInst →
        PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => sz0.Bctl n (p.1 : ℝ))) := by
  obtain ⟨𝔠₀, h0, hall⟩ := stOptL2_of_pins (d := 3) (by norm_num) hLWB hGM (1 / 10) (1 / 10)
    (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠₀, h0, fun 𝔠d h1 h2 hLK hS1L hS1W => hall 𝔠d h1 h2 (1 / 6) sz0 z0 flow_z0 sInst tInst
    (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n) hLK (conStInd_inst h1) hS1L hS1W⟩

/-- The restrictions at the data: the premises on `[0, 1/16]` give those on `[0, 1/32]`. -/
example (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
    (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst) :
    STStep1Loop sz0 (STflowE z0) sInst (fun _ => 1 / 32) ∧
      STStep1Weak sz0 (STflowE z0) sInst (fun _ => 1 / 32) ∧
      ∀ᶠ n in atTop, (sz0.Bctl n (1 / 32)) ^ (1 / 26 : ℝ) ≤ (1 - 1 / 32) / (1 - sInst n) :=
  ⟨OptL2b_loop_restrict sz0 (fun n => by simp only [tInst]; norm_num) hS1L,
    OptL2b_weak_restrict sz0 (fun n => by simp only [tInst]; norm_num) hS1W,
    OptL2b_con_restrict sz0 (T := fun _ => 1 / 32) (by norm_num) (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) (fun n => by simp only [tInst]; norm_num)
      (conStInd_inst (by norm_num : (0 : ℝ) < 1 / 26))⟩

/-- The arithmetic of `(eq:L-K2max)` at numbers: `C₀ = 2`, `𝔠_d = 1/26 = 1/(8 C₀ + 10)`,
`B_s = B_T = 1/10`, `ρ = 1` (`T = s`), `M = 2`. -/
example : (2 : ℝ) * ((1 / 10 : ℝ) ^ 2 + (1 * (1 / 10 : ℝ)) ^ (5 / 4 : ℝ)) * (1 : ℝ) ^ (2 : ℝ) ≤
    2 * 2 * (1 / 10 : ℝ) :=
  OptL2b_arith (C₀ := 2) (𝔠d := 1 / 26) (ρ := 1) (Bs := 1 / 10) (BT := 1 / 10) (M := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) (by norm_num))
    le_rfl

/-- The same at a time section after the start: `s = 0`, `T = 1/32`, `ρ = (1-s)/(1-T) = 32/31 > 1`,
`B_s = 1/20 < B_T = 1/10`, `ρ ≤ B_T^{-𝔠_d}`. -/
example : (2 : ℝ) * ((1 / 20 : ℝ) ^ 2 + (32 / 31 * (1 / 10 : ℝ)) ^ (5 / 4 : ℝ)) *
      (32 / 31 : ℝ) ^ (2 : ℝ) ≤ 2 * 2 * (1 / 10 : ℝ) := by
  have h1 : (1 / 10 : ℝ) ^ (-(1 / 26) : ℝ) = (10 : ℝ) ^ ((1 : ℝ) / 26) := by
    rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]
  have h2 : (32 / 31 : ℝ) = (((32 / 31 : ℝ) ^ (26 : ℕ)) ^ ((1 : ℝ) / 26)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hρ : (32 / 31 : ℝ) ≤ (1 / 10 : ℝ) ^ (-(1 / 26) : ℝ) := by
    rw [h1, h2]
    exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
  exact OptL2b_arith (C₀ := 2) (𝔠d := 1 / 26) (ρ := 32 / 31) (Bs := 1 / 20) (BT := 1 / 10) (M := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hρ le_rfl

end RBM.Gauss.OptL2bInst
