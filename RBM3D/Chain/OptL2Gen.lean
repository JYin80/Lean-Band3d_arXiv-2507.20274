/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2IterGen
import RBM3D.Induction.OptL2b

/-!
# (3.39) `eq:opt_L2` over the carrier

The band files `Induction/OptL2a`, `Induction/OptL2b` are restated over a carrier `Cm : Step2Mat sz` and a
law `μ` (`Cm.Pp`, `Cm.Hpath`, `Cm.eta`, `Cm.m`).  The model-free and size-level helpers are used by name
(`OptL2alam`, `OptL2aPsi`, `OptL2a_lam_*`, `OptL2a_floor`, `OptL2a_rho_le`, `OptL2a_w_pow`,
`OptL2a_mart_arith`, `OptL2a_alpha_arith`, `OptL2a_q_log_le`, `OptL2a_x_le`, `OptL2a_prob_combine`,
`OptL2a_grid`, `OptL2a_cards`, `OptL2b_rho_pow_mul`, `OptL2b_arith`, `OptL2b_con_restrict`).
No `BA/` import, no kernel is defined.

* `OptL2aJg` (the maximum `J`); `stOptL2a_driftg` ((3.40) `l>0EQ`: `lem:newKLK` at `ℓ = 0`, i.e.
  `Step2IterGen_NewKLKAtN`, and the light-weight statement `STLWBgL`); `stOptL2a_martingaleg`
  ((3.33) `eq:MG_conclusion`: `STEMn2PolygL`, and `STGridMartgL`); `stOptL2a_gronwallg` ((3.41)
  `eq:Gronwall_2L_max` on the grid, the form `ST_gronwall` consumes).
* `stOptL2_of_pinsg`: the statement `STOptL2gL` over a carrier family `(law, Flow, mk, T0)`.

The spectral data of the carrier is `DecayGen_Spec` (`κm ≤ Im m`, `η_t = (1 - t) Im m`); the constant
`q` of the band proof, `(√κ/2)⁻¹`, is `κm⁻¹`.  The carrier facts `Step2EventsGen_Flow` and
`Step2EventsGen_Grid`, the Hermitian walk and the size data `STBdatagL` replace `STFlow`,
`pathH_isHermitian`, `ST_Bdata_holds`.
-/

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The maximum `J` and the drift bound at one grid state -/

section Drift

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `J = max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}|` of a fine matrix `H`, over a carrier (band `OptL2aJ`). -/
def OptL2aJg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun i : STLab sz n => ‖STLKMg Cm n u H i.1 i.2‖)

private theorem OptL2Gen_J_ge (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (i : STLab sz n) : ‖STLKMg Cm n u H i.1 i.2‖ ≤ OptL2aJg Cm n u H :=
  Finset.le_sup' (fun i : STLab sz n => ‖STLKMg Cm n u H i.1 i.2‖) (Finset.mem_univ i)

private theorem OptL2Gen_J_nonneg (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : 0 ≤ OptL2aJg Cm n u H :=
  (norm_nonneg _).trans (OptL2Gen_J_ge Cm n u H ((fun _ => true), (fun _ => 0)))

private theorem OptL2Gen_J_le (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {B : ℝ} (h : ∀ i : STLab sz n, ‖STLKMg Cm n u H i.1 i.2‖ ≤ B) : OptL2aJg Cm n u H ≤ B :=
  Finset.sup'_le _ _ fun i _ => h i

/-- `Ĵ^0_{u,D} · W^{-d} 𝒯̃^0_{u,D} ≤ J` (band `OptL2a_Jhat_mul_le`). -/
private theorem OptL2Gen_Jhat_mul_le (n : ℕ) (D u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    STJhatMg Cm n D 0 u H * STprof sz n u D 0 (a 0) (a 1) ≤ OptL2aJg Cm n u H := by
  have hP := ST_STprof_pos sz n u D 0 (a 0) (a 1)
  rw [← le_div_iff₀ hP]
  unfold STJhatMg
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [OptL2a_prof_zero sz n u D (p.2 0) (p.2 1) (a 0) (a 1)]
  exact div_le_div_of_nonneg_right (OptL2Gen_J_ge Cm n u H p) hP.le

/-- Matrix level of (3.40) `l>0EQ` (band `OptL2a_drift_matrix`): `lem:newKLK` at `ℓ = 0` at `(Cm, n)`. -/
private theorem OptL2Gen_drift_matrix {C δ₀ : ℝ} (hC : 0 ≤ C) (n : ℕ) (hnew : Step2IterGen_NewKLKAtN Cm n C δ₀)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hH : H.IsHermitian) (hweak : ∀ x y, ‖STGMMg Cm n u H x y‖ ≤ δ₀) (i : STLab sz n) :
    ‖STthetaOpg Cm n u i.1 (STLKMg Cm n u H i.1) i.2‖ + ‖STELKLKMg Cm n u H i.1 i.2‖ ≤
      2 * C / (1 - u) * OptL2aJg Cm n u H := by
  have hL : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨h1, h2⟩ := hnew u 1 0 hu0 hu1 (by norm_num) le_rfl hL H hH hweak i.1 i.2
  have hv : 0 < 1 - u := by linarith
  have hJ := OptL2Gen_Jhat_mul_le Cm n 1 u H i.2
  have hc : 0 ≤ C / (1 - u) := div_nonneg hC hv.le
  have e1 : ‖STthetaOpg Cm n u i.1 (STLKMg Cm n u H i.1) i.2‖ ≤ C / (1 - u) * OptL2aJg Cm n u H := by
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hJ hc
  have e2 : ‖STELKLKMg Cm n u H i.1 i.2‖ ≤ C / (1 - u) * OptL2aJg Cm n u H := by
    refine h2.trans ?_
    have h0 : ¬ ((1 : ℝ) ≤ 0) := by norm_num
    simp only [h0, ite_false, mul_zero, add_zero]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hJ hc
  calc _ ≤ C / (1 - u) * OptL2aJg Cm n u H + C / (1 - u) * OptL2aJg Cm n u H := add_le_add e1 e2
    _ = 2 * C / (1 - u) * OptL2aJg Cm n u H := by ring

/-- Grid level of (3.40) `l>0EQ` (band `OptL2a_drift_grid`). -/
private theorem OptL2Gen_drift_grid {C δ₀ : ℝ} (hC : 0 ≤ C) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hnew : Step2IterGen_NewKLKAtN Cm n C δ₀) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    (ω : PathΩ sz) (j : ℕ) (hj : j ≤ K n) (hH : (Cm.Hpath s t K n j ω).IsHermitian)
    (hweak : ∀ x y, ‖STGMMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) x y‖ ≤ δ₀) (i : STLab sz n) :
    ‖STgDriftg Cm s t K n i.1 i.2 j ω‖ ≤
      2 * C / (1 - gridTime s t K n j) * OptL2aJg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) +
        ‖STEGtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ := by
  have hmem := ST_gridTime_mem s t K n j hst hK hj
  have hu0 : 0 ≤ gridTime s t K n j := hs0.trans hmem.1
  have hu1 : gridTime s t K n j < 1 := lt_of_le_of_lt hmem.2 ht1
  have h := OptL2Gen_drift_matrix Cm hC n hnew (gridTime s t K n j) hu0 hu1 (Cm.Hpath s t K n j ω) hH hweak i
  unfold STgDriftg
  calc _ ≤ ‖STthetaOpg Cm n (gridTime s t K n j) i.1
          (STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1) i.2‖ +
        ‖STELKLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ +
        ‖STEGtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ _ := add_le_add h le_rfl

end Drift


/-! ## 2. The hypotheses of the statements at a time section and the events on the grid -/

section Events

/-- The size data `c_B W^{-d} ≤ W^{-d}B_{u,0} ≤ N^{-c}` of `STBdatagL` with `c ≤ 1` (band `OptL2a_sizedata`;
`c` may be decreased since `N ≥ 1`). -/
private theorem OptL2Gen_sizedata {d : ℕ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hFl : Step2EventsGen_Flow d Flow T0) (hB : STBdatagL d Flow T0)
    {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ cB : ℝ, 0 < cB ∧ ∀ 𝔠 : ℝ, ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ T : ℕ → ℝ, (∀ n, 0 ≤ T n) →
        (∀ n, T n ≤ T0 sz z n) → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧
            sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
  obtain ⟨cB, hcB, hcBd⟩ := hB κ ε 𝔡 hκ hε h𝔡
  refine ⟨cB, hcB, fun 𝔠 => ?_⟩
  obtain ⟨c0, hc0, hBd0⟩ := hcBd 𝔠
  refine ⟨min c0 1, lt_min hc0 one_pos, min_le_right _ _, fun sz z hflow T hT0 hTT => ?_⟩
  filter_upwards [hBd0 sz z hflow T hT0 hTT,
    (tendsto_size sz (hFl.1 sz κ ε 𝔠 𝔡 z hflow).2.2.1).eventually (eventually_ge_atTop 1)] with n hn hN1 u hu0 huT
  refine ⟨(hn u hu0 huT).1, (hn u hu0 huT).2.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith [min_le_left c0 1])

/-- **The hypotheses of `lem:LWterm` and `lem: EMn2_N` at a time section `tt_n ∈ [s_n, T_n]`** with the bound
`Ψ = min(√λ, W^{-ε₀})` (band `OptL2a_premises`): (3.28) `eq:Psi`, (3.4) `initialGT2` from the weak law and (3.38) `lokis2` of Step 1,
(3.27) `eq:LW_assm` from (3.38) `lokis2`.  The flow enters through the admissibility of the sizes and `T < 1` only. -/
private theorem OptL2Gen_premises {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hd0 : 0 < d)
    {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {s T : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n)
    (hT1 : ∀ n, T n < 1) (hS1L : STStep1LoopgL C μ s T) (hS1W : STStep1WeakgL C μ s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    (tt : ∀ n, TimeIcc s T n) :
    STPsiClass sz ε₀ (fun n _ => OptL2aPsi sz ε₀ s T n) ∧
      STInitialGT2gL C μ (fun n => (tt n : ℝ)) ε₀ (fun n => OptL2aPsi sz ε₀ s T n) ∧
      STLWassmgL C μ (fun n => (tt n : ℝ)) (fun n _ => OptL2aPsi sz ε₀ s T n) := by
  classical
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hWt := ST_W_tendsto sz hsz hadm.1 hadm.2.2.2.1
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hε₀d : ε₀ ≤ (d : ℝ) / 2 := by rw [hε₀]; nlinarith
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  have hBT : ∀ n, 0 < sz.Bctl n (T n) := fun n => STBctl_pos sz n (hT1 n)
  have hlam : ∀ n, 0 < OptL2alam sz s T n := fun n =>
    mul_pos (div_pos (by linarith [hs1 n]) (by linarith [hT1 n])) (hBT n)
  have hρ1 : ∀ n, 1 ≤ (1 - s n) / (1 - T n) := fun n => by
    rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hΨpos : ∀ n, 0 < OptL2aPsi sz ε₀ s T n := fun n =>
    lt_min (Real.sqrt_pos.2 (hlam n)) (Real.rpow_pos_of_pos (hWpos n) _)
  have hΨle : ∀ n, OptL2aPsi sz ε₀ s T n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := fun n => min_le_right _ _
  have hbd : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (T n) ∧
      sz.Bctl n (T n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBd] with n hn using hn (T n) ((hs n).trans (hsT n)) le_rfl
  have hsq : ∀ᶠ n in atTop, Real.sqrt (OptL2alam sz s T n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
    (OptL2a_lam_facts sz hc hε₀ h𝔠d hT1 (hbd.mono fun n hn => hn.2) hcon).mono fun n hn => hn.2
  have hΨeq : ∀ᶠ n in atTop, OptL2aPsi sz ε₀ s T n = Real.sqrt (OptL2alam sz s T n) := by
    filter_upwards [hsq] with n hn using min_eq_left hn
  have hΨsq : ∀ᶠ n in atTop, (OptL2aPsi sz ε₀ s T n) ^ 2 = OptL2alam sz s T n := by
    filter_upwards [hΨeq] with n hn
    rw [hn, Real.sq_sqrt (hlam n).le]
  -- the window `W^{-d/2} ≲ Ψ`
  have hwin : ∀ᶠ n in atTop, min 1 (Real.sqrt cB) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤
      OptL2aPsi sz ε₀ s T n := by
    filter_upwards [hbd, hWt.eventually (eventually_ge_atTop 1)] with n hn hW1
    have hW := hWpos n
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
    have hc0 : 0 ≤ min 1 (Real.sqrt cB) := (lt_min one_pos (Real.sqrt_pos.2 hcB)).le
    have hn0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hW.le _
    refine le_min ?_ ?_
    · rw [ST_rpow_neg_half hW.le]
      calc min 1 (Real.sqrt cB) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ)
          ≤ Real.sqrt cB * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) := by
            refine mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (by positivity) _)
        _ = Real.sqrt (cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
            rw [Real.sqrt_mul hcB.le, Real.sqrt_eq_rpow (((sz.W n : ℕ) : ℝ) ^ d)⁻¹]
        _ ≤ Real.sqrt (OptL2alam sz s T n) := by
            refine Real.sqrt_le_sqrt ?_
            calc cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (T n) := hn.1
              _ = 1 * sz.Bctl n (T n) := (one_mul _).symm
              _ ≤ OptL2alam sz s T n := mul_le_mul_of_nonneg_right (hρ1 n) (hBT n).le
    · calc min 1 (Real.sqrt cB) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
          ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hn0
        _ = ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := one_mul _
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hPsi : STPsiClass sz ε₀ (fun n _ => OptL2aPsi sz ε₀ s T n) :=
    OptL2a_psiClass_const sz _ hΨpos hΨle (c0 := min 1 (Real.sqrt cB))
      (lt_min one_pos (Real.sqrt_pos.2 hcB)) (min_le_left _ _) hwin
  -- the size data at the section
  have hbdtt : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (tt n : ℝ) ∧
      sz.Bctl n (tt n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBd] with n hn
    exact hn (tt n : ℝ) ((hs n).trans (tt n).2.1) (tt n).2.2
  have hbpos : ∀ n, 0 ≤ sz.Bctl n (tt n : ℝ) := fun n =>
    (STBctl_pos sz n (lt_of_le_of_lt (tt n).2.2 (hT1 n))).le
  -- `(initialGT2)` at the section
  have hInit1 : PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖C.GM n (tt n : ℝ) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) := by
    have h1 := StochDomAt.precomp_param
      (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hS1W
      (fun n p => (tt n, p.1, p.2))
    refine Step2EventsGen_prec_mono_eventually μ ?_ h1
    filter_upwards [hbdtt] with n hn u ω
    have := ST_quarter_le sz n (hbpos n) hc.le hn.2
    rw [hε₀]
    exact this
  have hInit2 : PrecL sz μ (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2g C n (tt n : ℝ) ω)
      (fun n _ _ => (OptL2aPsi sz ε₀ s T n) ^ 2) := by
    have h1 := hS1L 2 (by norm_num)
    have h2 := StochDomAt.precomp_param (V := fun n => Zd d (sz.L n) × Zd d (sz.L n)) h1
      (fun n p => (tt n, ![false, true], ![p.1, p.2]))
    have h3 : PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖C.L n (tt n : ℝ) ![false, true] ![p.1, p.2] ω‖)
        (fun n _ _ => (OptL2aPsi sz ε₀ s T n) ^ 2) := by
      refine Step2EventsGen_prec_mono_eventually μ ?_ h2
      filter_upwards [hΨsq] with n hn u ω
      show ((1 - s n) / (1 - (tt n : ℝ))) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤ _
      rw [hn]
      exact OptL2a_loop_ctl sz n (tt n).2.1 (tt n).2.2 (hT1 n)
    exact Step2EventsGen_prec_sup μ _ _ h3
  have hassm : STLWassmgL C μ (fun n => (tt n : ℝ)) (fun n _ => OptL2aPsi sz ε₀ s T n) := by
    have h1 := hS1L 2 (by norm_num)
    have h2 := StochDomAt.precomp_param
      (V := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) h1
      (fun n p => (tt n, p.1.1, p.2))
    refine Step2EventsGen_prec_mono_eventually μ ?_ h2
    filter_upwards [hΨsq] with n hn u ω
    show ((1 - s n) / (1 - (tt n : ℝ))) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤ _
    rw [hn]
    exact OptL2a_loop_ctl sz n (tt n).2.1 (tt n).2.2 (hT1 n)
  exact ⟨hPsi, ⟨hInit1, hInit2⟩, hassm⟩

/-- **`lem:LWterm` at a time section** (band `OptL2a_sections_lw`): `𝓔^{G̃,(2)}_{tt,σ,a} ≺ η⁻¹ Ψ³` from `STLWBgL`. -/
private theorem OptL2Gen_sections_lw {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd0 : 0 < d)
    (hLWB : STLWBgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) (hadm : sz.Admissible 𝔠 𝔡) {s T : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n)
    (hT1 : ∀ n, T n < 1) (hTT : ∀ n, T n ≤ T0 sz z n)
    (hS1L : STStep1LoopgL (mk sz z).toFlowFM (law sz) s T) (hS1W : STStep1WeakgL (mk sz z).toFlowFM (law sz) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    (tt : ∀ n, TimeIcc s T n) :
    PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEGtg (mk sz z).toFlowFM n (tt n : ℝ) p.1 p.2 ω‖)
        (fun n _ _ => ((mk sz z).eta n (tt n : ℝ))⁻¹ * OptL2aPsi sz ε₀ s T n *
          (OptL2aPsi sz ε₀ s T n) ^ 2) := by
  obtain ⟨hPsi, hinit, hassm⟩ := OptL2Gen_premises (mk sz z).toFlowFM (law sz) hd0 hadm hs hsT hT1 hS1L hS1W hcB hc hc1
    hε₀ hBd h𝔠d hcon tt
  have hε₀pos : 0 < ε₀ := by
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [hε₀]; positivity
  exact hLWB κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ)) (fun n => (hs n).trans (tt n).2.1)
    (fun n => (tt n).2.2.trans (hTT n)) ε₀ hε₀pos (fun n _ => OptL2aPsi sz ε₀ s T n) hPsi hinit hassm

/-- **`lem: EMn2_N`, first estimate, at a time section** (band `OptL2a_sections_mg`): `(𝓔⊗𝓔)^{M,(2;k)}_{tt,σ,a,a} ≺ η⁻¹ Ψ⁵`
from `STEMn2PolygL`. -/
private theorem OptL2Gen_sections_mg {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd0 : 0 < d)
    (hEMP : STEMn2PolygL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) (hadm : sz.Admissible 𝔠 𝔡) {s T : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n)
    (hT1 : ∀ n, T n < 1) (hTT : ∀ n, T n ≤ T0 sz z n)
    (hS1L : STStep1LoopgL (mk sz z).toFlowFM (law sz) s T) (hS1W : STStep1WeakgL (mk sz z).toFlowFM (law sz) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    (tt : ∀ n, TimeIcc s T n) :
    PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEEg (mk sz z).toFlowFM n (tt n : ℝ) p.1 p.2.1 p.2.2 ω‖)
        (fun n _ _ => ((mk sz z).eta n (tt n : ℝ))⁻¹ * OptL2aPsi sz ε₀ s T n *
          (OptL2aPsi sz ε₀ s T n) ^ 4) := by
  obtain ⟨hPsi, hinit, hassm⟩ := OptL2Gen_premises (mk sz z).toFlowFM (law sz) hd0 hadm hs hsT hT1 hS1L hS1W hcB hc hc1
    hε₀ hBd h𝔠d hcon tt
  have hε₀pos : 0 < ε₀ := by
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [hε₀]; positivity
  exact hEMP κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ)) (fun n => (hs n).trans (tt n).2.1)
    (fun n => (tt n).2.2.trans (hTT n)) ε₀ hε₀pos (fun n _ => OptL2aPsi sz ε₀ s T n) hPsi hinit hassm


/-- **The light-weight term on the grid** (band `OptL2a_event_lw`; `lem:LWterm` at every grid time under `Step2EventsGen_Grid`):
`|𝓔^{G̃,(2)}_{u_j,σ,a}| ≤ N^{ε₁} η_{u_j}⁻¹ Ψ³` for all `j ≤ K_n` and all labels, w.h.p. -/
private theorem OptL2Gen_event_lw {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd0 : 0 < d)
    (hLWB : STLWBgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) (hadm : sz.Admissible 𝔠 𝔡) (hG : Step2EventsGen_Grid (mk sz z) (law sz))
    {s T : ℕ → ℝ} (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hK : ∀ n, K n ≠ 0)
    (hT1 : ∀ n, T n < 1) (hTT : ∀ n, T n ≤ T0 sz z n)
    (hS1L : STStep1LoopgL (mk sz z).toFlowFM (law sz) s T) (hS1W : STStep1WeakgL (mk sz z).toFlowFM (law sz) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (STLab sz n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    HighProbAt (mk sz z).Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEGtMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 2)}) := by
  have hG' := hG
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hG
  have hmain := Step2EventsGen_grid_whp_of_sections (mk sz z) (law sz) hlaw (V := fun n => STLab sz n) s T K hs hsT hK
    hC₁ hcard
    (fun n v u H => ‖STEGtMg (mk sz z) n u H v.1 v.2‖)
    (fun n v u H => ((mk sz z).eta n u)⁻¹ * OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 2)
    (fun n v u => (Step2EventsGen_STEGtMg_measurable hG' n u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt => by
      have h := OptL2Gen_sections_lw law Flow mk T0 hd0 hLWB hκ hε h𝔡 hflow hadm hs hsT hT1 hTT hS1L hS1W hcB hc hc1
        hε₀ hBd h𝔠d hcon tt
      simpa only [Step2EventsGen_STEGtMg_eq (mk sz z) hLM] using h)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  exact hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) i

/-- **The quadratic variation on the grid** (band `OptL2a_event_mg`; `lem: EMn2_N`, first estimate, at every grid
time under `Step2EventsGen_Grid`): `|(𝓔⊗𝓔)^{M,(2)}_{u_j,σ,a}| ≤ 2 N^{ε₁} η_{u_j}⁻¹ Ψ⁵` for all `j ≤ K_n` and all labels, w.h.p. -/
private theorem OptL2Gen_event_mg {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd0 : 0 < d)
    (hEMP : STEMn2PolygL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) (hadm : sz.Admissible 𝔠 𝔡) (hG : Step2EventsGen_Grid (mk sz z) (law sz))
    {s T : ℕ → ℝ} (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hK : ∀ n, K n ≠ 0)
    (hT1 : ∀ n, T n < 1) (hTT : ∀ n, T n ≤ T0 sz z n)
    (hS1L : STStep1LoopgL (mk sz z).toFlowFM (law sz) s T) (hS1W : STStep1WeakgL (mk sz z).toFlowFM (law sz) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Fin 2 × STLab sz n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    HighProbAt (mk sz z).Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖ ≤
        2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4)}) := by
  have hG' := hG
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hG
  have hmain := Step2EventsGen_grid_whp_of_sections (mk sz z) (law sz) hlaw (V := fun n => Fin 2 × STLab sz n) s T K hs hsT
    hK hC₁ hcard
    (fun n v u H => ‖STEEkMg (mk sz z) n u H v.1 v.2.1 v.2.2‖)
    (fun n v u H => ((mk sz z).eta n u)⁻¹ * OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4)
    (fun n v u => (Step2EventsGen_STEEkMg_measurable hG' n u v.1 v.2.1 v.2.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt => by
      have h := OptL2Gen_sections_mg law Flow mk T0 hd0 hEMP hκ hε h𝔡 hflow hadm hs hsT hT1 hTT hS1L hS1W hcB hc hc1
        hε₀ hBd h𝔠d hcon tt
      simpa only [Step2EventsGen_STEEkMg_eq (mk sz z) hLM] using h)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  have hj' := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have h0 := hω j hj' (0, i)
  have h1 := hω j hj' (1, i)
  calc ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖
      ≤ ‖STEEkMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) 0 i.1 i.2‖ +
        ‖STEEkMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) 1 i.1 i.2‖ :=
        norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4) +
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4) := add_le_add h0 h1
    _ = _ := by ring

end Events


/-! ## 3. The pathwise Grönwall inequality on one sample -/

section Pathwise

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `Δ Σ_{j<k} η_{u_j}⁻¹ ≤ q log((1-s)/(1-T))` along the grid, `η_t = (1 - t) Im m` (`DecayGen_Spec`), `(Im m)⁻¹ ≤ q` (band `OptL2a_eta_sum`;
the logarithmic time sum `ST_logsum`, (3.41) `eq:Gronwall_2L_max`). -/
private theorem OptL2Gen_eta_sum {s T : ℕ → ℝ} (K : ℕ → ℕ) (n : ℕ) {q : ℝ}
    (hη : ∀ t, Cm.eta n t = (1 - t) * (Cm.m n).im) (hmI : 0 < (Cm.m n).im) (hsT : s n ≤ T n) (hT1 : T n < 1)
    (hK : K n ≠ 0) (hq : ((Cm.m n).im)⁻¹ ≤ q) {k : ℕ} (hk : k ≤ K n) :
    gridStep s T K n * ∑ j ∈ Finset.range k, (Cm.eta n (gridTime s T K n j))⁻¹ ≤
      q * Real.log ((1 - s n) / (1 - T n)) := by
  have hΔ := ST_gridStep_nonneg s T K n hsT
  have hmemk := ST_gridTime_mem s T K n k hsT hK hk
  have hk1 : s n + (k : ℝ) * gridStep s T K n < 1 := by
    have := hmemk.2; unfold gridTime at this; linarith
  have hlog := ST_logsum hΔ k hk1
  have hq0 : 0 ≤ q := (inv_nonneg.mpr hmI.le).trans hq
  have hterm : ∀ j ∈ Finset.range k, (Cm.eta n (gridTime s T K n j))⁻¹ ≤
      q * (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ := by
    intro j hj
    have hjk : j ≤ K n := (Finset.mem_range.mp hj).le.trans hk
    have hmj := ST_gridTime_mem s T K n j hsT hK hjk
    have hu1 : gridTime s T K n j < 1 := lt_of_le_of_lt hmj.2 hT1
    have hpos : 0 < 1 - (s n + (j : ℝ) * gridStep s T K n) := by unfold gridTime at hu1; linarith
    rw [hη]
    unfold gridTime
    rw [mul_inv]
    calc (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ * ((Cm.m n).im)⁻¹
        ≤ (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ * q :=
          mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hpos.le)
      _ = q * (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ := mul_comm _ _
  have hsk : s n + (k : ℝ) * gridStep s T K n ≤ T n := by
    have := hmemk.2; unfold gridTime at this; linarith
  have hs1 : 0 < 1 - s n := by linarith
  have hA : 0 < 1 - (s n + (k : ℝ) * gridStep s T K n) := by linarith
  calc gridStep s T K n * ∑ j ∈ Finset.range k, (Cm.eta n (gridTime s T K n j))⁻¹
      ≤ gridStep s T K n * ∑ j ∈ Finset.range k, q * (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hΔ
    _ = q * (gridStep s T K n * ∑ j ∈ Finset.range k, (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ q * Real.log ((1 - s n) / (1 - (s n + (k : ℝ) * gridStep s T K n))) :=
        mul_le_mul_of_nonneg_left hlog hq0
    _ ≤ q * Real.log ((1 - s n) / (1 - T n)) := by
        refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hs1 hA) ?_) hq0
        exact div_le_div_of_nonneg_left hs1.le (by linarith) (by linarith)

/-- `Σ_{j<k} Δ (a η_{u_j}⁻¹) ≤ a q Lg`, `Lg ≥ log((1-s)/(1-T))` (band `OptL2a_eta_sum_mul`). -/
private theorem OptL2Gen_eta_sum_mul {s T : ℕ → ℝ} (K : ℕ → ℕ) (n : ℕ) {q Lg a : ℝ}
    (hη : ∀ t, Cm.eta n t = (1 - t) * (Cm.m n).im) (hmI : 0 < (Cm.m n).im) (hsT : s n ≤ T n) (hT1 : T n < 1)
    (hK : K n ≠ 0) (hq : ((Cm.m n).im)⁻¹ ≤ q) (hLg : Real.log ((1 - s n) / (1 - T n)) ≤ Lg) (ha : 0 ≤ a) {k : ℕ}
    (hk : k ≤ K n) :
    ∑ j ∈ Finset.range k, gridStep s T K n * (a * (Cm.eta n (gridTime s T K n j))⁻¹) ≤ a * (q * Lg) := by
  have hq0 : 0 ≤ q := (inv_nonneg.mpr hmI.le).trans hq
  have h := OptL2Gen_eta_sum Cm K n hη hmI hsT hT1 hK hq hk
  have h2 : q * Real.log ((1 - s n) / (1 - T n)) ≤ q * Lg := mul_le_mul_of_nonneg_left hLg hq0
  have hrew : ∑ j ∈ Finset.range k, gridStep s T K n * (a * (Cm.eta n (gridTime s T K n j))⁻¹) =
      a * (gridStep s T K n * ∑ j ∈ Finset.range k, (Cm.eta n (gridTime s T K n j))⁻¹) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_left (h.trans h2) ha

/-- **The Grönwall inequality on one sample** (band `OptL2a_pathwise`): on the sample where the drift bound, the initial value,
the martingale bound, the remainder and the grid decomposition hold, `J_k ≤ α + Δ Σ_{j<k} (C₀/(1-u_j)) J_j` for all `k ≤ K_n`
((3.41) `eq:Gronwall_2L_max`). -/
private theorem OptL2Gen_pathwise {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (s T : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hη : ∀ t, Cm.eta n t = (1 - t) * (Cm.m n).im) (hmI : 0 < (Cm.m n).im) (hsT : s n ≤ T n)
    (hT1 : T n < 1) (hK : K n ≠ 0)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    {a₀ r₀ Mx Y q Lg Mb α : ℝ} (ha₀ : 0 ≤ a₀) (hr₀ : 0 ≤ r₀) (hMx : 0 ≤ Mx) (hY : 0 ≤ Y)
    (hq : ((Cm.m n).im)⁻¹ ≤ q) (hLg : Real.log ((1 - s n) / (1 - T n)) ≤ Lg)
    (hα : a₀ + r₀ + Mx * Y * (q * Lg) + Mb ≤ α)
    (hdrift : ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STgDriftg Cm s T K n i.1 i.2 j ω‖ ≤ C₀ / (1 - gridTime s T K n j) *
          OptL2aJg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) +
        Mx * ((Cm.eta n (gridTime s T K n j))⁻¹ * Y))
    (hinit : ∀ i : STLab sz n, ‖STgAg Cm s T K n i.1 i.2 0 ω‖ ≤ a₀)
    (hmart : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Mart i k ω‖ ≤ Mb)
    (hrem : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ r₀)
    (hident : ∀ i : STLab sz n, ∀ k, k ≤ K n →
      STgAg Cm s T K n i.1 i.2 k ω =
        STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω + Rem i k ω + Mart i k ω) :
    ∀ k, k ≤ K n →
      OptL2aJg Cm n (gridTime s T K n k) (Cm.Hpath s T K n k ω) ≤
        α + gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
          OptL2aJg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) := by
  classical
  have hΔ := ST_gridStep_nonneg s T K n hsT
  have hmem : ∀ j, j ≤ K n → s n ≤ gridTime s T K n j ∧ gridTime s T K n j ≤ T n := fun j hj =>
    ST_gridTime_mem s T K n j hsT hK hj
  have hu1 : ∀ j, j ≤ K n → gridTime s T K n j < 1 := fun j hj =>
    lt_of_le_of_lt (hmem j hj).2 hT1
  have hηpos : ∀ j, j ≤ K n → 0 < Cm.eta n (gridTime s T K n j) := fun j hj => by
    rw [hη]; exact mul_pos (by linarith [hu1 j hj]) hmI
  have hdec : ∀ (i : STLab sz n) (k : ℕ), k ≤ K n → k ≤ K n →
      ‖STgAg Cm s T K n i.1 i.2 k ω‖ ≤ ‖STgAg Cm s T K n i.1 i.2 0 ω‖ +
        gridStep s T K n * ∑ j ∈ Finset.range k, ‖STgDriftg Cm s T K n i.1 i.2 j ω‖ +
        ‖Rem i k ω‖ + ‖Mart i k ω‖ := by
    intro i k hk _
    have hid := hident i k hk
    have hsum' : ‖((gridStep s T K n : ℝ) : ℂ) *
        ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω‖ ≤
        gridStep s T K n * ∑ j ∈ Finset.range k, ‖STgDriftg Cm s T K n i.1 i.2 j ω‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hΔ
    rw [hid]
    calc ‖STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω + Rem i k ω + Mart i k ω‖
        ≤ ‖STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω + Rem i k ω‖ +
          ‖Mart i k ω‖ := norm_add_le _ _
      _ ≤ (‖STgAg Cm s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω‖ + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖STgAg Cm s T K n i.1 i.2 0 ω‖ + ‖((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω‖) + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr
  have key := ST_pathwise_ineq (ι := STLab sz n) (K := K n) (τ := K n) (Δ := gridStep s T K n)
    (a₀ := a₀) (r₀ := r₀)
    (x := fun k i => ‖STgAg Cm s T K n i.1 i.2 k ω‖)
    (dr := fun j i => ‖STgDriftg Cm s T K n i.1 i.2 j ω‖)
    (mart := fun k i => ‖Mart i k ω‖) (P := fun _ _ => (1 : ℝ))
    (remk := fun k i => ‖Rem i k ω‖)
    (Jh := fun j => OptL2aJg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω))
    (β := fun j => C₀ / (1 - gridTime s T K n j))
    (e := fun j => Mx * ((Cm.eta n (gridTime s T K n j))⁻¹ * Y))
    (m := fun _ => Mb)
    hΔ ha₀ hr₀ (fun j _ => OptL2Gen_J_nonneg Cm n _ _)
    (fun k B _ h => OptL2Gen_J_le Cm n _ _ (fun i => by have := h i; rw [div_one] at this; exact this))
    (fun _ _ _ => one_pos) (fun _ _ _ _ _ _ => le_refl _)
    (fun j hj => div_nonneg hC₀ (by linarith [hu1 j hj.le]))
    (fun j hj => mul_nonneg hMx (mul_nonneg (inv_nonneg.mpr (hηpos j hj.le).le) hY))
    hdec (fun i => by simpa using hinit i)
    (fun i j hj => by simpa using hdrift j hj.le i)
    (fun i k hk => by simpa using hrem i k hk)
    (fun i k hk => by simpa using hmart i k hk)
  intro k hk
  have hk' := key k hk hk
  have hE_sum : gridStep s T K n * ∑ j ∈ Finset.range k,
      Mx * ((Cm.eta n (gridTime s T K n j))⁻¹ * Y) ≤ Mx * Y * (q * Lg) := by
    have h := OptL2Gen_eta_sum_mul Cm K n hη hmI hsT hT1 hK hq hLg (mul_nonneg hMx hY) hk
    have hrew : gridStep s T K n * ∑ j ∈ Finset.range k,
        Mx * ((Cm.eta n (gridTime s T K n j))⁻¹ * Y) =
        ∑ j ∈ Finset.range k, gridStep s T K n *
          (Mx * Y * (Cm.eta n (gridTime s T K n j))⁻¹) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrew]; exact h
  linarith

end Pathwise


/-! ## 4. The three statements on the grid -/

/-- **The drift bound of (3.40) `l>0EQ`** (band `stOptL2a_drift`) over a carrier family.  For
`κ, ε, 𝔡 > 0` there is `C₀ > 0` (`C₀ = 2C`, `C` of `lem:newKLK`: depends on `κ, 𝔡` only) such that, along a flow
(`Flow sz κ ε 𝔠 𝔡 z`) and for times `0 ≤ s ≤ T ≤ T0` with the first conjunct of (2.83) `con_st_ind` (`B_T^{𝔠_d} ≤ (1-T)/(1-s)`,
`𝔠_d ≤ 1/2`) and Step 1 on `[s,T]`, for every `τ > 0` and every grid `K_n = ⌈N^{CK}⌉` from `s` to `T`, w.h.p., for all `j ≤ K_n`
and all labels `(σ,a)`: the drift of `(𝓛-𝒦)^{(2)}` at `u_j` is at most `C₀ (1-u_j)⁻¹ J_j + N^τ η_{u_j}⁻¹ λ^{3/2}`,
`J_j = max_{σ,a} |(𝓛-𝒦)^{(2)}_{u_j,σ,a}|`, `λ = ((1-s)/(1-T)) W^{-d}B_{T,0}`.  The light-weight term enters through the statement `STLWBgL`;
`lem:newKLK` at `ℓ = 0` is `Step2IterGen_NewKLK`. -/
theorem stOptL2a_driftg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd : 3 ≤ d)
    (hFl : Step2EventsGen_Flow d Flow T0)
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz))
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian)
    (hBdata : STBdatagL d Flow T0)
    (hLWB : STLWBgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hNew : Step2IterGen_NewKLK d Flow mk)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ T0 sz z n) →
        ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1LoopgL (mk sz z).toFlowFM (law sz) s T → STStep1WeakgL (mk sz z).toFlowFM (law sz) s T →
          ∀ τ : ℝ, 0 < τ → ∀ CK : ℝ, 0 ≤ CK → ∀ K : ℕ → ℕ,
            (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              HighProbAt (mk sz z).Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
                ‖STgDriftg (mk sz z) s T K n i.1 i.2 j ω‖ ≤
                  C₀ / (1 - gridTime s T K n j) *
                      OptL2aJg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) +
                    ((sz.size n : ℕ) : ℝ) ^ τ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
                      (OptL2alam sz s T n) ^ (3 / 2 : ℝ))}) := by
  classical
  obtain ⟨C, δ₀, hC, hδ₀, hnew⟩ := hNew hd κ 𝔡 hκ h𝔡
  have hd0 : 0 < d := by omega
  obtain ⟨cB, hcB, hcd⟩ := OptL2Gen_sizedata hFl hBdata hκ hε h𝔡
  refine ⟨2 * C, by positivity, ?_⟩
  intro 𝔠 sz z hflow s T hs hsT hTT 𝔠d h𝔠d hcon hS1L hS1W τ hτ CK hCK K hKn
  have hadm := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hsize := tendsto_size sz hadm.2.2.1
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hT1 : ∀ n, T n < 1 := fun n => lt_of_le_of_lt (hTT n) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  have hBd := hBd0 sz z hflow T hT0 hTT
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  obtain ⟨hK0, -⟩ := OptL2a_grid sz K hKn
  obtain ⟨hcardIdx, -, hcardLab, -⟩ := OptL2a_cards sz hsize hCK K hKn
  -- the weak law
  have hsmallE1 : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ T n →
      ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n u) ^ (1 / 4 : ℝ) ≤ δ₀ := by
    filter_upwards [hBd, ST_size_pow_small sz hsize (a := c / 8 - c / 4) (δ := δ₀)
      (by linarith) hδ₀] with n hn hsm u hsu huT
    have hb := (hn u ((hs n).trans hsu) huT).2
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hb0 : 0 ≤ sz.Bctl n u := (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg
      (Nat.cast_nonneg _) d))).trans (hn u ((hs n).trans hsu) huT).1
    calc ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n u) ^ (1 / 4 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb0 hb (by norm_num)) (Real.rpow_nonneg hN0 _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (c / 8 - c / 4) := by
          rw [← Real.rpow_mul hN0, ← Real.rpow_add' hN0 (by linarith)]; congr 1; ring
      _ ≤ δ₀ := hsm
  have hE1 := ST_event_weakg d sz (mk sz z) (law sz) (hGrid sz z) s T T K hs hsT (fun n => le_refl _) hK0
    (CK + 5) (by linarith) hcardIdx hS1W (c / 8) δ₀ (by positivity) hsmallE1
  -- the light-weight term
  have hE3 := OptL2Gen_event_lw law Flow mk T0 hd0 hLWB hκ hε h𝔡 hflow hadm (hGrid sz z) K hs hsT hK0 hT1 hTT hS1L
    hS1W hcB hc hc1 hε₀ hBd h𝔠d hcon (C₁ := CK + 5) (by linarith) hcardLab hτ
  have hlf := OptL2a_lam_facts sz hc hε₀ h𝔠d hT1
    (hBd.mono fun n hn => (hn (T n) (hT0 n) le_rfl).2) hcon
  refine (HighProbAt.inter hsize hE1 hE3).mono ?_
  filter_upwards [hnew ε 𝔠 sz z hflow, hlf, hBd, hcon, hsize.eventually (eventually_ge_atTop 1)] with n hnewn hlfn
    hbdn hconn hN1
  rintro ω ⟨hw, hl⟩ j hj i
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hs1 : s n < 1 := lt_of_le_of_lt (hsT n) (hT1 n)
  obtain ⟨hlampos, -, -, hΨeq⟩ := OptL2a_lam_basic sz n hcB hs1 (hT1 n) (hsT n) hN1'
    (hbdn (T n) (hT0 n) le_rfl) hlfn hc.le
  obtain ⟨hw2, -, -, hw6⟩ := OptL2a_w_pow hlampos
  have hdr := OptL2Gen_drift_grid (mk sz z) (by positivity : (0 : ℝ) ≤ C) s T K n hnewn (hs n) (hsT n) (hT1 n)
    (hK0 n) ω j hj (hHerm sz z s T K n j ω) (hw j hj) i
  have hel := hl j hj i
  have hΨ3 : OptL2aPsi sz ε₀ s T n * OptL2aPsi sz ε₀ s T n ^ 2 = OptL2alam sz s T n ^ (3 / 2 : ℝ) := by
    rw [← hw6, hΨeq]; ring
  have hrew : ((sz.size n : ℕ) : ℝ) ^ τ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
      OptL2aPsi sz ε₀ s T n * OptL2aPsi sz ε₀ s T n ^ 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ * (((mk sz z).eta n (gridTime s T K n j))⁻¹ *
        OptL2alam sz s T n ^ (3 / 2 : ℝ)) := by
    rw [← hΨ3]; ring
  rw [hrew] at hel
  exact hdr.trans (add_le_add le_rfl hel)


/-- **The martingale bound** (band `stOptL2a_martingale`) over a carrier family.  Under the
hypotheses of the drift bound (without `STLWBgL`), for every `τ, D > 0` there is a grid exponent `CK` such that on every grid
`K_n = ⌈N^{CK}⌉` from `s` to `T` the grid decomposition of `STGridMartgL` holds with a remainder `|Rem| ≤ N^{-2}` and a martingale
part with `|Mart_k| ≤ N^τ λ^{5/4}` for all `k ≤ K_n` and all labels, with probability `≥ 1 - N^{-D}`.  Inputs: (3.33) `eq:MG_conclusion`
(`STEMn2PolygL`) with `Ψ = √λ`, `DecayGen_Spec` for `q = κm⁻¹ ≥ (Im m)⁻¹`, and the Markov step of the statement `STGridMartgL`. -/
theorem stOptL2a_martingaleg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd0 : 0 < d)
    (hFl : Step2EventsGen_Flow d Flow T0)
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz))
    (hSpec : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm)
    (hBdata : STBdatagL d Flow T0)
    (hEMP : STEMn2PolygL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hGM : STGridMartgL d Flow mk T0)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ T0 sz z n) →
        ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1LoopgL (mk sz z).toFlowFM (law sz) s T → STStep1WeakgL (mk sz z).toFlowFM (law sz) s T →
          ∀ τ : ℝ, 0 < τ → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
            ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
                (∀ n i, ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                  STgAg (mk sz z) s T K n i.1 i.2 k ω =
                    STgAg (mk sz z) s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s T K n i.1 i.2 j ω +
                        Rem n i k ω + Mart n i k ω) ∧
                (∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
                  ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)) ∧
                (∀ᶠ n in atTop, (mk sz z).Pp {ω | ∃ i : STLab sz n, ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ τ * (OptL2alam sz s T n) ^ (5 / 4 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) := by
  classical
  obtain ⟨CM, hCM0, hCM⟩ := hGM
  obtain ⟨κm, hκm⟩ := hSpec κ hκ
  obtain ⟨cB, hcB, hcd⟩ := OptL2Gen_sizedata hFl hBdata hκ hε h𝔡
  intro 𝔠 sz z hflow s T hs hsT hTT 𝔠d h𝔠d hcon hS1L hS1W τ hτ D hD
  have hspec := hκm sz ε 𝔠 𝔡 z hflow
  have hadm := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hsize := tendsto_size sz hadm.2.2.1
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hT1 : ∀ n, T n < 1 := fun n => lt_of_le_of_lt (hTT n) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  have hBd := hBd0 sz z hflow T hT0 hTT
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = τ / 8 := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  obtain ⟨Dm, hDmdef⟩ : ∃ Dm : ℝ, Dm = D + 4 := ⟨_, rfl⟩
  have hDmpos : 0 < Dm := by rw [hDmdef]; linarith
  obtain ⟨CK0, hCK0, hCK⟩ := hCM κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s T hs hsT hTT Dm hDmpos
  obtain ⟨CK', hCK'def⟩ : ∃ CK' : ℝ, CK' = max CK0 (2 * (CM + 2)) := ⟨_, rfl⟩
  have hCK'0 : 0 ≤ CK' := by rw [hCK'def]; exact hCK0.trans (le_max_left _ _)
  have hCK'1 : CK0 ≤ CK' := by rw [hCK'def]; exact le_max_left _ _
  have hCK'2 : 2 * (CM + 2) ≤ CK' := by rw [hCK'def]; exact le_max_right _ _
  refine ⟨CK', hCK'0, ?_⟩
  intro K hKn
  obtain ⟨hK0, hKbig'⟩ := OptL2a_grid sz K hKn
  have hKbig : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK0 ≤ (K n : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hCK'1).trans (hKbig' n)
  obtain ⟨Mart, Rem, hident, hrem0, hmart0⟩ := hCK K hK0 hKbig
  obtain ⟨-, hcardLab3, -, hcardF2⟩ := OptL2a_cards sz hsize hCK'0 K hKn
  refine ⟨Mart, Rem, hident, ?_, ?_⟩
  · -- the remainder
    filter_upwards [hrem0, hsize.eventually (eventually_ge_atTop 1)] with n hr hN1 i
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    refine (hr i).mono fun ω hω k hk => (hω k hk).trans ?_
    have hts : T n - s n ≤ 1 := by linarith [hT1 n, hs n]
    have hsq := ST_sqrt_gridStep_le s T K n hN1' hts (hKbig' n)
    calc ((sz.size n : ℕ) : ℝ) ^ CM * Real.sqrt (gridStep s T K n)
        ≤ ((sz.size n : ℕ) : ℝ) ^ CM * ((sz.size n : ℕ) : ℝ) ^ (-CK' / 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (CM + -CK' / 2) := (Real.rpow_add hN0 _ _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  · -- the martingale
    obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = κm⁻¹ := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by rw [hqdef]; exact (inv_pos.2 hspec.1).le
    have hbigE : ∀ᶠ n in atTop, q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)) ≤
        ((sz.size n : ℕ) : ℝ) ^ (ε₁ / 2) :=
      ST_size_pow_big sz hsize (a := ε₁ / 2) (M := q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)))
        (by positivity)
    have hMge : ∀ᶠ n in atTop, 2 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ :=
      ST_size_pow_big sz hsize (a := ε₁) (M := 2) hε₁
    have hfm : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-(4 - 5 / 2 : ℝ)) ≤ cB ^ (5 / 2 : ℝ) :=
      ST_size_pow_small sz hsize (by norm_num) (Real.rpow_pos_of_pos hcB _)
    have hlf := OptL2a_lam_facts sz hc hε₀ h𝔠d hT1
      (hBd.mono fun n hn => (hn (T n) (hT0 n) le_rfl).2) hcon
    have hE4 := OptL2Gen_event_mg law Flow mk T0 hd0 hEMP hκ hε h𝔡 hflow hadm (hGrid sz z) K hs hsT hK0 hT1 hTT hS1L
      hS1W hcB hc hc1 hε₀ hBd h𝔠d hcon (C₁ := CK' + 5) (by linarith) hcardF2 hε₁
    refine OptL2a_prob_combine (mk sz z).Pp sz.size hsize _ hE4
      (fun n i => {ω | ∃ k, k ≤ K n ∧ ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        (∑ j ∈ Finset.range k, gridStep s T K n *
          ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖ +
          ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖})
      (fun n => ∅) hD (Dm := Dm) (by rw [hDmdef]; linarith) (hmart0 ε₁ hε₁) hcardLab3
      (Eventually.of_forall fun n => measure_empty) _ ?_
    filter_upwards [hsize.eventually (eventually_ge_atTop 1), hBd, hlf, hcon, hMge, hbigE, hfm]
      with n hN1 hbdn hlfn hconn hM hbig hfmn
    intro ω hω
    by_contra hcon'
    have hΞω := fun h => hcon' (Or.inl (Or.inl h))
    have hm := not_not.1 hΞω
    have hΔ0 := ST_gridStep_nonneg s T K n (hsT n)
    have hnB : ∀ i, ω ∉ ({ω | ∃ k, k ≤ K n ∧ ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        (∑ j ∈ Finset.range k, gridStep s T K n *
          ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖ +
          ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖} : Set (PathΩ sz)) :=
      fun i hB => hcon' (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, hB⟩)))
    obtain ⟨i, k, hk, hlt⟩ := hω
    -- the numbers at `n`
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hmI : 0 < ((mk sz z).m n).im := lt_of_lt_of_le hspec.1 (hspec.2.1 n)
    have hη : ∀ t, (mk sz z).eta n t = (1 - t) * ((mk sz z).m n).im := hspec.2.2 n
    obtain ⟨hlampos, -, hlamge, hΨeq⟩ := OptL2a_lam_basic sz n hcB (hs1 n) (hT1 n) (hsT n) hN1'
      (hbdn (T n) (hT0 n) le_rfl) hlfn hc.le
    obtain ⟨hw2, hw5, hw10, -⟩ := OptL2a_w_pow hlampos
    have hw0 : 0 < OptL2alam sz s T n ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlampos _
    have hΨ0 : 0 < OptL2aPsi sz ε₀ s T n := by rw [hΨeq]; positivity
    have hΨw : OptL2aPsi sz ε₀ s T n ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 2 := hΨeq.le
    have hNmfl : ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 10 := by
      calc ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤ ((sz.size n : ℕ) : ℝ) ^ (-4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1' (by rw [hDmdef]; linarith)
        _ ≤ OptL2alam sz s T n ^ (5 / 2 : ℝ) :=
            OptL2a_floor hcB hN1' hlamge (by norm_num) hfmn
        _ = (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 10 := hw10.symm
    have hxM := OptL2a_x_le sz n hq0 hε₁ hcB (hT1 n) (hsT n) hN1' (hbdn (T n) (hT0 n) le_rfl)
      hc.le h𝔠d hconn hbig
    have hρ1 : 1 ≤ (1 - s n) / (1 - T n) := by
      rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
    have hx0 : 0 ≤ q * Real.log ((1 - s n) / (1 - T n)) := mul_nonneg hq0 (Real.log_nonneg hρ1)
    have hNm0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-Dm) := Real.rpow_nonneg hN0.le _
    have hqim : (((mk sz z).m n).im)⁻¹ ≤ q := by
      rw [hqdef]; exact inv_anti₀ hspec.1 (hspec.2.1 n)
    -- the quadratic variation sum
    have hmgn : ∀ j, j ≤ K n →
        ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖ ≤
          (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5) *
            ((mk sz z).eta n (gridTime s T K n j))⁻¹ := fun j hj => by
      refine (hm j hj i).trans (le_of_eq ?_)
      ring
    have ha : 0 ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5 :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hN0.le _)) (pow_nonneg hΨ0.le 5)
    have hetaS := OptL2Gen_eta_sum_mul (mk sz z) K n hη hmI (hsT n) (hT1 n) (hK0 n) hqim (le_refl _) ha hk
    have hsumE : ∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖ ≤
        (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5) *
          (q * Real.log ((1 - s n) / (1 - T n))) :=
      le_trans (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
        (hmgn j ((Finset.mem_range.mp hj).le.trans hk)) hΔ0) hetaS
    have hmartn := not_lt.1 fun h => hnB i ⟨k, hk, h⟩
    have h1 : ((sz.size n : ℕ) : ℝ) ^ ε₁ * (∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEMg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5 *
          (q * Real.log ((1 - s n) / (1 - T n))) + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) := by
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ (by norm_num))
        (Real.rpow_nonneg hN0.le _)
      linarith
    have h2 := OptL2a_mart_arith (M := ((sz.size n : ℕ) : ℝ) ^ ε₁) (w := OptL2alam sz s T n ^ (1 / 4 : ℝ))
      (Ψ := OptL2aPsi sz ε₀ s T n) (x := q * Real.log ((1 - s n) / (1 - T n)))
      (Nm := ((sz.size n : ℕ) : ℝ) ^ (-Dm)) (by linarith) hw0 hΨ0 hΨw hx0 hxM hNm0 hNmfl
    have hM8 : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 8 = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; rw [hε₁def]; push_cast; ring
    have h3 : 2 * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 ≤ (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 8 :=
      OptL2a_two_sq_le hM
    have hw5' : 0 ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 := by positivity
    have h4 : 2 * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 * (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * OptL2alam sz s T n ^ (5 / 4 : ℝ) := by
      rw [← hw5, ← hM8]; exact mul_le_mul_of_nonneg_right h3 hw5'
    exact absurd (hlt.trans_le (hmartn.trans (h1.trans (h2.trans h4)))) (lt_irrefl _)


/-- **(3.41) `eq:Gronwall_2L_max` on the grid in the form `ST_gronwall` consumes** (band `stOptL2a_gronwall`) over a carrier family.  For `κ, ε, 𝔡 > 0` there is `C₀ > 0` (`C₀ = 2C`) such that along a flow, for times
`0 ≤ s ≤ T ≤ T0`, under (2.78) `Eq:L-KGt+IND` at `s` (`STLKgL`), the first conjunct `B_T^{𝔠_d} ≤ (1-T)/(1-s)` of (2.83) `con_st_ind`
(`𝔠_d ≤ 1/2`) and Step 1 on `[s,T]`, for every `τ, D > 0` there is a grid exponent `CK` such that on the grid `K_n = ⌈N^{CK}⌉` from `s`
to `T`, with probability `≥ 1 - N^{-D}`, for all `k ≤ K_n`
`J_k ≤ N^τ ((W^{-d}B_{s,0})² + λ^{5/4}) + Δ Σ_{j<k} (C₀/(1-u_j)) J_j`, `J_k = max_{σ,a} |(𝓛-𝒦)^{(2)}_{u_k,σ,a}|` of the grid walk.  It
combines the drift and martingale bounds with the initial value `J_0 ≺ B_s²` (`STLKgL` at `k = 2`, `Step2EventsGen_Grid`). -/
theorem stOptL2a_gronwallg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd : 3 ≤ d)
    (hFl : Step2EventsGen_Flow d Flow T0)
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz))
    (hSpec : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm)
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian)
    (hBdata : STBdatagL d Flow T0)
    (hLWB : STLWBgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hEMP : STEMn2PolygL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hNew : Step2IterGen_NewKLK d Flow mk)
    (hGM : STGridMartgL d Flow mk T0)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ T0 sz z n) →
        STLKgL (mk sz z).toFlowFM (law sz) s → ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1LoopgL (mk sz z).toFlowFM (law sz) s T → STStep1WeakgL (mk sz z).toFlowFM (law sz) s T →
          ∀ τ : ℝ, 0 < τ → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
            ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              ∀ᶠ n in atTop, (mk sz z).Pp {ω | ¬ ∀ k, k ≤ K n →
                OptL2aJg (mk sz z) n (gridTime s T K n k) ((mk sz z).Hpath s T K n k ω) ≤
                  ((sz.size n : ℕ) : ℝ) ^ τ *
                      ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) +
                    gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
                      OptL2aJg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω)} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  classical
  have hd0 : 0 < d := by omega
  obtain ⟨C₀, hC₀, hDrift⟩ := stOptL2a_driftg d law Flow mk T0 hd hFl hGrid hHerm hBdata hLWB hNew κ ε 𝔡 hκ hε h𝔡
  refine ⟨C₀, hC₀, ?_⟩
  obtain ⟨κm, hκm⟩ := hSpec κ hκ
  obtain ⟨cB, hcB, hcd⟩ := OptL2Gen_sizedata hFl hBdata hκ hε h𝔡
  intro 𝔠 sz z hflow s T hs hsT hTT hSTLK 𝔠d h𝔠d hcon hS1L hS1W τ hτ D hD
  have hspec := hκm sz ε 𝔠 𝔡 z hflow
  have hadm := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hsize := tendsto_size sz hadm.2.2.1
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hT1 : ∀ n, T n < 1 := fun n => lt_of_le_of_lt (hTT n) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  have hBd := hBd0 sz z hflow T hT0 hTT
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = τ / 8 := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  obtain ⟨CK, hCK0, hCK⟩ := stOptL2a_martingaleg d law Flow mk T0 hd0 hFl hGrid hSpec hBdata hEMP hGM κ ε 𝔡 hκ hε h𝔡
    𝔠 sz z hflow s T hs hsT hTT 𝔠d h𝔠d hcon hS1L hS1W (τ / 2) (by positivity) (D + 4) (by positivity)
  refine ⟨CK, hCK0, fun K hKn => ?_⟩
  obtain ⟨Mart, Rem, hident, hrem, hmartP⟩ := hCK K hKn
  obtain ⟨hK0, -⟩ := OptL2a_grid sz K hKn
  obtain ⟨-, hcardLab3, -, -⟩ := OptL2a_cards sz hsize hCK0 K hKn
  have hE1 := hDrift 𝔠 sz z hflow s T hs hsT hTT 𝔠d h𝔠d hcon hS1L hS1W ε₁ hε₁ CK hCK0 K hKn
  have hG' := hGrid sz z
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hGrid sz z
  have hE2 := Step2EventsGen_grid_whp_zero (mk sz z) (law sz) hlaw (V := fun n => STLab sz n) s T K hs hsT hK0
    (C := 3) (by norm_num) hcardLab3
    (fun n v u H => ‖STLKMg (mk sz z) n u H v.1 v.2‖)
    (fun n v u H => (sz.Bctl n (s n)) ^ 2)
    (fun n v u => (Step2EventsGen_STLKMg_measurable hG' n u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (by
      have h := hSTLK 2 (by norm_num)
      simpa only [Step2EventsGen_STLKMg_eq (mk sz z) hLM] using h)
  have hΞ := HighProbAt.inter hsize hE1 hE2
  -- the null set
  have hNl : ∀ᶠ n in atTop, (mk sz z).Pp {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgAg (mk sz z) s T K n i.1 i.2 k ω =
        STgAg (mk sz z) s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s T K n i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)} = 0 := by
    filter_upwards [hrem] with n hr
    have h1 : ∀ᵐ ω ∂((mk sz z).Pp), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        STgAg (mk sz z) s T K n i.1 i.2 k ω =
          STgAg (mk sz z) s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
            ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s T K n i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := ae_all_iff.2 fun i => hident n i
    have h2 : ∀ᵐ ω ∂((mk sz z).Pp), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := ae_all_iff.2 fun i => hr i
    have hae : ∀ᵐ ω ∂((mk sz z).Pp), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        (STgAg (mk sz z) s T K n i.1 i.2 k ω =
          STgAg (mk sz z) s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
            ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s T K n i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω) ∧
        ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := by
      filter_upwards [h1, h2] with ω a b i k hk
      exact ⟨a i k hk, b i k hk⟩
    exact ae_iff.1 hae
  -- the constants of the final comparison
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = κm⁻¹ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; exact (inv_pos.2 hspec.1).le
  have hbigE : ∀ᶠ n in atTop, q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (ε₁ / 2) :=
    ST_size_pow_big sz hsize (a := ε₁ / 2) (M := q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)))
      (by positivity)
  have hMge : ∀ᶠ n in atTop, 2 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ :=
    ST_size_pow_big sz hsize (a := ε₁) (M := 2) hε₁
  have hfr : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-(2 - 5 / 4 : ℝ)) ≤ cB ^ (5 / 4 : ℝ) :=
    ST_size_pow_small sz hsize (by norm_num) (Real.rpow_pos_of_pos hcB _)
  have hlf := OptL2a_lam_facts sz hc hε₀ h𝔠d hT1
    (hBd.mono fun n hn => (hn (T n) (hT0 n) le_rfl).2) hcon
  refine OptL2a_prob_combine (mk sz z).Pp sz.size hsize _ hΞ (V := fun _ : ℕ => Unit)
    (fun n _ => {ω | ∃ i : STLab sz n, ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (OptL2alam sz s T n) ^ (5 / 4 : ℝ) < ‖Mart n i k ω‖})
    (fun n => {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgAg (mk sz z) s T K n i.1 i.2 k ω =
        STgAg (mk sz z) s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s T K n i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)})
    hD (Dm := D + 4) (by linarith) (by filter_upwards [hmartP] with n hn _ using hn) ?_ hNl _ ?_
  · filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    simpa using Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 3)
  filter_upwards [hsize.eventually (eventually_ge_atTop 1), hBd, hlf, hcon, hMge, hbigE, hfr]
    with n hN1 hbdn hlfn hconn hM hbig hfrn
  intro ω hω
  by_contra hcon'
  have hΞω := fun h => hcon' (Or.inl (Or.inl h))
  obtain ⟨hdr, hi⟩ := not_not.1 hΞω
  have hnB : ω ∉ ({ω | ∃ i : STLab sz n, ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (OptL2alam sz s T n) ^ (5 / 4 : ℝ) < ‖Mart n i k ω‖} :
        Set (PathΩ sz)) := fun hB => hcon' (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨(), hB⟩)))
  have hnN := fun h => hcon' (Or.inr h)
  have hQ : ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgAg (mk sz z) s T K n i.1 i.2 k ω =
        STgAg (mk sz z) s T K n i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg (mk sz z) s T K n i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := by
    by_contra h
    exact hnN h
  -- the numbers at `n`
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hmI : 0 < ((mk sz z).m n).im := lt_of_lt_of_le hspec.1 (hspec.2.1 n)
  have hη : ∀ t, (mk sz z).eta n t = (1 - t) * ((mk sz z).m n).im := hspec.2.2 n
  obtain ⟨hlampos, hlam1, hlamge, -⟩ := OptL2a_lam_basic sz n hcB (hs1 n) (hT1 n) (hsT n) hN1'
    (hbdn (T n) (hT0 n) le_rfl) hlfn hc.le
  obtain ⟨-, hw5, -, hw6⟩ := OptL2a_w_pow hlampos
  have hw0 : 0 < OptL2alam sz s T n ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlampos _
  have hw1 : OptL2alam sz s T n ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one hlampos.le hlam1 (by norm_num)
  have hrfl : ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 := by
    rw [hw5]; exact OptL2a_floor hcB hN1' hlamge (by norm_num) hfrn
  have hxM := OptL2a_x_le sz n hq0 hε₁ hcB (hT1 n) (hsT n) hN1' (hbdn (T n) (hT0 n) le_rfl)
    hc.le h𝔠d hconn hbig
  have hρ1 : 1 ≤ (1 - s n) / (1 - T n) := by
    rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
  have hx0 : 0 ≤ q * Real.log ((1 - s n) / (1 - T n)) := mul_nonneg hq0 (Real.log_nonneg hρ1)
  have hqim : (((mk sz z).m n).im)⁻¹ ≤ q := by
    rw [hqdef]; exact inv_anti₀ hspec.1 (hspec.2.1 n)
  have hY : OptL2alam sz s T n ^ (3 / 2 : ℝ) ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 := by
    rw [← hw6]; exact pow_le_pow_of_le_one hw0.le hw1 (by norm_num)
  have hM4 : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 4 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; rw [hε₁def]; push_cast; ring
  have hM8 : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 8 = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; rw [hε₁def]; push_cast; ring
  have hα := OptL2a_alpha_arith (M := ((sz.size n : ℕ) : ℝ) ^ ε₁) (B2 := (sz.Bctl n (s n)) ^ 2)
    (w := OptL2alam sz s T n ^ (1 / 4 : ℝ)) (Y := OptL2alam sz s T n ^ (3 / 2 : ℝ))
    (x := q * Real.log ((1 - s n) / (1 - T n))) (r := ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ))
    (Mb := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * OptL2alam sz s T n ^ (5 / 4 : ℝ)) hM (sq_nonneg _) hw0
    hY hx0 hxM hrfl (by rw [hM4, hw5])
  rw [hM8, hw5] at hα
  have hM0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  refine hω (OptL2Gen_pathwise (mk sz z) hC₀.le s T K n hη hmI (hsT n) (hT1 n) (hK0 n) (Mart n)
    (Rem n) ω (a₀ := ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ 2)
    (r₀ := ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)) (Mx := ((sz.size n : ℕ) : ℝ) ^ ε₁)
    (Y := OptL2alam sz s T n ^ (3 / 2 : ℝ)) (q := q) (Lg := Real.log ((1 - s n) / (1 - T n)))
    (Mb := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * OptL2alam sz s T n ^ (5 / 4 : ℝ))
    (α := ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (s n)) ^ 2 + OptL2alam sz s T n ^ (5 / 4 : ℝ)))
    (mul_nonneg hM0 (sq_nonneg _)) (Real.rpow_nonneg hN0.le _) hM0 (Real.rpow_nonneg hlampos.le _)
    hqim le_rfl (by linarith) hdr (fun i => hi i)
    (fun i k hk => not_lt.1 fun h => hnB ⟨i, k, hk, h⟩)
    (fun i k hk => (hQ i k hk).2) (fun i k hk => (hQ i k hk).1))


/-! ## 5. The statement `STOptL2gL` from `STLWBgL`, `STEMn2PolygL`, `STGridMartgL` and `lem:newKLK` -/

section Restrict

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- (2.85) `lRB1` on `[s,t]` gives (2.85) `lRB1` on `[s,T]` for a pointwise smaller end `T ≤ t` (band `OptL2b_loop_restrict`). -/
private theorem OptL2Gen_loop_restrict {s t T : ℕ → ℝ} (hTt : ∀ n, T n ≤ t n) (h : STStep1LoopgL C μ s t) :
    STStep1LoopgL C μ s T := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : TimeIcc s T n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) =>
      ((⟨p.1.1, p.1.2.1, (p.1.2.2).trans (hTt n)⟩ : TimeIcc s t n), p.2))

/-- (2.86) `Gtmwc` on `[s,t]` gives (2.86) `Gtmwc` on `[s,T]`, `T ≤ t` (band `OptL2b_weak_restrict`). -/
private theorem OptL2Gen_weak_restrict {s t T : ℕ → ℝ} (hTt : ∀ n, T n ≤ t n) (h : STStep1WeakgL C μ s t) :
    STStep1WeakgL C μ s T := by
  unfold STStep1WeakgL PrecL at h ⊢
  exact StochDomAt.precomp_param h
    (fun n (p : TimeIcc s T n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      ((⟨p.1.1, p.1.2.1, (p.1.2.2).trans (hTt n)⟩ : TimeIcc s t n), p.2))

end Restrict

section JModel

variable {d : ℕ} {sz : Sizes d}

/-- `J` is a measurable function of the fine matrix (band `OptL2b_J_measurable`; `Step2EventsGen_Grid`). -/
private theorem OptL2Gen_J_measurable {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} (hG : Step2EventsGen_Grid Cm μ) (n : ℕ)
    (u : ℝ) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => OptL2aJg Cm n u H) := by
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset (STLab sz n)))
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (f := fun (i : STLab sz n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖STLKMg Cm n u H i.1 i.2‖) (fun i _ => (Step2EventsGen_STLKMg_measurable hG n u i.1 i.2).norm)
  convert h using 1
  ext H
  have := Finset.sup'_apply (s := (Finset.univ : Finset (STLab sz n)))
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun (i : STLab sz n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖STLKMg Cm n u H i.1 i.2‖) H
  exact this.symm

/-- The failure event of `PrecL` at the section `T` (union over the labels inside) is the event `N^τ B < J` of the model matrix `Hm`
(band `OptL2b_badSet_eq`; `Step2EventsGen_Grid`, second clause). -/
private theorem OptL2Gen_badSet_eq {Cm : Step2Mat sz}
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω,
      Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω) (n : ℕ) (T τ B : ℝ) :
    {ω : sz.SeqΩ | ∃ v : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ τ * B <
        ‖Cm.L n T v.1 v.2 ω - Cm.K n T v.1 v.2‖} =
      {ω : sz.SeqΩ | ((sz.size n : ℕ) : ℝ) ^ τ * B < OptL2aJg Cm n T (Hm n T ω)} := by
  ext ω
  change (∃ v : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ τ * B <
      ‖Cm.L n T v.1 v.2 ω - Cm.K n T v.1 v.2‖) ↔
    ((sz.size n : ℕ) : ℝ) ^ τ * B < OptL2aJg Cm n T (Hm n T ω)
  unfold OptL2aJg
  refine Iff.trans ?_ (Finset.lt_sup'_iff (s := (Finset.univ : Finset (STLab sz n))) _).symm
  simp only [Finset.mem_univ, true_and]
  simp only [Step2EventsGen_STLKMg_eq Cm hLM]

end JModel

/-- **(3.39) `eq:opt_L2` from its ingredients, over a carrier family** (proof via (3.38) `lokis2`; band
`stOptL2_of_pins`), conclusion `STOptL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0`.  Carrier facts: `Step2EventsGen_Flow`,
`Step2EventsGen_Grid`, `DecayGen_Spec` (family form) and the Hermitian walk (inline).  Statements used: the size
data `STBdatagL`; the light-weight statement `STLWBgL`; (3.33) `eq:MG_conclusion` (`STEMn2PolygL`); `lem:newKLK` (`Step2IterGen_NewKLK`);
`Sol_CalL` (Lemma 3.4) + `lem:DIfREP` (`STGridMartgL`).  `𝔠₀ = 1/(8 C₀ + 10)`, `C₀` the constant of `stOptL2a_gronwallg`.  For every time section
`T_n ∈ [s_n, t_n]`: the Grönwall inequality on the grid `[s_n, T_n]` (`stOptL2a_gronwallg`, hypotheses restricted to `[s,T]`),
`ST_gronwall` with `ST_prod_le_rpow` (`J_K ≤ α ρ_T^{C₀}`), the comparison (3.43) `eq:L-K2max` (`OptL2b_arith`), the transfer of the endpoint to
the single-time model (`Step2EventsGen_model_le_path`), and `Step2EventsGen_PT_of_sections`. -/
theorem stOptL2_of_pinsg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hd : 3 ≤ d)
    (hFl : Step2EventsGen_Flow d Flow T0)
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz))
    (hSpec : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm)
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian)
    (hBdata : STBdatagL d Flow T0)
    (hLWB : STLWBgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hEMP : STEMn2PolygL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hNew : Step2IterGen_NewKLK d Flow mk)
    (hGM : STGridMartgL d Flow mk T0) :
    STOptL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 := by
  classical
  intro κ ε 𝔡 hκ hε h𝔡
  obtain ⟨C₀, hC₀, hG⟩ := stOptL2a_gronwallg d law Flow mk T0 hd hFl hGrid hSpec hHerm hBdata hLWB hEMP hNew hGM κ ε 𝔡
    hκ hε h𝔡
  have hd0 : 0 < d := by omega
  have hden : (0 : ℝ) < 8 * C₀ + 10 := by linarith
  refine ⟨1 / (8 * C₀ + 10), by positivity, ?_⟩
  intro 𝔠d h𝔠d0 h𝔠d 𝔠 sz z hflow s t hs hst htl hLK hcon hS1L hS1W
  have hadm := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hsize := tendsto_size sz hadm.2.2.1
  have hc12 : 𝔠d ≤ 1 / 2 := by
    refine h𝔠d.trans ?_
    rw [div_le_div_iff₀ hden (by norm_num)]
    linarith
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htl n) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨cB, hcB, hcd⟩ := OptL2Gen_sizedata hFl hBdata hκ hε h𝔡
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hGrid sz z
  refine Step2EventsGen_PT_of_sections (law sz) (V := fun n => STLab sz n) hst _ _ ?_
  intro tt
  -- the time section `T_n = tt n ∈ [s_n, t_n]`
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℝ, T = fun n => ((tt n : TimeIcc s t n) : ℝ) := ⟨_, rfl⟩
  have hsT : ∀ n, s n ≤ T n := fun n => by rw [hTdef]; exact (tt n).2.1
  have hTt : ∀ n, T n ≤ t n := fun n => by rw [hTdef]; exact (tt n).2.2
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hTl : ∀ n, T n ≤ T0 sz z n := fun n => (hTt n).trans (htl n)
  have hT1 : ∀ n, T n < 1 := fun n => lt_of_le_of_lt (hTt n) (ht1 n)
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  have hconT := OptL2b_con_restrict sz h𝔠d0 hsT hTt ht1 hcon
  have hS1LT := OptL2Gen_loop_restrict (mk sz z).toFlowFM (law sz) hTt hS1L
  have hS1WT := OptL2Gen_weak_restrict (mk sz z).toFlowFM (law sz) hTt hS1W
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
        OptL2aJg (mk sz z) n (T n) ((mk sz z).Hpath s T K n (K n) ω)} ⊆
      {ω | ¬ ∀ k, k ≤ K n →
        OptL2aJg (mk sz z) n (gridTime s T K n k) ((mk sz z).Hpath s T K n k ω) ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
              ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) +
            gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
              OptL2aJg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω)} := by
    intro ω hω hall
    have hβ : ∀ j, j < K n → 0 ≤ C₀ / (1 - gridTime s T K n j) := fun j hj => by
      have hm := ST_gridTime_mem s T K n j (hsT n) (hK0 n) hj.le
      exact div_nonneg hC₀.le (by linarith [hm.2, hT1 n])
    have hGr := ST_gronwall (m := K n) (Δ := gridStep s T K n) hΔ
      (α := fun _ => ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
        ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)))
      (β := fun j => C₀ / (1 - gridTime s T K n j))
      (J := fun j => OptL2aJg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω))
      monotoneOn_const hβ (fun k hk => hall k hk) (K n) le_rfl
    have hprod : ∏ j ∈ Finset.range (K n), (1 + gridStep s T K n * (C₀ / (1 - gridTime s T K n j))) ≤
        ((1 - s n) / (1 - T n)) ^ C₀ := by
      have hlast : s n + (K n : ℝ) * gridStep s T K n = T n := gridTime_last s T K n (hK0 n)
      have h := ST_prod_le_rpow (s := s n) (Δ := gridStep s T K n) (c := C₀) hΔ hC₀.le (k := K n)
        (by rw [hlast]; exact hT1 n)
      rw [hlast] at h
      refine le_trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)) h
      simp only [gridTime, div_eq_mul_inv]
    have hJK : OptL2aJg (mk sz z) n (T n) ((mk sz z).Hpath s T K n (K n) ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
          ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) *
            ((1 - s n) / (1 - T n)) ^ C₀ := by
      have h1 : OptL2aJg (mk sz z) n (gridTime s T K n (K n)) ((mk sz z).Hpath s T K n (K n) ω) ≤
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
        OptL2aJg (mk sz z) n (T n) ((mk sz z).Hpath s T K n (K n) ω) := hω
    rw [← hMM] at hlt
    exact absurd (hlt.trans_le (hJK.trans hA)) (lt_irrefl _)
  -- the transfer to the single-time model
  refine le_trans ?_ hn
  have hmodel := Step2EventsGen_model_le_path (mk sz z) (law sz) hlaw s T K hs hsT hK0 n
    (fun n u H => OptL2aJg (mk sz z) n u H) (fun n u _ => sz.Bctl n u)
    (fun n u => OptL2Gen_J_measurable (hGrid sz z) n u) (fun n u => measurable_const) τ'
    {ω | ¬ ∀ k, k ≤ K n →
      OptL2aJg (mk sz z) n (gridTime s T K n k) ((mk sz z).Hpath s T K n k ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
            ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) +
          gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
            OptL2aJg (mk sz z) n (gridTime s T K n j) ((mk sz z).Hpath s T K n j ω)} hBad
  have hset := OptL2Gen_badSet_eq hLM n (T n) τ' (sz.Bctl n (T n))
  convert hmodel using 2
  rw [hTdef] at hset ⊢
  exact hset


end RBM.BA

end
