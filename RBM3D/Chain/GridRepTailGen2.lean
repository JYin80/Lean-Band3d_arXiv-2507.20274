/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridRepTailGen

/-!
# The two-slot weighted martingale tail over a carrier, part 2 (BA-T row P1b-1, ticket T2471)

Paper: arXiv:2507.20274, `lem:DIfREP`, `(alu9_STime)` (`3_5:218-245`).  Continuation of `Chain/GridRepTailGen.lean`:

* §6 the pathwise inclusion (exact transfer, kernel transfer (f1), proxy transfer (f2)), §7 the core (union over the coarse
  levels and labels), §8 the tail at one size index, §9 **target 2** `stGridWTail2gL_of`
  (`GridRepTailGen_Hyp d Flow mk T0 → STGridWTail2gL d Flow mk T0`), §10 **target 3** (the band: the bridge
  `bandStep2_STGridWTail2`; the discharge of `Ker`, the window, `Inc` and `Hyp` at the band, `gridRepTailGen_hyp_band`),
  §11 compiled nonempty instances at `d = 3`.

Band source: `Path/DifREP3.lean` (T2200, RBM3D `b3c37aae`): `difRep3_pathwise` (`:1457`), `difRep3_core` (`:1678`), `difRep3_tail_at` (`:2245`),
`gridRepWTailQN_holds` (`:2343`), copied and adapted at `Q = ∅`, `m = 2` to the classes `Ker`, `Inc`; the numerical budgets
(`difRep3_budget_*`, `difRep3_Cbig`, `difRep3_eventually_Z`) are reused by `open private`.  CK = `9m + 3D + 22 = 3D + 40`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private difRep3_gridTime_nonneg difRep3_gridTime_le difRep3_gridTime_mono difRep3_K_mul_step difRep3_card_label_le
  difRep3_vc difRep3_vc_ge difRep3_vc_le difRep3_coarse difRep3_Mee difRep3_VQ difRep3_c3 difRep3_PY difRep3_cShift
  difRep3_Cbig difRep3_cShift_nonneg difRep3_budget_shift difRep3_budget_f2 difRep3_budget_f1 difRep3_budget_Y difRep3_budget_Z
  difRep3_eventually_Z difRep3_rpow_CK difRep3_sum_norm_uKer_sub_one difRep3_conj_uKer difRep3_inv_le difRep3_stopW_eq difRep3_memLp_two_of_pow4
  difRep3_measurable_STeeM from RBM3D.Path.DifREP3

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 6. The pathwise inclusion -/

section Pathwise

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

/-- **The pathwise inclusion** (step (g)): at the coarse level `v_p`, `p = ⌈k P/K⌉`, if the first-chaos sums
`Σ_{j<k} ζ^{p,a'}_j` obey the peeled bound and the second-order sums `Σ_{j<k} Σ_b κ^{p,a'}_{j,b} Y_{j,b}` are at most
`x_Y = ρ √δ`, for every label `a'`, then the pin's sum `X_k = Σ_{j<k} (𝒰_{u_j,u_k} ξ_j)_a` is at most
`ρ (A_k + N^{-D})^{1/2} + 2 x_Y`: the exact transfer `X_k = (𝒰_{v_p,u_k} W_k)_a` (`GridRepTailGen_UN_transfer`), the kernel transfer
(f1) `GridRepTailGen_UN_sub_le` and the proxy transfer (f2) `GridRepTailGen_norm_STeeUMg_sub_le` (band `difRep3_pathwise`). -/
theorem GridRepTailGen_pathwise {Z Y : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hK : GridRepTailGen_Ker Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hwin : ∀ u : ℝ, 0 ≤ u → u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (hHerm : ∀ j ω, (Cm.Hpath s t K n j ω).IsHermitian)
    (hQ1 : ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
        ‖STeeMg Cm n u H σ a a'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6)
    {P : ℕ} (hP1 : 1 ≤ P) {ρ₁ : ℝ} (hPρ : 1 / (P : ℝ) ≤ ρ₁) (D : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1)
    (hf2 : difRep3_c3 ((sz.size n : ℕ) : ℝ) 2 * ρ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hf1 : ((2 : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ) * ρ₁) *
        (1 + 16 * ((sz.size n : ℕ) : ℝ) * ρ₁) ^ (2 - 1) *
        (ρ * Real.sqrt (difRep3_VQ ((sz.size n : ℕ) : ℝ) 2 + ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) +
          ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ≤
        ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2))
    (ω : PathΩ sz) {k : ℕ} (hk : k ≤ K n)
    (hdec : ∀ j, j < k → ∀ b, martIncNg Cm s t K n j σ ω b = Z j σ ω b + Y j σ ω b)
    (hZg : ∀ a' : Fin 2 → Zd d (sz.L n),
      ‖∑ j ∈ Finset.range k, GridRepTailGen_zeta Cm s t K n Z σ
          (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
        ρ * (∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ
          (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω +
          ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) ^ (1 / 2 : ℝ))
    (hYg : ∀ a' : Fin 2 → Zd d (sz.L n),
      ‖∑ j ∈ Finset.range k, GridRepTailGen_yinc Cm s t K n Y σ
          (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
        ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) :
    ‖∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n k)
        (martIncNg Cm s t K n j σ ω) a‖ ≤
      ρ * (∑ j ∈ Finset.range k, gridStep s t K n *
          ‖STeeUMg Cm n (gridTime s t K n j) (gridTime s t K n k) (Cm.Hpath s t K n j ω) σ a‖ +
            ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) +
        2 * (ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) := by
  -- notation
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  set p : ℕ := ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ with hp
  set vp : ℝ := difRep3_vc (s n) (t n) P p with hvp
  set uk : ℝ := gridTime s t K n k with huk
  -- the coarse index
  obtain ⟨hpP, hukvp, hvpuk⟩ := difRep3_coarse s t K n hst hK0 hP1 hk
  have hvp_t : vp ≤ t n := difRep3_vc_le hst hP1 hpP
  have huk0 : 0 ≤ uk := difRep3_gridTime_nonneg hs0 hst k
  have hvp0 : 0 ≤ vp := huk0.trans hukvp
  have hvp1 : vp < 1 := hvp_t.trans_lt ht1
  have hukt : uk ≤ t n := difRep3_gridTime_le hst hK0 hk
  have huk1 : uk < 1 := hukt.trans_lt ht1
  have hts : t n - s n ≤ 1 := by linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
  have hvpuk' : vp - uk ≤ ρ₁ :=
    hvpuk.trans ((div_le_div_of_nonneg_right hts hP0.le).trans hPρ)
  have hvp16 : (1 - vp)⁻¹ ≤ 16 * N := hwin vp hvp0 hvp_t
  have huk16 : (1 - uk)⁻¹ ≤ 16 * N := hwin uk huk0 hukt
  have hρ₁ : 0 ≤ ρ₁ := (div_nonneg zero_le_one hP0.le).trans hPρ
  -- `δ`, `x_Y`
  have hND : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  set δ : ℝ := N ^ (-D) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  set xY : ℝ := ρ * Real.sqrt δ with hxY
  have hxY0 : 0 ≤ xY := mul_nonneg hρ (Real.sqrt_nonneg _)
  -- Step 1: the exact transfer
  set ξ : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ := fun j => martIncNg Cm s t K n j σ ω with hξ
  have hT := GridRepTailGen_UN_transfer hK.1 σ hvp0 hvp1 huk0 huk1 k (fun j => gridTime s t K n j) ξ
  set W : (Fin 2 → Zd d (sz.L n)) → ℂ :=
    ∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) vp (ξ j) with hWdef
  have hX : ∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) uk (ξ j) a =
      Step2Gen_UN Cm.toFlowFM n σ vp uk W a := by
    rw [← hT, Finset.sum_apply]
  have hXe : ∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n k)
        (martIncNg Cm s t K n j σ ω) a = Step2Gen_UN Cm.toFlowFM n σ vp uk W a := hX
  rw [hXe]
  -- Step 2: the label sums
  have hW : ∀ a' : Fin 2 → Zd d (sz.L n), W a' =
      ∑ j ∈ Finset.range k, GridRepTailGen_zeta Cm s t K n Z σ vp a' j ω +
        ∑ j ∈ Finset.range k, GridRepTailGen_yinc Cm s t K n Y σ vp a' j ω := by
    intro a'
    rw [hWdef, Finset.sum_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.1 hj
    have hon : gridTime s t K n j ≤ vp := (difRep3_gridTime_mono hst hjk.le).trans hukvp
    simp only [Step2Gen_UN, GridRepTailGen_zeta, GridRepTailGen_yinc, GridRepTailGen_kap,
      GridRepTailGen_kp, hon, ↓reduceIte, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ξ j b = Z j σ ω b + Y j σ ω b := hdec j hjk b
    rw [this]; ring
  -- Step 3: the crude bound on `‖W‖_∞`
  have hVQ0 : 0 ≤ difRep3_VQ N 2 := by unfold difRep3_VQ difRep3_Mee; positivity
  have hkΔ : (k : ℝ) * Δ ≤ 1 :=
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast hk : (k : ℝ) ≤ K n) hΔ)).trans hKΔ
  have haSum : ∀ a' : Fin 2 → Zd d (sz.L n),
      ∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a' j ω ≤ difRep3_VQ N 2 := by
    intro a'
    have hterm : ∀ j ∈ Finset.range k,
        GridRepTailGen_aSeq Cm s t K n σ vp a' j ω ≤ Δ * difRep3_VQ N 2 := fun j hj =>
      GridRepTailGen_aSeq_le hK hs0 hst hK0 ((Finset.mem_range.1 hj).le.trans hk) (hHerm j) hQ1 σ hvp1 hvp16 a' ω
    calc ∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a' j ω
        ≤ ∑ j ∈ Finset.range k, Δ * difRep3_VQ N 2 := Finset.sum_le_sum hterm
      _ = (k : ℝ) * Δ * difRep3_VQ N 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1 * difRep3_VQ N 2 := mul_le_mul_of_nonneg_right hkΔ hVQ0
      _ = difRep3_VQ N 2 := one_mul _
  have haSum0 : ∀ a' : Fin 2 → Zd d (sz.L n),
      0 ≤ ∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a' j ω := fun a' =>
    Finset.sum_nonneg fun j _ => GridRepTailGen_aSeq_nonneg hst σ vp a' j ω
  have hZ' : ∀ a' : Fin 2 → Zd d (sz.L n),
      ‖∑ j ∈ Finset.range k, GridRepTailGen_zeta Cm s t K n Z σ vp a' j ω‖ ≤
        ρ * Real.sqrt (difRep3_VQ N 2 + δ) := by
    intro a'
    refine (hZg a').trans (mul_le_mul_of_nonneg_left ?_ hρ)
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by linarith [haSum a'])
  have hWa : ∀ a' : Fin 2 → Zd d (sz.L n), ‖W a'‖ ≤ ρ * Real.sqrt (difRep3_VQ N 2 + δ) + xY := by
    intro a'
    rw [hW a']
    exact (norm_add_le _ _).trans (add_le_add (hZ' a') (hYg a'))
  have hWmax0 : 0 ≤ ρ * Real.sqrt (difRep3_VQ N 2 + δ) + xY := by positivity
  have hWsup : ‖W‖ ≤ ρ * Real.sqrt (difRep3_VQ N 2 + δ) + xY :=
    (pi_norm_le_iff_of_nonneg hWmax0).2 hWa
  -- Step 4: the kernel transfer (f1)
  have hε : |uk - vp| * (1 - uk)⁻¹ ≤ 16 * N * ρ₁ := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    calc (vp - uk) * (1 - uk)⁻¹ ≤ ρ₁ * (16 * N) :=
          mul_le_mul hvpuk' huk16 (inv_nonneg.2 (by linarith)) hρ₁
      _ = 16 * N * ρ₁ := by ring
  have hf := GridRepTailGen_UN_sub_le hK σ huk0 huk1 hε W a
  have herr : ‖Step2Gen_UN Cm.toFlowFM n σ vp uk W a - W a‖ ≤ ρ * Real.sqrt δ := by
    refine hf.trans ?_
    have hc0 : 0 ≤ ((2 : ℕ) : ℝ) * (16 * N * ρ₁) * (1 + 16 * N * ρ₁) ^ (2 - 1) := by positivity
    exact (mul_le_mul_of_nonneg_left hWsup hc0).trans hf1
  -- Step 5: the proxy transfer (f2)
  have hc3 : 0 ≤ difRep3_c3 N 2 := by unfold difRep3_c3; positivity
  have hAk : ∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a j ω ≤
      ∑ j ∈ Finset.range k, Δ * ‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖ +
        N ^ (-D) / 4 := by
    have hterm : ∀ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a j ω ≤
        Δ * ‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖ +
          Δ * (difRep3_c3 N 2 * ρ₁) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.1 hj
      have hon : gridTime s t K n j ≤ vp := (difRep3_gridTime_mono hst hjk.le).trans hukvp
      have hju : gridTime s t K n j ≤ uk := difRep3_gridTime_mono hst hjk.le
      have hjt : gridTime s t K n j ≤ t n := difRep3_gridTime_le hst hK0 (hjk.le.trans hk)
      have hsub := GridRepTailGen_norm_STeeUMg_sub_le Cm n hK (difRep3_gridTime_nonneg hs0 hst j) hju
        hukvp hvp1 huk16 hvp16
        (fun σ a a' => hQ1 _ (difRep3_gridTime_nonneg hs0 hst j) hjt _ (hHerm j ω) σ a a') σ a
      have h1 : ‖STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a‖ ≤
          ‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖ +
            difRep3_c3 N 2 * ρ₁ := by
        have h0 := norm_sub_norm_le
          (STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a)
          (STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a)
        have h2 : difRep3_c3 N 2 * (vp - uk) ≤ difRep3_c3 N 2 * ρ₁ :=
          mul_le_mul_of_nonneg_left hvpuk' hc3
        linarith
      unfold GridRepTailGen_aSeq
      simp only [hon, ↓reduceIte]
      calc Δ * ‖STeeUMg Cm n (gridTime s t K n j) vp (Cm.Hpath s t K n j ω) σ a‖
          ≤ Δ * (‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖ +
            difRep3_c3 N 2 * ρ₁) := mul_le_mul_of_nonneg_left h1 hΔ
        _ = _ := by ring
    calc ∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a j ω
        ≤ ∑ j ∈ Finset.range k, (Δ * ‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖ +
            Δ * (difRep3_c3 N 2 * ρ₁)) := Finset.sum_le_sum hterm
      _ = ∑ j ∈ Finset.range k, Δ * ‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖ +
            (k : ℝ) * (Δ * (difRep3_c3 N 2 * ρ₁)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range k, Δ * ‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖ +
            N ^ (-D) / 4 := by
          have hc3ρ : 0 ≤ difRep3_c3 N 2 * ρ₁ := mul_nonneg hc3 hρ₁
          have : (k : ℝ) * (Δ * (difRep3_c3 N 2 * ρ₁)) = ((k : ℝ) * Δ) * (difRep3_c3 N 2 * ρ₁) := by ring
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_right hkΔ hc3ρ, hf2]
  -- the conclusion
  set Ak : ℝ := ∑ j ∈ Finset.range k, Δ * ‖STeeUMg Cm n (gridTime s t K n j) uk (Cm.Hpath s t K n j ω) σ a‖
    with hAkdef
  have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (norm_nonneg _)
  have hT1 : (∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a j ω + δ) ^ (1 / 2 : ℝ) ≤
      (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith [haSum0 a]) (by linarith [hAk]) (by norm_num)
  have hT2 : Real.sqrt δ ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hδ0.le (by linarith) (by norm_num)
  have hWa' : ‖W a‖ ≤ ρ * (∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a j ω + δ) ^
      (1 / 2 : ℝ) + xY := by
    rw [hW a]
    exact (norm_add_le _ _).trans (add_le_add (hZg a) (hYg a))
  calc ‖Step2Gen_UN Cm.toFlowFM n σ vp uk W a‖
      = ‖W a + (Step2Gen_UN Cm.toFlowFM n σ vp uk W a - W a)‖ := by
        congr 1; ring
    _ ≤ ‖W a‖ + ‖Step2Gen_UN Cm.toFlowFM n σ vp uk W a - W a‖ := norm_add_le _ _
    _ ≤ (ρ * (∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n σ vp a j ω + δ) ^
        (1 / 2 : ℝ) + xY) + ρ * Real.sqrt δ := add_le_add hWa' herr
    _ ≤ (ρ * (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) + ρ * Real.sqrt δ) + ρ * Real.sqrt δ := by
        have := mul_le_mul_of_nonneg_left hT1 hρ
        linarith
    _ = ρ * (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) + 2 * (ρ * Real.sqrt δ) := by ring

end Pathwise

/-! ## 7. The core: the union over the coarse levels and the labels -/

section Core

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

/-- The `Y` constant: `2000 (S C₂)² N⁸ = P_Y` at `S = (32 N)^2`, `C₂ = 6 N (16 N)^4` (`difRep3_PY N 2`). -/
theorem GridRepTailGen_PY_le (N : ℝ) :
    2000 * ((32 * N) ^ 2 * (6 * N * (16 * N) ^ 4)) ^ 2 * N ^ 8 ≤ difRep3_PY N 2 := by
  refine le_of_eq ?_
  unfold difRep3_PY; push_cast; ring

/-- **The tail at one size index and one label** (steps (c)-(g)): given the numerical budgets, the window and the classes,
the pin's event is contained, up to a null set, in the union over the coarse levels `p ≤ P` and the labels `a'` of the bad
events of the `Z` part (peeling) and of the `Y` part (Doob); band `difRep3_core`. -/
theorem GridRepTailGen_core {Z Y : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hProb : IsProbabilityMeasure Cm.Pp)
    (hdec : ∀ j σ, ∀ᵐ ω ∂Cm.Pp, ∀ b, martIncNg Cm s t K n j σ ω b = Z j σ ω b + Y j σ ω b)
    (hZ : GridRepTailGen_Zfields Cm s t K n Z) (hY : GridRepTailGen_Yfields Cm s t K n Y)
    (hK : GridRepTailGen_Ker Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (hH : ∀ j, Measurable[filt sz j] (Cm.Hpath s t K n j) ∧ ∀ ω, (Cm.Hpath s t K n j ω).IsHermitian)
    (hM : ∀ (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u M σ b b'))
    (hQ1 : ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
        ‖STeeMg Cm n u H σ a a'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6)
    (hQ2 : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
          ‖STeeMg Cm n u' H σ a a' - STeeMg Cm n u H σ a a'‖ ≤
            12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * (u' - u))
    (hwin : ∀ u : ℝ, 0 ≤ u → u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    {P : ℕ} (hP1 : 1 ≤ P) {ρ₁ : ℝ} (hPρ : 1 / (P : ℝ) ≤ ρ₁)
    (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1)
    (hshift : ((32 * ((sz.size n : ℕ) : ℝ)) ^ 2) ^ 2 *
      (((2 : ℕ) : ℝ) * (2 * ((2 : ℕ) : ℝ) + 2) * 16 ^ (2 * 2 + 3) * ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 4)) *
        gridStep s t K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (hf2 : difRep3_c3 ((sz.size n : ℕ) : ℝ) 2 * ρ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hf1 : ((2 : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ) * ρ₁) *
        (1 + 16 * ((sz.size n : ℕ) : ℝ) * ρ₁) ^ (2 - 1) *
        (((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (difRep3_VQ ((sz.size n : ℕ) : ℝ) 2 +
            ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) +
          ((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2))
    (hbY : ((P : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ 2 *
        (4 * (gridStep s t K n * difRep3_PY ((sz.size n : ℕ) : ℝ) 2) /
          (((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ^ 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hbZ : ((P : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ 2 *
        (((⌈difRep3_VQ ((sz.size n : ℕ) : ℝ) 2 / (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)⌉₊ : ℝ) + 1) *
          (4 * Real.exp (-(((sz.size n : ℕ) : ℝ) ^ ε' / 4) ^ 2 / (16 * 2)))) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) :
    Cm.Pp {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
          ‖STeeUMg Cm n (gridTime s t K n j) (gridTime s t K n k) (Cm.Hpath s t K n j ω) i.1 i.2‖ +
            ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n i.1 (gridTime s t K n j) (gridTime s t K n k)
          (martIncNg Cm s t K n j i.1 ω) i.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hND : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  set δ : ℝ := N ^ (-D) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hNε : 1 ≤ N ^ ε' := Real.one_le_rpow hN1 hε'.le
  set ρ : ℝ := N ^ ε' / 4 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ : 0 ≤ ρ := hρ0.le
  set VQ : ℝ := difRep3_VQ N 2 with hVQ
  have hVQ0 : 0 ≤ VQ := by rw [hVQ]; unfold difRep3_VQ difRep3_Mee; positivity
  set Lmax : ℕ := ⌈VQ / δ⌉₊ with hLmax
  set xY : ℝ := ρ * Real.sqrt δ with hxY
  have hxY0 : 0 < xY := mul_pos hρ0 (Real.sqrt_pos.2 hδ0)
  set PY : ℝ := difRep3_PY N 2 with hPY
  have hPY0 : 0 ≤ PY := by rw [hPY]; unfold difRep3_PY; positivity
  obtain ⟨hHm, hHh⟩ : (∀ j, Measurable[filt sz j] (Cm.Hpath s t K n j)) ∧
      ∀ j ω, (Cm.Hpath s t K n j ω).IsHermitian := ⟨fun j => (hH j).1, fun j => (hH j).2⟩
  -- the coarse levels
  have hvp0 : ∀ p : ℕ, 0 ≤ difRep3_vc (s n) (t n) P p := fun p => hs0.trans (difRep3_vc_ge hst P p)
  have hvpt : ∀ p : ℕ, p ≤ P → difRep3_vc (s n) (t n) P p ≤ t n := fun p hp => difRep3_vc_le hst hP1 hp
  have hvp1 : ∀ p : ℕ, p ≤ P → difRep3_vc (s n) (t n) P p < 1 := fun p hp => (hvpt p hp).trans_lt ht1
  have hvp16 : ∀ p : ℕ, p ≤ P → (1 - difRep3_vc (s n) (t n) P p)⁻¹ ≤ 16 * N := fun p hp =>
    hwin _ (hvp0 p) (hvpt p hp)
  -- the shift budget
  have hesum : ∑ j ∈ Finset.range (K n), GridRepTailGen_eSeq (sz := sz) s t K n j ≤ δ := by
    have hc : ((2 : ℕ) : ℝ) * (2 * ((2 : ℕ) : ℝ) + 2) * 16 ^ (2 * 2 + 3) * N ^ (2 * 2 + 4) = 12 * 16 ^ 7 * N ^ 8 := by
      norm_num
    rw [hc] at hshift
    have h2 : ∑ j ∈ Finset.range (K n), GridRepTailGen_eSeq (sz := sz) s t K n j =
        ((K n : ℝ) * Δ) * (((32 * N) ^ 2) ^ 2 * (12 * 16 ^ 7 * N ^ 8 * Δ)) := by
      unfold GridRepTailGen_eSeq
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [h2]
    have hS0 : 0 ≤ ((32 * N) ^ 2) ^ 2 * (12 * 16 ^ 7 * N ^ 8 * Δ) := by positivity
    calc ((K n : ℝ) * Δ) * (((32 * N) ^ 2) ^ 2 * (12 * 16 ^ 7 * N ^ 8 * Δ))
        ≤ 1 * (((32 * N) ^ 2) ^ 2 * (12 * 16 ^ 7 * N ^ 8 * Δ)) := mul_le_mul_of_nonneg_right hKΔ hS0
      _ = ((32 * N) ^ 2) ^ 2 * (12 * 16 ^ 7 * N ^ 8) * Δ := by ring
      _ ≤ δ := hshift
  -- the threshold sums
  have haL : ∀ p : ℕ, p ≤ P → ∀ (a' : Fin 2 → Zd d (sz.L n)) (ω : PathΩ sz),
      ∑ j ∈ Finset.range (K n), GridRepTailGen_aSeq Cm s t K n i.1 (difRep3_vc (s n) (t n) P p) a' j ω ≤
        2 ^ Lmax * δ := by
    intro p hp a' ω
    have hterm : ∀ j ∈ Finset.range (K n),
        GridRepTailGen_aSeq Cm s t K n i.1 (difRep3_vc (s n) (t n) P p) a' j ω ≤ Δ * VQ := fun j hj =>
      GridRepTailGen_aSeq_le hK hs0 hst hK0 (Finset.mem_range.1 hj).le (hHh j) hQ1 i.1 (hvp1 p hp)
        (hvp16 p hp) a' ω
    have hVL : VQ ≤ (Lmax : ℝ) * δ := (div_le_iff₀ hδ0).1 (Nat.le_ceil _)
    have hL2 : (Lmax : ℝ) < 2 ^ Lmax := by exact_mod_cast Nat.lt_two_pow_self
    calc ∑ j ∈ Finset.range (K n),
          GridRepTailGen_aSeq Cm s t K n i.1 (difRep3_vc (s n) (t n) P p) a' j ω
        ≤ ∑ j ∈ Finset.range (K n), Δ * VQ := Finset.sum_le_sum hterm
      _ = (K n : ℝ) * Δ * VQ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1 * VQ := mul_le_mul_of_nonneg_right hKΔ hVQ0
      _ = VQ := one_mul _
      _ ≤ (Lmax : ℝ) * δ := hVL
      _ ≤ 2 ^ Lmax * δ := mul_le_mul_of_nonneg_right hL2.le hδ0.le
  -- the bad events
  set EZ : ℕ → (Fin 2 → Zd d (sz.L n)) → Set (PathΩ sz) := fun p a' =>
    {ω | ∃ k, k ≤ K n ∧ ρ * (∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n i.1
        (difRep3_vc (s n) (t n) P p) a' j ω + δ) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, GridRepTailGen_zeta Cm s t K n Z i.1 (difRep3_vc (s n) (t n) P p) a' j ω‖}
    with hEZ
  set EY : ℕ → (Fin 2 → Zd d (sz.L n)) → Set (PathΩ sz) := fun p a' =>
    {ω | ∃ k, k ≤ K n ∧
      xY ≤ ‖∑ j ∈ Finset.range k, GridRepTailGen_yinc Cm s t K n Y i.1 (difRep3_vc (s n) (t n) P p) a' j ω‖}
    with hEY
  have hZbad : ∀ p : ℕ, p ≤ P → ∀ a' : Fin 2 → Zd d (sz.L n),
      Cm.Pp.real (EZ p a') ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * 2))) :=
    fun p hp a' => GridRepTailGen_Z_tail hProb hZ hK hs0 hst hK0 hH hM hQ2 i.1 (hvp0 p) (hvp1 p hp)
      (hvp16 p hp) a' Lmax hδ0 hρ hesum (haL p hp a')
  have hYbad : ∀ p : ℕ, p ≤ P → ∀ a' : Fin 2 → Zd d (sz.L n),
      Cm.Pp.real (EY p a') ≤ 4 * (Δ * PY) / xY ^ 2 := by
    intro p hp a'
    have h := GridRepTailGen_Y_tail Cm hProb hY i.1
      (fun j => GridRepTailGen_kap Cm s t K n i.1 (difRep3_vc (s n) (t n) P p) a' j)
      (S := (32 * N) ^ 2) (by positivity)
      (fun j => GridRepTailGen_kap_sum_le hK hs0 hst i.1 (hvp1 p hp) (hvp16 p hp) a' j)
      (P := PY) (GridRepTailGen_PY_le N) hxY0
    refine h.trans ?_
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have : (K n : ℝ) * (Δ ^ 2 * PY) = ((K n : ℝ) * Δ) * (Δ * PY) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hKΔ (mul_nonneg hΔ hPY0)
    linarith
  -- the pathwise inclusion, almost surely
  have hae : ∀ᵐ ω ∂Cm.Pp, ∀ j b, martIncNg Cm s t K n j i.1 ω b = Z j i.1 ω b + Y j i.1 ω b :=
    ae_all_iff.2 fun j => hdec j i.1
  have hincl : {ω | ∃ k, k ≤ K n ∧
      N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖STeeUMg Cm n (gridTime s t K n j)
        (gridTime s t K n k) (Cm.Hpath s t K n j ω) i.1 i.2‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n i.1 (gridTime s t K n j) (gridTime s t K n k)
          (martIncNg Cm s t K n j i.1 ω) i.2‖} ≤ᵐ[Cm.Pp]
      ⋃ p ∈ Finset.range (P + 1), ⋃ a' ∈ (Finset.univ : Finset (Fin 2 → Zd d (sz.L n))),
        (EZ p a' ∪ EY p a') := by
    filter_upwards [hae] with ω hω hmem
    obtain ⟨k, hk, hlt⟩ := hmem
    by_contra hnot
    have hgood : ∀ p ∈ Finset.range (P + 1), ∀ a' : Fin 2 → Zd d (sz.L n),
        ω ∉ EZ p a' ∧ ω ∉ EY p a' := by
      intro p hp a'
      by_contra hcon
      apply hnot
      simp only [Set.mem_iUnion]
      refine ⟨p, hp, a', Finset.mem_univ _, ?_⟩
      by_cases h1 : ω ∈ EZ p a'
      · exact Or.inl h1
      · exact Or.inr (by_contra fun h2 => hcon ⟨h1, h2⟩)
    obtain ⟨hpP, -, -⟩ := difRep3_coarse s t K n hst hK0 hP1 hk
    have hmem : ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ ∈ Finset.range (P + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le hpP)
    have hZg : ∀ a' : Fin 2 → Zd d (sz.L n),
        ‖∑ j ∈ Finset.range k, GridRepTailGen_zeta Cm s t K n Z i.1
            (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
          ρ * (∑ j ∈ Finset.range k, GridRepTailGen_aSeq Cm s t K n i.1
            (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω + δ) ^ (1 / 2 : ℝ) := by
      intro a'
      by_contra hcon
      exact (hgood _ hmem a').1 ⟨k, hk, not_le.1 hcon⟩
    have hYg : ∀ a' : Fin 2 → Zd d (sz.L n),
        ‖∑ j ∈ Finset.range k, GridRepTailGen_yinc Cm s t K n Y i.1
            (difRep3_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
          ρ * Real.sqrt δ := by
      intro a'
      by_contra hcon
      exact (hgood _ hmem a').2 ⟨k, hk, (not_le.1 hcon).le⟩
    have hpw := GridRepTailGen_pathwise hK hs0 hst ht1 hK0 i.1 i.2 hwin hHh hQ1 hP1 hPρ D hρ hKΔ hf2 hf1 ω hk
      (fun j _ b => hω j b) hZg hYg
    set Ak : ℝ := ∑ j ∈ Finset.range k, Δ * ‖STeeUMg Cm n (gridTime s t K n j)
      (gridTime s t K n k) (Cm.Hpath s t K n j ω) i.1 i.2‖ with hAkdef
    have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (norm_nonneg _)
    have hT0 : 0 ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hsq : Real.sqrt δ ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hδ0.le (by linarith) (by norm_num)
    have hρ4 : N ^ ε' = 4 * ρ := by rw [hρdef]; ring
    rw [hρ4] at hlt
    nlinarith [mul_le_mul_of_nonneg_left hsq hρ]
  -- the measure
  have hcard : (Fintype.card (Fin 2 → Zd d (sz.L n)) : ℝ) ≤ N ^ 2 := difRep3_card_label_le sz n 2
  have hbound : Cm.Pp.real (⋃ p ∈ Finset.range (P + 1),
      ⋃ a' ∈ (Finset.univ : Finset (Fin 2 → Zd d (sz.L n))), (EZ p a' ∪ EY p a')) ≤ N ^ (-D) := by
    calc Cm.Pp.real (⋃ p ∈ Finset.range (P + 1),
          ⋃ a' ∈ (Finset.univ : Finset (Fin 2 → Zd d (sz.L n))), (EZ p a' ∪ EY p a'))
        ≤ ∑ p ∈ Finset.range (P + 1), Cm.Pp.real
          (⋃ a' ∈ (Finset.univ : Finset (Fin 2 → Zd d (sz.L n))), (EZ p a' ∪ EY p a')) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ p ∈ Finset.range (P + 1), ∑ a' : Fin 2 → Zd d (sz.L n),
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * 2))) + 4 * (Δ * PY) / xY ^ 2) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpP : p ≤ P := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
          refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
          exact (measureReal_union_le _ _).trans (add_le_add (hZbad p hpP a') (hYbad p hpP a'))
      _ = ((P : ℝ) + 1) * (Fintype.card (Fin 2 → Zd d (sz.L n)) : ℝ) *
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * 2))) + 4 * (Δ * PY) / xY ^ 2) := by
          simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((P : ℝ) + 1) * N ^ 2 *
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * 2))) + 4 * (Δ * PY) / xY ^ 2) := by
          have h0 : (0 : ℝ) ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * 2))) +
              4 * (Δ * PY) / xY ^ 2 := by positivity
          have hP0 : (0 : ℝ) ≤ (P : ℝ) + 1 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hP0) h0
      _ = ((P : ℝ) + 1) * N ^ 2 * (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * 2)))) +
          ((P : ℝ) + 1) * N ^ 2 * (4 * (Δ * PY) / xY ^ 2) := by ring
      _ ≤ N ^ (-D) / 2 + N ^ (-D) / 4 := add_le_add hbZ hbY
      _ ≤ N ^ (-D) := by linarith
  calc Cm.Pp {ω | ∃ k, k ≤ K n ∧
        N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖STeeUMg Cm n (gridTime s t K n j)
          (gridTime s t K n k) (Cm.Hpath s t K n j ω) i.1 i.2‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n i.1 (gridTime s t K n j) (gridTime s t K n k)
          (martIncNg Cm s t K n j i.1 ω) i.2‖}
      ≤ Cm.Pp (⋃ p ∈ Finset.range (P + 1),
          ⋃ a' ∈ (Finset.univ : Finset (Fin 2 → Zd d (sz.L n))), (EZ p a' ∪ EY p a')) :=
        measure_mono_ae hincl
    _ = ENNReal.ofReal (Cm.Pp.real (⋃ p ∈ Finset.range (P + 1),
          ⋃ a' ∈ (Finset.univ : Finset (Fin 2 → Zd d (sz.L n))), (EZ p a' ∪ EY p a'))) := by
        rw [ofReal_measureReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hbound

end Core

/-! ## 8. The tail at one size index -/

section TailAt

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

/-- **The tail at one size index**: given the window, the classes at `n`, `K ≥ N^{3D+40}` (`CK = 9m + 3D + 22`, `m = 2`),
`N ≥ N₀(2)` and the `Z` budget, the pin's event has probability at most `N^{-D}`, for the label `(σ, a)`, with the coarse grid
`P = ⌈N^{14} N^D⌉` (`C' = 4m + D + 6`); band `difRep3_tail_at`. -/
theorem GridRepTailGen_tail_at {Z Y : ℕ → (Fin 2 → Bool) → PathΩ sz → (Fin 2 → Zd d (sz.L n)) → ℂ}
    (hProb : IsProbabilityMeasure Cm.Pp)
    (hdec : ∀ j σ, ∀ᵐ ω ∂Cm.Pp, ∀ b, martIncNg Cm s t K n j σ ω b = Z j σ ω b + Y j σ ω b)
    (hZ : GridRepTailGen_Zfields Cm s t K n Z) (hY : GridRepTailGen_Yfields Cm s t K n Y)
    (hK : GridRepTailGen_Ker Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK0 : K n ≠ 0)
    (hH : ∀ j, Measurable[filt sz j] (Cm.Hpath s t K n j) ∧ ∀ ω, (Cm.Hpath s t K n j ω).IsHermitian)
    (hM : ∀ (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      Measurable (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u M σ b b'))
    (hQ1 : ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
        ‖STeeMg Cm n u H σ a a'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6)
    (hQ2 : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
          ‖STeeMg Cm n u' H σ a a' - STeeMg Cm n u H σ a a'‖ ≤
            12 * 16 ^ 7 * ((sz.size n : ℕ) : ℝ) ^ 8 * (u' - u))
    (hwin : ∀ u : ℝ, 0 ≤ u → u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    (hKN : ((sz.size n : ℕ) : ℝ) ^ (3 * D + 40) ≤ K n)
    (hbig : difRep3_Cbig 2 ≤ ((sz.size n : ℕ) : ℝ))
    (hZb : 24 * (2 * difRep3_VQ 1 2 + 2) *
        (((sz.size n : ℕ) : ℝ) ^ (9 * 2 + 9) * (((sz.size n : ℕ) : ℝ) ^ D) ^ 3) *
        Real.exp (-(((sz.size n : ℕ) : ℝ) ^ ε' / 4) ^ 2 / (16 * 2)) ≤ 1)
    (i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) :
    Cm.Pp {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
          ‖STeeUMg Cm n (gridTime s t K n j) (gridTime s t K n k) (Cm.Hpath s t K n j ω) i.1 i.2‖ +
            ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n i.1 (gridTime s t K n j) (gridTime s t K n k)
          (martIncNg Cm s t K n j i.1 ω) i.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ0 : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hKΔ : (K n : ℝ) * Δ ≤ 1 := by
    rw [hΔdef, difRep3_K_mul_step s t K n hK0]; linarith
  set ND : ℝ := N ^ D with hNDdef
  have hND1 : 1 ≤ ND := Real.one_le_rpow hN1 hD.le
  have hND0 : 0 < ND := by linarith
  have hNmD : N ^ (-D) = ND⁻¹ := Real.rpow_neg hN0.le D
  have hΔN : Δ * (N ^ (9 * 2 + 22) * ND ^ 3) ≤ 1 := by
    have h1 : N ^ (9 * ((2 : ℕ) : ℝ) + 3 * D + 22) = N ^ (9 * 2 + 22) * ND ^ 3 :=
      difRep3_rpow_CK hN0 2 D
    have h2 : N ^ (9 * ((2 : ℕ) : ℝ) + 3 * D + 22) = N ^ (3 * D + 40) := by
      congr 1; push_cast; ring
    calc Δ * (N ^ (9 * 2 + 22) * ND ^ 3) = Δ * N ^ (9 * ((2 : ℕ) : ℝ) + 3 * D + 22) := by rw [h1]
      _ = Δ * N ^ (3 * D + 40) := by rw [h2]
      _ ≤ Δ * K n := mul_le_mul_of_nonneg_left hKN hΔ0
      _ = (K n : ℝ) * Δ := mul_comm _ _
      _ ≤ 1 := hKΔ
  -- the coarse grid
  set X : ℝ := N ^ (4 * 2 + 6) * ND with hXdef
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) hND1
  have hX0 : 0 < X := by linarith
  set P : ℕ := ⌈X⌉₊ with hPdef
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hX0))
  have hXP : X ≤ (P : ℝ) := Nat.le_ceil X
  have hP3 : (P : ℝ) + 1 ≤ 3 * X := by
    have := Nat.ceil_lt_add_one hX0.le
    linarith
  have hPρ : 1 / (P : ℝ) ≤ X⁻¹ := by
    rw [← one_div]; exact one_div_le_one_div_of_le hX0 hXP
  -- the constants
  have hcs := difRep3_cShift_nonneg 2
  have hc3 : 0 ≤ difRep3_c3 1 2 := by unfold difRep3_c3; positivity
  have hVQ1 : 0 ≤ difRep3_VQ 1 2 := by unfold difRep3_VQ difRep3_Mee; positivity
  have hPY1 : 0 ≤ difRep3_PY 1 2 := by unfold difRep3_PY; positivity
  have hb64 : 0 ≤ 64 * ((2 : ℕ) : ℝ) * 2 ^ 2 + 128 * ((2 : ℕ) : ℝ) * 2 ^ 2 * difRep3_VQ 1 2 := by positivity
  have hbig_shift : 2 * difRep3_cShift 2 ≤ N := by unfold difRep3_Cbig at hbig; linarith
  have hbig_f2 : 4 * difRep3_c3 1 2 ≤ N := by unfold difRep3_Cbig at hbig; linarith
  have hbig_f1 : 64 * ((2 : ℕ) : ℝ) * 2 ^ 2 + 128 * ((2 : ℕ) : ℝ) * 2 ^ 2 * difRep3_VQ 1 2 ≤ N := by
    unfold difRep3_Cbig at hbig; linarith
  have hbig_Y : 1536 * difRep3_PY 1 2 ≤ N := by unfold difRep3_Cbig at hbig; linarith
  have hm1 : 1 ≤ 2 := by norm_num
  have hρ0 : 0 ≤ N ^ ε' / 4 := by positivity
  have hρ14 : 1 / 4 ≤ N ^ ε' / 4 := by
    have := Real.one_le_rpow hN1 hε'.le
    linarith
  refine GridRepTailGen_core hProb hdec hZ hY hK hs0 hst ht1 hK0 hH hM hQ1 hQ2 hwin D ε' hD hε' hP1 hPρ hKΔ
    ?_ ?_ ?_ ?_ ?_ i
  · rw [hNmD]; exact difRep3_budget_shift 2 hN1 hND1 hΔ0 hΔN hbig_shift
  · rw [hNmD]; exact difRep3_budget_f2 2 hm1 hN1 hND1 hbig_f2
  · rw [hNmD]; exact difRep3_budget_f1 2 hm1 hN1 hND1 _ hρ0 hbig_f1
  · rw [hNmD]
    exact difRep3_budget_Y 2 hN1 hND1 hΔ0 hΔN (Nat.cast_nonneg _) hP3 hρ14 hbig_Y
  · rw [hNmD]
    have hVQ0 : 0 ≤ difRep3_VQ N 2 := by unfold difRep3_VQ difRep3_Mee; positivity
    have hceil : ((⌈difRep3_VQ N 2 / (ND⁻¹ / 2)⌉₊ : ℕ) : ℝ) + 1 ≤ 2 * difRep3_VQ N 2 * ND + 2 := by
      have h0 : 0 ≤ difRep3_VQ N 2 / (ND⁻¹ / 2) := by positivity
      have := Nat.ceil_lt_add_one h0
      have e : difRep3_VQ N 2 / (ND⁻¹ / 2) = 2 * difRep3_VQ N 2 * ND := by
        field_simp
      linarith
    have hZ' : 24 * (2 * difRep3_VQ 1 2 + 2) * (N ^ (9 * 2 + 9) * ND ^ 3) *
        Real.exp (-(N ^ ε' / 4) ^ 2 / (16 * 2)) ≤ 1 := hZb
    exact difRep3_budget_Z 2 hN1 hND1 (Real.exp_pos _).le (Nat.cast_nonneg _) hP3
      (Nat.cast_nonneg _) hceil hZ'

end TailAt

/-! ## 9. Target 2: the generic clause 4 -/

/-- **Target 2, `stGridWTail2gL_of`** (`T2471_WTail2`): the classes `Ker`, `Window`, `Inc` along the flow datum give clause 4 of
`STGridRepNAtgL d 2` over the carrier `(Flow, mk, T0)`, for the canonical martingale `Σ_{j<k} martIncNg`, with the grid exponent
`CK = 3 D + 40` (`9m + 3D + 22`, `m = 2`; the band's `gridRepWTailQN_holds` at `Q = ∅`).  Every `d`. -/
theorem stGridWTail2gL_of {d : ℕ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
    {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz} {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}
    (hH : GridRepTailGen_Hyp d Flow mk T0) : STGridWTail2gL d Flow mk T0 := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨3 * D + 40, by positivity, ?_⟩
  intro K hK0 hKN ε' hε'
  obtain ⟨hsize, hev⟩ := hH κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  have hbig := hsize.eventually (eventually_ge_atTop (difRep3_Cbig 2))
  have hZev := hsize.eventually (difRep3_eventually_Z 2 (by norm_num) D ε' hD hε')
  filter_upwards [hKN, hbig, hZev, hev] with n hKNn hbign hZn hevn
  intro i
  obtain ⟨hKer, hWin, hInc⟩ := hevn
  obtain ⟨hN1, hZn⟩ := hZn
  rw [show ((2 : ℕ) : ℝ) = 2 from Nat.cast_ofNat] at hZn
  obtain ⟨hProb, hHp, hM, ⟨Z, Y, hdec, hZf, hYf⟩, hQ1, hQ2⟩ := hInc K (hK0 n)
  have hwin : ∀ u : ℝ, 0 ≤ u → u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ) :=
    fun u hu0 hu => hWin.2 u hu0 hu
  have key := GridRepTailGen_tail_at hProb hdec hZf hYf hKer (hs n) (hst n) hWin.1 (hK0 n) hHp hM hQ1 hQ2
    hwin D ε' hD hε' hKNn hbign hZn i
  have hfun : ∀ (j : ℕ) (ω : PathΩ sz),
      (fun b => (∑ j' ∈ Finset.range (j + 1), martIncNg (mk sz z) s t K n j' i.1 ω b) -
        ∑ j' ∈ Finset.range j, martIncNg (mk sz z) s t K n j' i.1 ω b) =
      martIncNg (mk sz z) s t K n j i.1 ω := fun j ω =>
    funext fun b => Finset.sum_range_succ_sub_sum (fun j' => martIncNg (mk sz z) s t K n j' i.1 ω b)
  simp only [hfun]
  exact key

/-! ## 10. Target 3: the band

(a) the conclusion bridge: the band's `GridRepWTailNAt d 2` is `STGridWTail2gL` at the band carrier; (b) `GridRepTailGen_Ker` (and the
window) at the band; the nonempty instances at the `DifREP3Inst` data. -/

/-- **Target 3 (a), `bandStep2_STGridWTail2`** (the route of `bandStep2_STGridRepNAt`, `Chain/Step2Gen.lean:1075`): the band's clause
(iv) `GridRepWTailNAt d 2` is the generic clause 4 at the band carrier `(STFlow, bandStep2Mat ∘ STflowE, lemT)`. -/
theorem bandStep2_STGridWTail2 (d : ℕ) :
    RBM.Ind.GridRepWTailNAt d 2 ↔
      STGridWTail2gL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
        (fun _ z n => lemT (z n)) := by
  unfold RBM.Ind.GridRepWTailNAt STGridWTail2gL
  have hfm : ∀ (sz : Sizes d) (z : ℕ → ℂ), (bandStep2Mat sz (STflowE z)).toFlowFM = bandFM sz (STflowE z) :=
    fun _ _ => rfl
  simp only [RBM.Ind.difRepMartN, bandStep2_STeeUM, hfm, Step2Kern_UN_band, bandStep2_martIncN]
  exact Iff.rfl

/-- **Target 3 (b), `gridRepTailGen_ker_band`**: the band discharge of `GridRepTailGen_Ker` (K1 `step2Gen_USemigroup_band`,
K2 `norm_uKer_le`, K3 `difRep3_sum_norm_uKer_sub_one` [`open private`], K4 `difRep3_conj_uKer` [`open private`]); the only
hypothesis is `|E n| ≤ 2`. -/
theorem gridRepTailGen_ker_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| ≤ 2) :
    GridRepTailGen_Ker (bandStep2Mat sz E).toFlowFM n := by
  have hfm : (bandStep2Mat sz E).toFlowFM = bandFM sz E := rfl
  have hμ : ∀ σ σ' : Bool, ‖mSigma (E n) σ * mSigma (E n) σ'‖ = 1 := fun σ σ' => by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, mul_one]
  have hnot : ∀ s : Bool, mSigma (E n) (!s) = starRingEnd ℂ (mSigma (E n) s) := fun s => by
    cases s <;> simp [mSigma]
  rw [hfm]
  refine ⟨step2Gen_USemigroup_band sz E n hE, ?_, ?_, ?_⟩
  · intro σ σ' v w hv hvw hw a
    rw [Step2Kern_uKer_band]
    exact (sum_norm_row_le _ a).trans (norm_uKer_le (sz.three_le_L n) hv hvw hw (hμ σ σ'))
  · intro σ σ' s t ht0 ht1 a
    rw [Step2Kern_uKer_band]
    exact difRep3_sum_norm_uKer_sub_one (sz.three_le_L n) (hμ σ σ') ht0 ht1 a
  · intro σ σ' v w hw0 hw1 a b
    rw [Step2Kern_uKer_band, Step2Kern_uKer_band, difRep3_conj_uKer (sz.three_le_L n)
      (norm_t_mul_lt_one hw0 hw1 (hμ σ σ')) a b, hnot, hnot, map_mul]

/-- The spectral height at the band along the flow: `η_u ≥ N^{-1+ε}/16 ≥ 1/(16 N)` for `u ≤ t_n ≤ t₀` (`difRep_flow_bounds`); no
eventuality is needed. -/
theorem gridRepTailGen_eta_band {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (sz : Sizes d) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (htT : ∀ n, t n ≤ lemT (z n)) (n : ℕ) :
    ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (STflowE z n) u := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  intro u hu
  have h := (RBM.Ind.difRep_flow_bounds sz hκ hz n (hu.trans (htT n))).2.2.1
  refine le_trans ?_ h
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_neg_one] at h2
  calc 1 / (16 * ((sz.size n : ℕ) : ℝ)) = ((sz.size n : ℕ) : ℝ)⁻¹ / 16 := by field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 16 := by gcongr

/-- The band discharge of `GridRepTailGen_Window` along the flow (`difRep_flow_bounds`: `η_u ≥ 1/(16 N)`, `η_u ≤ 1 - u`,
`t₀ < 1`). -/
theorem gridRepTailGen_window_band {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (sz : Sizes d) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (htT : ∀ n, t n ≤ lemT (z n)) (n : ℕ) :
    GridRepTailGen_Window (bandStep2Mat sz (STflowE z)) t n := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hη := gridRepTailGen_eta_band hκ hε sz hz t htT n
  refine ⟨(htT n).trans_lt (RBM.Ind.difRep_flow_bounds sz hκ hz n (le_refl _)).2.1, fun u _ hu => ?_⟩
  have h1u : etaT (STflowE z n) u ≤ 1 - u := (RBM.Ind.difRep_flow_bounds sz hκ hz n (hu.trans (htT n))).2.2.2
  exact difRep3_inv_le hN0 (hη u hu) h1u

/-! ### The band discharge of the per-step class `Inc` (the band per-step layer: `ZvecN`, `YvecN`, `hermTestFunLoopN`,
`difRepTail_condMGF_Z`, `difRep2_norm_STeeM_le_N`, `norm_STeeM_shiftN_le`) -/

section BandInc

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The `Z` fields at the band: `Z = ZvecN` (`difRepTail_condMGF_Z` at `k = 2`). -/
theorem gridRepTailGen_zfields_band (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) :
    GridRepTailGen_Zfields (bandStep2Mat sz E) s t K n (fun j σ ω b => RBM.Ind.ZvecN sz E s t K n j σ ω b) := by
  intro j hj σ κ r
  obtain ⟨h1, h2, h3, h4⟩ := RBM.Ind.difRepTail_condMGF_Z sz E s t K n j hE hs0 hst ht1 hj (k := 2) le_rfl σ κ r
  simp only [Nat.cast_ofNat] at h3 h4
  refine ⟨?_, h1, h2, h3, h4⟩
  exact (Finset.stronglyMeasurable_fun_sum _ fun b _ =>
    ((continuous_apply b).comp_stronglyMeasurable
      (RBM.Ind.gridAsm_stronglyMeasurable_ZvecN sz E s t K n j σ)).const_mul _).measurable

open scoped Matrix.Norms.L2Operator in
/-- The `Y` fields at the band: `Y = YvecN` (`AzumaProxyN_YfieldsW` at `S = Σ|κ|`, `C₂ = 6 N (16 N)^4`, `τ ≡ K n`, and
`integral_condExp` for the second moments; band `difRep3_Y_tail`). -/
theorem gridRepTailGen_yfields_band (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) u) :
    GridRepTailGen_Yfields (bandStep2Mat sz E) s t K n (fun j σ ω b => RBM.Ind.YvecN sz E s t K n j σ ω b) := by
  intro j hj σ κ
  have hK : K n ≠ 0 := by omega
  have hu0 := difRep3_gridTime_nonneg (K := K) hs0 hst (j + 1)
  have hu1t : gridTime s t K n (j + 1) ≤ t n := difRep3_gridTime_le hst hK hj
  have hu1 : gridTime s t K n (j + 1) < 1 := hu1t.trans_lt ht1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Smax : ℝ := ∑ c, ‖κ c‖ with hSmax
  have hS0 : 0 ≤ Smax := Finset.sum_nonneg fun c _ => norm_nonneg _
  set C2 : ℝ := ((2 * (2 + 1) : ℕ) : ℝ) * N * (16 * N) ^ (2 + 2) with hC2def
  have hC2e : C2 = 6 * N * (16 * N) ^ 4 := by rw [hC2def]; norm_num
  have hC20 : 0 ≤ C2 := by rw [hC2e]; positivity
  have hη0 : 0 < etaT (E n) (gridTime s t K n (j + 1)) := etaT_pos hE hu1
  have hinv : (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ≤ 16 * N := by
    calc (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ≤ (1 / (16 * N))⁻¹ :=
          inv_anti₀ (by positivity) (hη _ hu1t)
      _ = 16 * N := by rw [one_div, inv_inv]
  have hC2 : ∀ (a' : Fin 2 → Zd d (sz.L n))
      (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (RBM.Ind.loopFamN sz E s t K n j σ a')) M y y‖ ≤ C2 * ‖y‖ ^ 2 := by
    intro a' M y hM hy
    refine ((RBM.Ind.hermTestFunLoopN sz 2 n (E n) (gridTime s t K n (j + 1)) hE hu0 hu1 σ a').2 M y hM
      hy).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hC2def]
    gcongr
  have hτ : ∀ j', MeasurableSet[filt sz j'] {ω : PathΩ sz | j' < (fun _ => K n) ω} := fun j' =>
    MeasurableSet.const _
  have h := RBM.Ind.AzumaProxyN_YfieldsW sz E s t K n j hE hs0 hst ht1 hj σ κ hS0 hC20 le_rfl hC2
    (P := 2000 * (Smax * C2) ^ 2 * N ^ 8) le_rfl (fun _ => K n) hτ
  simp only [difRep3_stopW_eq sz E s t K n j hj σ κ] at h
  obtain ⟨hre0, him0, h4re, h4im, hre2, him2, -, -⟩ := h
  have hYm : StronglyMeasurable[filt sz (j + 1)] (fun ω => ∑ c, κ c * RBM.Ind.YvecN sz E s t K n j σ ω c) :=
    Finset.stronglyMeasurable_fun_sum _ fun c _ =>
      ((continuous_apply c).comp_stronglyMeasurable
        (RBM.Ind.gridAsm_stronglyMeasurable_YvecN sz E s t K n j σ)).const_mul _
  have hq : ∀ (F : PathΩ sz → ℝ),
      (pathP sz)[fun ω => F ω ^ 2 | filt sz j] ≤ᵐ[pathP sz]
        (fun _ => gridStep s t K n ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8)) →
      ∫ ω, (F ω) ^ 2 ∂(pathP sz) ≤ gridStep s t K n ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) := by
    intro F h5
    rw [← integral_condExp ((filt sz).le j) (f := fun ω => F ω ^ 2)]
    calc ∫ ω, ((pathP sz)[fun ω => F ω ^ 2 | filt sz j]) ω ∂(pathP sz)
        ≤ ∫ _ω, gridStep s t K n ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) ∂(pathP sz) :=
          integral_mono_ae integrable_condExp (integrable_const _) h5
      _ = gridStep s t K n ^ 2 * (2000 * (Smax * C2) ^ 2 * N ^ 8) := by simp
  rw [hC2e] at hq
  refine ⟨hYm.measurable, hre0, him0, ?_, ?_, hq _ hre2, hq _ him2⟩
  · exact difRep3_memLp_two_of_pow4
      ((Complex.continuous_re.comp_stronglyMeasurable (hYm.mono ((filt sz).le (j + 1)))).aestronglyMeasurable) h4re
  · exact difRep3_memLp_two_of_pow4
      ((Complex.continuous_im.comp_stronglyMeasurable (hYm.mono ((filt sz).le (j + 1)))).aestronglyMeasurable) h4im

/-- **The band discharge of `GridRepTailGen_Inc`** (`Z = ZvecN`, `Y = YvecN = martIncN - ZvecN`; Q1 `difRep2_norm_STeeM_le_N`;
Q2 `norm_STeeM_shiftN_le` and `difRep2_eeShiftErrN_le`), given the band bulk `|E_n| < 2`, `t_n < 1` and `η_u ≥ 1/(16 N)` for
`u ≤ t_n`. -/
theorem gridRepTailGen_inc_band (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1)
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) u) :
    GridRepTailGen_Inc (bandStep2Mat sz E) s t K n := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  refine ⟨(inferInstance : IsProbabilityMeasure (pathP sz)),
    fun j => ⟨pathH_measurable_filt sz s t K n j, pathH_isHermitian sz s t K n j⟩,
    fun u σ b b' => difRep3_measurable_STeeM sz n (E n) u σ b b',
    ⟨fun j σ ω b => RBM.Ind.ZvecN sz E s t K n j σ ω b, fun j σ ω b => RBM.Ind.YvecN sz E s t K n j σ ω b,
      fun j σ => Eventually.of_forall fun ω b => ?_,
      gridRepTailGen_zfields_band sz E s t K n hE hs0 hst ht1,
      gridRepTailGen_yfields_band sz E s t K n hE hs0 hst ht1 hη⟩, ?_, ?_⟩
  · simp only [RBM.Ind.YvecN, bandStep2_martIncN]; ring
  · intro u hu0 hut H hH σ a a'
    have h := RBM.Ind.difRep2_norm_STeeM_le_N sz n hE (hut.trans_lt ht1) hH (hη u hut) σ a a'
    exact h.trans (le_of_eq (by norm_num))
  · intro u u' hu0 huu' hu't H hH σ a a'
    have h1 := RBM.Ind.norm_STeeM_shiftN_le sz n hE hH huu' (hu't.trans_lt ht1) σ a a'
    have h2 := RBM.Ind.difRep2_eeShiftErrN_le sz n (E n) huu' (hη u' hu't) 2
    refine h1.trans (h2.trans (le_of_eq ?_))
    push_cast
    ring

end BandInc

/-- **Target 3 (b), `gridRepTailGen_hyp_band`** (non-vacuity of the classes): `GridRepTailGen_Hyp` holds at the band carrier along
every flow datum, for every `d`: `SizeTendsto` from the flow, `Ker` (`gridRepTailGen_ker_band`), the window and `Inc`
(`gridRepTailGen_inc_band`) at every `n`. -/
theorem gridRepTailGen_hyp_band (d : ℕ) :
    GridRepTailGen_Hyp d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
      (fun _ z n => lemT (z n)) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  refine ⟨hz.1.2.2.1, Eventually.of_forall fun n => ?_⟩
  have hfl := RBM.Ind.difRep_flow_bounds sz hκ hz n (htT n)
  have hE : |STflowE z n| < 2 := by linarith [hfl.1]
  have ht1 : t n < 1 := (htT n).trans_lt hfl.2.1
  exact ⟨gridRepTailGen_ker_band sz (STflowE z) n (by linarith [hfl.1]),
    gridRepTailGen_window_band hκ hε sz hz t htT n,
    fun K _ => gridRepTailGen_inc_band sz (STflowE z) s t K n hE (hs n) (hst n) ht1
      (gridRepTailGen_eta_band hκ hε sz hz t htT n)⟩

end RBM.BA

namespace RBM.BA.GridRepTailGenInst

open MeasureTheory ProbabilityTheory Filter RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
  RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-! ## 11. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `sz0` (`d = 3`, `L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`, `N_0 = 2097152`) and the flow
block of `Induction/Defs.lean` (`z0`, `flow_z0` with `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `s ≡ 0`, `t ≡ 1/16 ≤ lemT z0`), as in
`DifREP3Inst`.  Target 1 (the classes): `Ker` and the window at the band carrier for every `n`.  Target 3 (a): the band's
`GridRepWTailNAt 3 2` gives the generic clause 4 at the band carrier, and back.  
Target 3 (b)/target 2: `gridRepTailGen_hyp_band` (the classes `Ker`, window, `Inc`, `Hyp` hold at the band carrier along every
flow datum) and `stGridWTail2gL_of` through it, applied at the flow data with `D = 1`, `ε' = 1/10`, `K_n = ⌈N_n^{CK}⌉ + 1`;
no hypothesis stays open. -/

/-- **Target 1 / 3 (b) at the data**: `GridRepTailGen_Ker` at the band carrier along `z0`, every `n` (K1-K4). -/
example : ∀ n, GridRepTailGen_Ker (bandStep2Mat sz0 (STflowE z0)).toFlowFM n := fun n =>
  gridRepTailGen_ker_band sz0 _ n
    ((difRep_flow_bounds sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 n (DifREP3Inst.htT n)).1.trans
      (by norm_num))

/-- **Target 1 at the data**: `GridRepTailGen_Window` at the band carrier along `z0` with `t ≡ 1/16`, every `n`. -/
example : ∀ n, GridRepTailGen_Window (bandStep2Mat sz0 (STflowE z0)) tInst n := fun n =>
  gridRepTailGen_window_band (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) sz0 flow_z0 tInst
    DifREP3Inst.htT n

/-- **Target 1 at the data**: `GridRepTailGen_Inc` at the band carrier along `z0` with `s ≡ 0`, `t ≡ 1/16`, every grid `K` and
every `n`; and `GridRepTailGen_Hyp` at the band carrier (`d = 3`). -/
example : ∀ (K : ℕ → ℕ) (n : ℕ), GridRepTailGen_Inc (bandStep2Mat sz0 (STflowE z0)) sInst tInst K n := fun K n =>
  gridRepTailGen_inc_band sz0 (STflowE z0) sInst tInst K n
    (by linarith [(difRep_flow_bounds sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 n (DifREP3Inst.htT n)).1])
    (DifREP3Inst.hs0 n) (DifREP3Inst.hst n)
    ((DifREP3Inst.htT n).trans_lt (difRep_flow_bounds sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 n
      (DifREP3Inst.htT n)).2.1)
    (gridRepTailGen_eta_band (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) sz0 flow_z0 tInst
      DifREP3Inst.htT n)

example : GridRepTailGen_Hyp 3 (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  gridRepTailGen_hyp_band 3

/-- **Target 3 (a) at `d = 3`**: the band's clause (iv) `GridRepWTailNAt 3 2` (the merged `gridRepWTailN_holds`) is the generic
clause 4 at the band carrier, and conversely. -/
example : STGridWTail2gL 3 (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
    (fun _ z n => lemT (z n)) :=
  (bandStep2_STGridWTail2 3).1 (gridRepWTailN_holds 3 2 le_rfl)

example : GridRepWTailNAt 3 2 :=
  (bandStep2_STGridWTail2 3).2 ((bandStep2_STGridWTail2 3).1 (gridRepWTailN_holds 3 2 le_rfl))

/-- **Target 3 (b) at `d = 3`** (non-vacuity of the classes): `GridRepTailGen_Hyp` at the band carrier, and **target 2** through it:
the generic clause 4 at the band carrier is re-derived without the band's own proof; with target 3 (a) this gives
`gridRepWTailN_holds 3 2` through the classes. -/
example : GridRepWTailNAt 3 2 :=
  (bandStep2_STGridWTail2 3).2 (stGridWTail2gL_of (gridRepTailGen_hyp_band 3))

/-- **Target 2 at the flow data** (`sz0`, `z0`, `s ≡ 0`, `t ≡ 1/16`, `D = 1`, `ε' = 1/10`): the grid exponent `CK` it returns, the
grid `K_n = ⌈N_n^{CK}⌉ + 1`, and the weighted tail bound `≤ N^{-1}` eventually, for every label `(σ, a)`; no hypothesis. -/
theorem inst_stGridWTail2gL_band :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      (∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)),
        (bandStep2Mat sz0 (STflowE z0)).Pp {ω | ∃ k, k ≤ K n ∧
          ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
              (∑ j ∈ Finset.range k, gridStep sInst tInst K n *
                ‖STeeUMg (bandStep2Mat sz0 (STflowE z0)) n (gridTime sInst tInst K n j)
                  (gridTime sInst tInst K n k) ((bandStep2Mat sz0 (STflowE z0)).Hpath sInst tInst K n j ω) i.1 i.2‖ +
                ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
            ‖∑ j ∈ Finset.range k,
              Step2Gen_UN (bandStep2Mat sz0 (STflowE z0)).toFlowFM n i.1
                (gridTime sInst tInst K n j) (gridTime sInst tInst K n k)
                (fun b => (∑ j' ∈ Finset.range (j + 1),
                    martIncNg (bandStep2Mat sz0 (STflowE z0)) sInst tInst K n j' i.1 ω b) -
                  ∑ j' ∈ Finset.range j, martIncNg (bandStep2Mat sz0 (STflowE z0)) sInst tInst K n j' i.1 ω b)
                i.2‖} ≤
          ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)))) := by
  obtain ⟨CK, hCK, h⟩ := stGridWTail2gL_of (gridRepTailGen_hyp_band 3) (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst DifREP3Inst.hs0 DifREP3Inst.hst
    DifREP3Inst.htT 1 one_pos
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 ≠ 0 := fun n => Nat.succ_ne_zero _
  have hKN : ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤
      ((⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 : ℕ) : ℝ) :=
    Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  exact ⟨CK, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1, hK0, hKN,
    h (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) hK0 hKN (1 / 10) (by norm_num)⟩

end RBM.BA.GridRepTailGenInst

end
