/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.IterationsGen
import RBM3D.Induction.IterationsB
import RBM3D.Chain.NQEndFlowGen

/-!
# `lem:iterations` over the flow carrier, second part

Generic forms of `Induction/IterationsB` over a carrier `Cm : Step2Mat sz` and a law `μ`, namespace
`RBM.BA`.  Paper: Lemma 4.11 (`lem:iterations`) and its proof (Subsection 4.5, `subsec:support`).

* The private estimates and obligations of `iterationsB_step` as `…g` versions (`Prec sz` → `PrecL sz μ`,
  `STXiL sz n (E n)` → `STXiLg C n`, `etaT (E n)` → `C.eta n`, `IterationsAScale` →
  `IterationsAScaleg`; the value-level quantities `iterationsB_XLv`, `iterationsB_XLKv` and their bounds
  are model-free and reused by `open private`), and `iterationsB_stepg`: the step with the bootstrap
  hypothesis `STXiBootgL'`; the odd chain obligation reads `Step34Gen_LCompat`,
  `StepDecompGen_LoopForm` and a Hermitian flow matrix (`iterationsA_xiL_odd_leg`).
* `stIterationsgL'_of`, `stIterationsIIgL'_of`: the statements `STIterationsgL'`, `STIterationsIIgL'`
  at `(mkM sz z).toFlowFM`, from the family bundle `IterationsGen2_Fam`; `𝔠d = 1/100`.  The uniform
  `𝒦` bound is rebuilt by `stKbound_timeIccgL` from the statement's own `STKboundgL` hypothesis and the
  law `μ = law sz` (a probability measure).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private iterationsB_Bctl_nonneg iterationsB_XLv iterationsB_XLKv iterationsB_XLv_ge_one iterationsB_XLv_le_pred
  iterationsB_XLv_le iterationsB_XLv_le_chain iterationsB_XLv_four_p iterationsB_XLKv_ge_one iterationsB_XLKv_le
  iterationsB_XLv_le_Z iterationsB_sqrt_prod_le from RBM3D.Induction.IterationsB

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ} {sz : Sizes d} {μ : Measure sz.SeqΩ} (Cf : FlowFM sz)

/-! ## 1. The private estimates and obligations of the step -/

/-- `Ξ̂^{(𝓛)}_m ≺ 1 + T Y` from (4.38) `rela_XILXILK` and `Ξ̂^{(𝓛-𝒦)}_m ≺ Y` (in the proof of Lemma 4.11): the transfer
`1 + B_v Ξ̂^{(𝓛-𝒦)} ≺ 1 + B_v Y ≤ 1 + T Y` for `W^{-d}B_{v,0} ≤ T`. -/
private theorem iterationsB_prec_XL_ofg (hsize : Tendsto sz.size atTop atTop) {s t T : ℕ → ℝ} {m : ℕ}
    (hrela : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω))
    {Y : ∀ n, STPair s t n → ℝ} (hY0 : ∀ n q, 0 ≤ Y n q)
    (hG : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => Y n q))
    (hT : ∀ᶠ n in atTop, ∀ q : STPair s t n, sz.Bctl n q.1.1 ≤ T n) (ht1 : ∀ n, t n < 1) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => 1 + T n * Y n q) := by
  have hGnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ STXiLKg Cf n q.1.1 m ω := fun n q ω => by
    have hu : q.1.1 < 1 := lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n)
    linarith [st_one_le_XiLKg Cf (n := n) (v := q.1.1) m ω (st_Bctl_pos sz (n := n) hu)]
  have hA := iterationsA_prec_one_add_mulg hsize (U := STPair s t) (c := fun n q => sz.Bctl n q.1.1)
    (fun n q => iterationsB_Bctl_nonneg sz n _) hGnn hG
  have hB := StochDomAt.trans hsize hrela hA
  refine iterationsA_prec_mono_rightg hB ?_
  filter_upwards [hT] with n hn q ω
  have := hY0 n q
  have := hn q
  nlinarith [mul_le_mul_of_nonneg_right (hn q) (hY0 n q)]


/-- The weight `ρ_u = max 1 (η_s/η_u)` (equal to `η_s/η_u` on the pairs, where it is `≥ 1`). -/
private noncomputable def iterationsB_rhog (s : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  max 1 (Cf.eta n (s n) / Cf.eta n u)

/-- The quantity bounding `Ξ̂^{(𝓛)}_m` at the size `n` and the endpoint `u`. -/
private noncomputable def iterationsB_XLg (s A T : ℕ → ℝ) (cB cv : ℝ) (N k m n : ℕ) (u : ℝ) : ℝ :=
  iterationsB_XLv (A n) (iterationsB_rhog Cf s n u) (T n) cB cv N k (N + 4) m

/-- The quantity bounding `Ξ̂^{(𝓛-𝒦)}_m`. -/
private noncomputable def iterationsB_XLKg (s A : ℕ → ℝ) (k m n : ℕ) (u : ℝ) : ℝ :=
  iterationsB_XLKv (A n) (iterationsB_rhog Cf s n u) k m

private theorem iterationsB_rhog_ge_one (s : ℕ → ℝ) (n : ℕ) (u : ℝ) : 1 ≤ iterationsB_rhog Cf s n u :=
  le_max_left _ _

private theorem iterationsB_rhog_eq {Cf : FlowFM sz} {s : ℕ → ℝ} {n : ℕ} {u : ℝ} (h : 1 ≤ Cf.eta n (s n) / Cf.eta n u) :
    iterationsB_rhog Cf s n u = Cf.eta n (s n) / Cf.eta n u := max_eq_right h

/-- **The obligations for `m ≤ N+1`**: `Ξ̂^{(𝓛)}_m ≺ 1 + T Y_m` with `Y_1 = 1`, `Y_m = Ψ(m,k)` for `m + 1 ≤ N`
((4.41) `eq:iteration_induc` at `(m,k)`), `Y_m = Ψ(m,k-1)` for `N ≤ m ≤ N+1` (at `(m,k-1)`); (4.65) `sadui_w0`. -/
private theorem iterationsB_obl_shortg (hsize : Tendsto sz.size atTop atTop)
    {s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScaleg Cf s t A T cB cv K) {N k : ℕ}
    (hrela : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω))
    (havg : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 1 ω) (fun _ _ _ => 1))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHypgL Cf μ s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHypgL Cf μ s t A r (k - 1))
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ N + 1) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
      (fun n q _ => iterationsB_XLg Cf s A T cB cv N k m n q.1.2) := by
  set Y : ∀ n, STPair s t n → ℝ := fun n q =>
    if m = 1 then 1 else if m + 1 ≤ N then STPsi (A n) (iterationsB_rhog Cf s n q.1.2) m k
    else STPsi (A n) (iterationsB_rhog Cf s n q.1.2) m (k - 1) with hY
  have hY0 : ∀ n q, 0 ≤ Y n q := by
    intro n q
    have hρ0 : 0 ≤ iterationsB_rhog Cf s n q.1.2 := by linarith [iterationsB_rhog_ge_one Cf s n q.1.2]
    simp only [hY]
    split_ifs
    · norm_num
    · exact iterationsA_STPsi_nonneg (hS.A_nonneg n) hρ0 _ _
    · exact iterationsA_STPsi_nonneg (hS.A_nonneg n) hρ0 _ _
  have hG : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => Y n q) := by
    by_cases hm : m = 1
    · subst hm
      refine iterationsA_prec_mono_rightg havg ?_
      exact Eventually.of_forall fun n q ω => by simp [hY]
    · have hm2' : 2 ≤ m := by omega
      by_cases hmN : m + 1 ≤ N
      · have h : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω)
            (fun n q _ => STPsi (A n) (Cf.eta n (s n) / Cf.eta n q.1.2) m k) := IH1 m hm2' hmN
        refine iterationsA_prec_mono_rightg h ?_
        filter_upwards [hS.rho] with n hn q ω
        have := (hn q).1
        simp only [hY, hm, hmN, ite_true, ite_false]
        rw [iterationsB_rhog_eq this]
      · have h : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω)
            (fun n q _ => STPsi (A n) (Cf.eta n (s n) / Cf.eta n q.1.2) m (k - 1)) := IH2 m hm2' (by omega)
        refine iterationsA_prec_mono_rightg h ?_
        filter_upwards [hS.rho] with n hn q ω
        have := (hn q).1
        simp only [hY, hm, hmN, ite_false]
        rw [iterationsB_rhog_eq this]
  have hT : ∀ᶠ n in atTop, ∀ q : STPair s t n, sz.Bctl n q.1.1 ≤ T n := by
    filter_upwards [hS.Bctl] with n hn q
    exact (hn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).2
  have hmain := iterationsB_prec_XL_ofg Cf hsize (hrela m hm1) hY0 hG hT hS.t_lt_one
  refine iterationsA_prec_mono_rightg hmain (Eventually.of_forall fun n q ω => le_of_eq ?_)
  unfold iterationsB_XLg iterationsB_XLv
  rw [ite_eq_left hm2]

/-- The `≺` of `1 + c ((F₁F₂)(F₂F₃))^{1/2}` from `F_i ≺ X_i` (the four loops `2l₁, 2l₂, 2l₃ = 2l₂, 2l₄` of `(auskoppw2)`). -/
private theorem iterationsB_prec_chain_absg (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {F1 F2 F3 X1 X2 X3 : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ} (hc : ∀ n u, 0 ≤ c n u)
    (hF1 : ∀ n u ω, 0 ≤ F1 n u ω) (hF2 : ∀ n u ω, 0 ≤ F2 n u ω) (hF3 : ∀ n u ω, 0 ≤ F3 n u ω)
    (hX1 : ∀ n u ω, 0 ≤ X1 n u ω) (hX2 : ∀ n u ω, 0 ≤ X2 n u ω) (hX3 : ∀ n u ω, 0 ≤ X3 n u ω)
    (h1 : PrecL sz μ F1 X1) (h2 : PrecL sz μ F2 X2) (h3 : PrecL sz μ F3 X3) :
    PrecL sz μ (fun n u ω => 1 + c n u * ((F1 n u ω * F2 n u ω) * (F2 n u ω * F3 n u ω)) ^ (1 / 2 : ℝ))
      (fun n u ω => 1 + c n u * ((X1 n u ω * X2 n u ω) * (X2 n u ω * X3 n u ω)) ^ (1 / 2 : ℝ)) := by
  have h12 : PrecL sz μ (fun n u ω => F1 n u ω * F2 n u ω) (fun n u ω => X1 n u ω * X2 n u ω) :=
    StochDomAt.mul (ξ₁ := F1) (ξ₂ := F2) (ζ₁ := X1) (ζ₂ := X2) hsize hF2 hX1 h1 h2
  have h23 : PrecL sz μ (fun n u ω => F2 n u ω * F3 n u ω) (fun n u ω => X2 n u ω * X3 n u ω) :=
    StochDomAt.mul (ξ₁ := F2) (ξ₂ := F3) (ζ₁ := X2) (ζ₂ := X3) hsize hF3 hX2 h2 h3
  have hP : PrecL sz μ (fun n u ω => (F1 n u ω * F2 n u ω) * (F2 n u ω * F3 n u ω))
      (fun n u ω => (X1 n u ω * X2 n u ω) * (X2 n u ω * X3 n u ω)) :=
    StochDomAt.mul (ξ₁ := fun n u ω => F1 n u ω * F2 n u ω) (ξ₂ := fun n u ω => F2 n u ω * F3 n u ω)
      (ζ₁ := fun n u ω => X1 n u ω * X2 n u ω) (ζ₂ := fun n u ω => X2 n u ω * X3 n u ω) hsize
      (fun n u ω => mul_nonneg (hF2 n u ω) (hF3 n u ω)) (fun n u ω => mul_nonneg (hX1 n u ω) (hX2 n u ω)) h12 h23
  have hsq := iterationsA_prec_rpowg
    (fun n u ω => mul_nonneg (mul_nonneg (hF1 n u ω) (hF2 n u ω)) (mul_nonneg (hF2 n u ω) (hF3 n u ω)))
    (fun n u ω => mul_nonneg (mul_nonneg (hX1 n u ω) (hX2 n u ω)) (mul_nonneg (hX2 n u ω) (hX3 n u ω)))
    (θ := 1 / 2) (by norm_num) hP
  exact iterationsA_prec_one_add_mulg hsize hc
    (fun n u ω => Real.rpow_nonneg (mul_nonneg (mul_nonneg (hF1 n u ω) (hF2 n u ω))
      (mul_nonneg (hF2 n u ω) (hF3 n u ω))) _) hsq

/-- **The obligation for `m = 2N-1`, `N ≥ 3`** ((4.69) `auskoppw2`): `Ξ̂^{(𝓛)}_{2N-1} ≺ 1 + cv A Z²`, from the
odd chain bound `iterationsA_xiL_odd_le` and the bounds of the four loops `Ξ̂_{2l_i}`, `2 l_i ≤ N+1`. -/
private theorem iterationsB_obl_chaing {Cm : Step2Mat sz}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {E : ℕ → ℝ}
    (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E)
    (hHf : ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf n u ω).IsHermitian) (hsize : Tendsto sz.size atTop atTop)
    {s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScaleg Cm.toFlowFM s t A T cB cv K) {N k : ℕ} (hN3 : 3 ≤ N)
    (hk : 1 ≤ k)
    (hshort : ∀ m, 1 ≤ m → m ≤ N + 1 → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
      (fun n q _ => iterationsB_XLg Cm.toFlowFM s A T cB cv N k m n q.1.2)) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 (2 * N - 1) ω)
      (fun n q _ => iterationsB_XLg Cm.toFlowFM s A T cB cv N k (2 * N - 1) n q.1.2) := by
  have ht1 := hS.t_lt_one
  have hBpos : ∀ n (q : STPair s t n), 0 < sz.Bctl n q.1.1 := fun n q =>
    st_Bctl_pos sz (n := n) (lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n))
  have hFge : ∀ m n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ STXiLg Cm.toFlowFM n q.1.1 m ω := fun m n q ω => by
    linarith [st_one_le_XiLg Cm.toFlowFM (n := n) (v := q.1.1) m ω (hBpos n q)]
  have hXge : ∀ m n (q : STPair s t n), 1 ≤ iterationsB_XLg Cm.toFlowFM s A T cB cv N k m n q.1.2 := fun m n q =>
    iterationsB_XLv_ge_one (hS.A_nonneg n) (by linarith [iterationsB_rhog_ge_one Cm.toFlowFM s n q.1.2]) (hS.T_nonneg n)
      hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m
  have hone := iterationsB_prec_chain_absg hsize (U := STPair s t) (c := fun n _ => cv * A n)
    (fun n _ => by have := hS.A_nonneg n; have := hS.one_le_cv; positivity)
    (fun n q ω => hFge _ n q ω) (fun n q ω => hFge _ n q ω) (fun n q ω => hFge _ n q ω)
    (fun n q _ => by linarith [hXge (2 * ((N + 1) / 2)) n q]) (fun n q _ => by linarith [hXge (2 * (N / 2)) n q])
    (fun n q _ => by linarith [hXge (2 * ((N - 1) / 2)) n q])
    (hshort (2 * ((N + 1) / 2)) (by omega) (by omega)) (hshort (2 * (N / 2)) (by omega) (by omega))
    (hshort (2 * ((N - 1) / 2)) (by omega) (by omega))
  -- the right side: `1 + cv A P^{1/2} ≤ XL (2N-1)`
  have hright : ∀ᶠ n in atTop, ∀ (q : STPair s t n) (ω : sz.SeqΩ),
      1 + cv * A n * (((iterationsB_XLg Cm.toFlowFM s A T cB cv N k (2 * ((N + 1) / 2)) n q.1.2 *
          iterationsB_XLg Cm.toFlowFM s A T cB cv N k (2 * (N / 2)) n q.1.2) *
        (iterationsB_XLg Cm.toFlowFM s A T cB cv N k (2 * (N / 2)) n q.1.2 *
          iterationsB_XLg Cm.toFlowFM s A T cB cv N k (2 * ((N - 1) / 2)) n q.1.2)) ^ (1 / 2 : ℝ)) ≤
        iterationsB_XLg Cm.toFlowFM s A T cB cv N k (2 * N - 1) n q.1.2 := by
    filter_upwards [hS.one_le_A, hS.TA] with n hAn hT1n q ω
    have hρ1 := iterationsB_rhog_ge_one Cm.toFlowFM s n q.1.2
    have hXZ : ∀ m, 1 ≤ m → m ≤ N + 1 → iterationsB_XLg Cm.toFlowFM s A T cB cv N k m n q.1.2 ≤
        (1 + cB) + T n * iterationsB_rhog Cm.toFlowFM s n q.1.2 ^ N * A n ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := fun m hm1 hm2 =>
      iterationsB_XLv_le_Z hAn hρ1 (hS.T_nonneg n) hT1n hk hm2
    have hsqrt := iterationsB_sqrt_prod_le (by linarith [hXge (2 * ((N + 1) / 2)) n q])
      (by linarith [hXge (2 * (N / 2)) n q]) (by linarith [hXge (2 * ((N - 1) / 2)) n q])
      (hXZ (2 * ((N + 1) / 2)) (by omega) (by omega)) (hXZ (2 * (N / 2)) (by omega) (by omega))
      (hXZ (2 * ((N - 1) / 2)) (by omega) (by omega))
    have hcvA : 0 ≤ cv * A n := by have := hS.A_nonneg n; have := hS.one_le_cv; positivity
    calc _ ≤ 1 + cv * A n * ((1 + cB) + T n * iterationsB_rhog Cm.toFlowFM s n q.1.2 ^ N * A n ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 := by
          gcongr
      _ = iterationsB_XLg Cm.toFlowFM s A T cB cv N k (2 * N - 1) n q.1.2 := by
          unfold iterationsB_XLg iterationsB_XLv
          rw [ite_eq_right (by omega), ite_eq_left rfl]
  have hone' := iterationsA_prec_mono_rightg hone (Eventually.mono hright fun n hn q ω => hn q ω)
  -- the left side: `Ξ̂_{2N-1} ≤ 1 + cv A P^{1/2}`
  refine iterationsA_prec_mono_leftg ?_ hone'
  filter_upwards [hS.Bctl, hS.one_le_A] with n hn hAn q ω
  have hB0 := hBpos n q
  have hlow : (sz.Bctl n q.1.1)⁻¹ ≤ cv * A n := by
    have := (hn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).1
    have hcvA : 0 < cv * A n := by have := hS.one_le_cv; positivity
    exact inv_le_of_inv_le₀ hcvA this
  refine (iterationsA_xiL_odd_leg hLC hL hHf n (v := q.1.1) ω hB0 hN3).trans ?_
  have hP0 := Real.rpow_nonneg (mul_nonneg (mul_nonneg (hFge (2 * ((N + 1) / 2)) n q ω) (hFge (2 * (N / 2)) n q ω))
    (mul_nonneg (hFge (2 * (N / 2)) n q ω) (hFge (2 * ((N - 1) / 2)) n q ω))) (1 / 2 : ℝ)
  gcongr


/-- **The obligation for `Ξ̂^{(𝓛)}_{4p}`**: the a priori level `ρ^{4p-1}` ((4.39) `sef8w483r324`), `p = N + 4`
(so that `4p > N + 1` and `4p ≠ 2N - 1`). -/
private theorem iterationsB_obl_four_pg {s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScaleg Cf s t A T cB cv K) {N k : ℕ}
    (hapri : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
      (fun n q _ => (Cf.eta n (s n) / Cf.eta n q.1.2) ^ (m - 1))) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 (4 * (N + 4)) ω)
      (fun n q _ => iterationsB_XLg Cf s A T cB cv N k (4 * (N + 4)) n q.1.2) := by
  refine iterationsA_prec_mono_rightg (hapri (4 * (N + 4)) (by omega)) ?_
  filter_upwards [hS.rho] with n hn q ω
  have hρ1 := (hn q).1
  unfold iterationsB_XLg
  rw [iterationsB_XLv_four_p _ _ _ _ _ (by omega) (by omega), iterationsB_rhog_eq hρ1]
  have : 0 ≤ (Cf.eta n (s n) / Cf.eta n q.1.2) ^ (4 * (N + 4) - 1) := by positivity
  linarith

/-- **The obligations for `Ξ̂^{(𝓛-𝒦)}_m`, `m + 1 ≤ N`**: `m = 1` is the averaged law, `m ≥ 2` is `(eq:iteration_induc)` at `(m,k)`. -/
private theorem iterationsB_obl_Kg {s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScaleg Cf s t A T cB cv K) {N k : ℕ}
    (havg : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 1 ω) (fun _ _ _ => 1))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHypgL Cf μ s t A r k)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m + 1 ≤ N) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω)
      (fun n q _ => iterationsB_XLKg Cf s A k m n q.1.2) := by
  by_cases hm : m = 1
  · subst hm
    refine iterationsA_prec_mono_rightg havg ?_
    exact Eventually.of_forall fun n q ω => by simp [iterationsB_XLKg, iterationsB_XLKv]
  · have h : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω)
        (fun n q _ => STPsi (A n) (Cf.eta n (s n) / Cf.eta n q.1.2) m k) := IH1 m (by omega) hm2
    refine iterationsA_prec_mono_rightg h ?_
    filter_upwards [hS.rho] with n hn q ω
    have hρ1 := (hn q).1
    have hP := iterationsA_STPsi_nonneg (hS.A_nonneg n) (by linarith : 0 ≤ Cf.eta n (s n) / Cf.eta n q.1.2) m k
    unfold iterationsB_XLKg iterationsB_XLKv
    rw [iterationsB_rhog_eq hρ1, ite_eq_right hm]
    linarith

/-! ## 2. The step of `lem:iterations` over `STXiBootgL'` -/

/-- **`iterationsB_stepg`** (band `iterationsB_step`): the step with the
bootstrap bound `hboot : STXiBootgL'` (the first summand of `STbootRHS` at `B_s = sz.Bctl n (s n)`) and the lower bound `(cv A)⁻¹ ≤ B` of
the field `Bctl` of `IterationsAScaleg` taken at `w = s ∈ [s,t]`.  The loop class of the odd chain obligation is `Step34Gen_LCompat`,
`StepDecompGen_LoopForm` and a Hermitian flow matrix. -/
theorem iterationsB_stepg {Cm : Step2Mat sz}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {E : ℕ → ℝ}
    (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E)
    (hHf : ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf n u ω).IsHermitian) (hsize : Tendsto sz.size atTop atTop)
    {s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScaleg Cm.toFlowFM s t A T cB cv K)
    (hboot : STXiBootgL' Cm.toFlowFM μ s t)
    (hrela : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg Cm.toFlowFM n q.1.1 m ω))
    (havg : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 1 ω) (fun _ _ _ => 1))
    (hapri : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
      (fun n q _ => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1)))
    {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k)
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHypgL Cm.toFlowFM μ s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHypgL Cm.toFlowFM μ s t A r (k - 1)) :
    STIterHypgL Cm.toFlowFM μ s t A N k := by
  have hshort : ∀ m, 1 ≤ m → m ≤ N + 1 → PrecL sz μ (U := STPair s t)
      (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω) (fun n q _ => iterationsB_XLg Cm.toFlowFM s A T cB cv N k m n q.1.2) :=
    fun m hm1 hm2 => iterationsB_obl_shortg Cm.toFlowFM hsize hS hrela havg IH1 IH2 hm1 hm2
  have hFobl : ∀ m, 1 ≤ m → STlenL N (N + 4) m → PrecL sz μ (U := STPair s t)
      (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω) (fun n q _ => iterationsB_XLg Cm.toFlowFM s A T cB cv N k m n q.1.2) := by
    intro m hm1 hlen
    by_cases hmN : m ≤ N + 1
    · exact hshort m hm1 hmN
    · have h2 : m = 2 * N - 1 ∨ m = 4 * (N + 4) := by unfold STlenL at hlen; omega
      rcases h2 with h | h
      · subst h
        exact iterationsB_obl_chaing hLC hL hHf hsize hS (by omega) hk hshort
      · subst h
        exact iterationsB_obl_four_pg Cm.toFlowFM hS hapri
  have hbootN := hboot N (N + 4) hN (by omega) (fun m n u => iterationsB_XLg Cm.toFlowFM s A T cB cv N k m n u)
    (fun m n u => iterationsB_XLKg Cm.toFlowFM s A k m n u)
    (fun m n u => iterationsB_XLv_ge_one (hS.A_nonneg n) (by linarith [iterationsB_rhog_ge_one Cm.toFlowFM s n u])
      (hS.T_nonneg n) hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m)
    (fun m n u => iterationsB_XLKv_ge_one (hS.A_nonneg n) (by linarith [iterationsB_rhog_ge_one Cm.toFlowFM s n u]) k m)
    hFobl (fun m hm1 hm2 => iterationsB_obl_Kg Cm.toFlowFM hS havg IH1 hm1 hm2)
  obtain ⟨C, hCpos, hC⟩ := iterationsA_boot_bound cB cv K hS.cB_nonneg hS.one_le_cv hS.one_le_K N k hN hk
  have hmain : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 N ω)
      (fun n q _ => C * STPsi (A n) (Cm.eta n (s n) / Cm.eta n q.1.2) N k) := by
    refine iterationsA_prec_mono_rightg hbootN ?_
    filter_upwards [hS.one_le_A, hS.rho, hS.TA, hS.Bctl] with n hAn hρn hTAn hBn q ω
    have hρ1 := (hρn q).1
    have hρeq := iterationsB_rhog_eq hρ1
    have hρ1' := iterationsB_rhog_ge_one Cm.toFlowFM s n q.1.2
    have hρ0 : 0 ≤ iterationsB_rhog Cm.toFlowFM s n q.1.2 := by linarith
    -- the lower bound of the field `Bctl` of `IterationsAScale` at `w = s ∈ [s,t]` (`s ≤ v ≤ u ≤ t` on a pair)
    have hlow := (hBn ⟨s n, le_rfl, q.2.1.trans (q.2.2.1.trans q.2.2.2)⟩).1
    have hb := hC (A n) (iterationsB_rhog Cm.toFlowFM s n q.1.2) (T n) (sz.Bctl n (s n)) (N + 4)
      (fun m => iterationsB_XLg Cm.toFlowFM s A T cB cv N k m n q.1.2) (fun m => iterationsB_XLKg Cm.toFlowFM s A k m n q.1.2)
      (by omega) hAn hρ1' (by rw [hρeq]; exact (hρn q).2.1) (hS.T_nonneg n) hTAn
      (by rw [hρeq]; exact (hρn q).2.2) hlow
      (fun m hm1 hm2 => iterationsB_XLv_le_pred hAn hρ0 (hS.T_nonneg n) hk hm2)
      (fun m hm1 hm2 => iterationsB_XLv_le hAn hρ0 (hS.T_nonneg n) hm2)
      (fun m => iterationsB_XLv_ge_one (hS.A_nonneg n) hρ0 (hS.T_nonneg n) hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m)
      (iterationsB_XLv_le_chain hAn hρ1' (hS.T_nonneg n) hS.cB_nonneg hS.one_le_cv hTAn hN)
      (iterationsB_XLv_four_p _ _ _ _ _ (by omega) (by omega)).le
      (fun m => iterationsB_XLKv_ge_one (hS.A_nonneg n) hρ0 k m)
      (fun m hm1 hm2 => iterationsB_XLKv_le hAn hρ0)
    rw [hρeq] at hb
    exact hb
  refine iterationsA_prec_absorbg hsize ?_ hmain
  filter_upwards [hS.one_le_A, hS.rho] with n hAn hρn q ω
  exact iterationsA_STPsi_nonneg (by linarith) (by linarith [(hρn q).1]) N k

/-! ## 3. The setting facts and the family bundle -/

/-- The `𝒦`-loop bound uniform in the pairs `(v,u)` and the labels (the hypothesis `hK` of `iterationsA_rela_of_Kg`): `stKbound_timeIccgL`
(uniform in `u ∈ [s,t]`, from the hypothesis `STKboundgL` and a probability law) reindexed along `(q, p) ↦ (⟨q.1.1, _⟩, p)` (band
`iterationsB_K_pairs`). -/
private theorem iterationsB_K_pairsg [IsProbabilityMeasure μ] (hN : sz.SizeTendsto) (hK : STKboundgL Cf μ) {s t : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (m : ℕ) (hm : 1 ≤ m) :
    PrecL sz μ (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖Cf.K n p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)) := by
  have h := stKbound_timeIccgL sz Cf μ hN hK s t hs0 hst ht1 m hm
  let φ : ∀ n, STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) →
      TimeIcc s t n × (Fin m → Bool) × (Fin m → Zd d (sz.L n)) :=
    fun n p => (⟨p.1.1.1, p.1.2.1, p.1.2.2.1.trans p.1.2.2.2⟩, p.2)
  exact StochDomAt.precomp_param h φ

/-- **All the hypotheses of `iterationsB_stepg` from the hypotheses of `STIterRgL'`** except the scale facts `hS`, which the two regimes
supply (band `iterationsB_setting`; `STAvgUgL` is part of `STStep2ConclgL`, the a priori bound is `STStep1LoopgL`,
(4.38) `rela_XILXILK` comes from the uniform `𝒦` bound). -/
private theorem iterationsB_settingg {Cm : Step2Mat sz}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {E : ℕ → ℝ}
    [IsProbabilityMeasure μ] (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E)
    (hHf : ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf n u ω).IsHermitian) (hN : sz.SizeTendsto) {s t A T : ℕ → ℝ} {cB cv K Cd : ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hKb : STKboundgL Cm.toFlowFM μ)
    (hStep1 : STStep1LoopgL Cm.toFlowFM μ s t) (hStep2 : STStep2ConclgL Cm.toFlowFM μ s t Cd)
    (hS : IterationsAScaleg Cm.toFlowFM s t A T cB cv K) (hboot : STXiBootgL' Cm.toFlowFM μ s t) {N k : ℕ} (hN2 : 2 ≤ N)
    (hk : 1 ≤ k) (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHypgL Cm.toFlowFM μ s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHypgL Cm.toFlowFM μ s t A r (k - 1)) :
    STIterHypgL Cm.toFlowFM μ s t A N k := by
  have hsize := tendsto_size sz hN
  exact iterationsB_stepg hLC hL hHf hsize hS hboot
    (fun m hm => iterationsA_rela_of_Kg Cm.toFlowFM hsize ht1 m hm
      (iterationsB_K_pairsg Cm.toFlowFM hN hKb hs0 (fun n => (hst n).le) ht1 m hm))
    (iterationsA_avg_of_STAvgUg Cm.toFlowFM hsize ht1 hStep2.2.1)
    (fun m hm => iterationsA_apriori_of_lRB1g hL hsize ht1 hStep1 m hm) hN2 hk IH1 IH2

/-- **The family bundle**: the flow facts (`Admissible`, `T0 < 1`); the law is a probability measure; `StepDecompGen_LoopForm` and `‖m‖ ≤ 1`
along a flow (guarded by `0 < κ` and the flow); the loop class of the odd chain bound (`Step34Gen_LCompat` and a Hermitian flow matrix; unguarded). -/
def IterationsGen2_Fam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  Step2EventsGen_Flow d Flow T0 ∧ (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) ∧
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (Es sz z) ∧ ∀ n : ℕ, ‖(mkM sz z).m n‖ ≤ 1) ∧
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z) ∧
      ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf sz z n u ω).IsHermitian)

/-! ## 4. `stIterationsgL'_of`, `stIterationsIIgL'_of` -/

/-- **`stIterationsgL'_of`** (band `stIterations'_holds`): the statement `STIterationsgL'` (case (i)) at the carrier family `(mkM sz z).toFlowFM`,
`𝔠d = 1/100` (`≤ 1/16` for `iterationsA_scale_Ig`).  The bootstrap bound `STXiBootgL'` stays a hypothesis of the statement. -/
theorem stIterationsgL'_of :
    ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
      (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      IterationsGen2_Fam d law Flow mkM Hf Es T0 →
        STIterationsgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro d law Flow mkM Hf Es T0 ⟨hFl, hProb, hLoop, hLC⟩ hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg hKb hLK hcon hStep1 hStep2 hboot n_ k hn hk IH1 IH2
  haveI := hProb sz
  have hA := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨hL, hm⟩ := hLoop sz κ ε 𝔠 𝔡 z hκ hflow
  exact iterationsB_settingg (hLC sz z).1 hL (hLC sz z).2 hA.2.2.1 hs0 hst ht1 hKb hStep1 hStep2
    (iterationsA_scale_Ig (by omega) hL hm (by norm_num) (by norm_num) hreg hcon hA.2.2.2.2 ht1) hboot hn hk IH1 IH2

/-- **`stIterationsIIgL'_of`** (band `stIterationsII'_holds`): the statement `STIterationsIIgL'` (case (ii)), `𝔠d = 1/100` (`≤ 1/24` for `iterationsA_scale_IIg`);
the regime `STCaseII` is not consumed. -/
theorem stIterationsIIgL'_of :
    ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
      (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      IterationsGen2_Fam d law Flow mkM Hf Es T0 →
        STIterationsIIgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro d law Flow mkM Hf Es T0 ⟨hFl, hProb, hLoop, hLC⟩ hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT _hreg hKb hLK hcon hStep1 hStep2 hboot n_ k hn hk IH1 IH2
  haveI := hProb sz
  have hA := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨hL, hm⟩ := hLoop sz κ ε 𝔠 𝔡 z hκ hflow
  exact iterationsB_settingg (hLC sz z).1 hL (hLC sz z).2 hA.2.2.1 hs0 hst ht1 hKb hStep1 hStep2
    (iterationsA_scale_IIg hL hm (by norm_num) (by norm_num) hcon ht1) hboot hn hk IH1 IH2

end RBM.BA
