/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.ExpIntIGen
import RBM3D.Chain.QopDecayGen
import RBM3D.Induction.ExpIntIQ
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.B45Gen
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.GridDuhamelGen

/-!
# The `𝒬` conjunct of the integrated estimate of regime (i) over the carrier (BA-V row V1s3', ticket T2508 row b, targets 10-12)

Additive restatement of `Induction/ExpIntIQ.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ = law sz`, on the one kernel `Step2Gen_UN C`, the generator `Step2Gen_ThetaN C` and the vocabulary and pins of
`Chain/Step6Gen.lean`, `Chain/ExpIntIGen.lean`.  Paper: arXiv:2507.20274, `6:97, 104-132` (regime (i) with `σ₁ ≠ σ₂`: `(eq:EPL-K)`, `(int_K-L+QE)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)`), `3_5:1204-1252`
(`Def:QtPt`, `rmk:choosechi`), `3_5:1284-1289` (`lem_+Q`), `3_5:1659` (`(sum_res_2)`).  The route is the band's transfer from the explicit mollifier `ϑ*` (`expIntIQ_star`, reused by name with `expIntIQ_star_props`,
`expIntIQ_Qop_sub`, `expIntIQ_diff_sumZero`, which are size-level).

* **Target 10.**  `expIntIQ_src_sumZerog` (band `expIntIQ_src_sumZero`, `:142`; W-z): the `𝒬`-source of `ϑ*` is sum-zero, by `QopAlgebra_ThetaN_sumZerog` and the constant row and column sums `ZeroModeGen_KerSums` of
  `B45Gen_Facts` (row 19').  `expIntIQ_f_leg`, `expIntIQ_D_leg` (band `expIntIQ_f_le`, `expIntIQ_D_le`, `:291`, `:403`; W-a): the polynomial envelopes `‖f_v‖ ≤ N³`, `‖D_v‖ ≤ N⁶` and `(1-v)⁻¹ ≤ N` along the flow, from
  `κ' ≤ Im m` and `N^{-1+δ} ≤ 1 - t` (row 9', `ExpIntIQGen_ctrl`), `CltRepg` (`ExpIniIGen_envelope`) and `STKboundgL` (row 17).  `expIntIQ_src_decayg` (band `expIntIQ_src_decay`, `:492`; W-q): `(deccA0)` of the source,
  where `Θ^{(2)}` propagates the decay through `QopDecayGen_ThetaN2_fastDecayg` (class `Step5KerGen_ThDecay` at the kernel coupling `gK ≤ sz.lam`, row 22).
* **Target 11.**  `expIntIQ_inig` (band `expIntIQ_ini`, `:638`): the initial term `𝒰_{s,u} 𝒬*_s f_s` from the sum-zero branch of `expIntI_kernel_unifg` (kernel pin `STEKSumRes2gL` at the coupling `gK`; ratio `≤ 2A`, constant `4A²`,
  `A = Aof κm`; W-b').  `expIntIQ_star_boundg` (band `expIntIQ_star_bound`, `:1104`): the `ϑ*`-Duhamel identity (row 8 `STExpDuhamelQgL`, through `st6_duhEqQ_of_ping`), the sup bound of the source (private
  `ExpIntIQGen_src_sup`: `lem_+Q`), the kernel, `∫ (1-v)⁻¹ ≤ 2 log L` and the rates `≤ 4 T_u` (constant `32 A²`).  `expIntIQ_backg` (band `expIntIQ_back`, `:1252`) and `expIntIQ_conclg` (band `expIntIQ_concl`, `:1306`).
* **Target 12.**  `stExpIntIgL'_of` (→ `STExpIntIgL'`; `T2508_RowBOf`): the first conjunct is `expIntI_sameg` (row a), the second `expIntIQ_conclg`.  Band: `ExpIntIQGen_stExpIntI'_band` (band `stExpIntI'_holds`, `:1346`) through
  `STExpIntI'_of_gL'` and `ExpIntIQGen_stStep6I_of_LW_band` (band `stStep6I_of_LW`, `:1362`) through `ST_step6I_of_LW_Int_gen_band` (row a; V1L-C1 (ii)), from `ExpIntIQGen_stExpIntIgL'_band`.

Coupling (UBA-C1): `STReg5I` at `sz.lam`; the kernels at `gK`, R1 (`∀ n, 0 ≤ gK n * lam n ∧ gK n ^ 2 ≤ lam n ^ 2 ∧ lam n ^ 2 ≤ Aof κm * gK n ^ 2`) enters only at the window, the decay class and the ratio of `expIntI_kernel_unifg`, and,
through `gK ≤ sz.lam` (`Step5KerGen_cmp_pos`), at `QopDecayGen_ThetaN2_fastDecayg`.  No `def`, `abbrev` or `structure` is added; helpers are `private` and prefixed `ExpIntIQGen_`.  The model-free private lemmas of the band file
(`expIntIQ_star_abs`, `expIntIQ_Psum_*`, `expIntIQ_Pvth_le`, `expIntIQ_Bctl_nonneg`, `expIntIQ_rpow_le_cube`, `expIntIQ_L_le_N`, `expIntIQ_N_le_W`, `expIntIQ_sub_Qop`, `expIntIQ_norm_five`, `expIntIQ_norm_three`) and
`ExpIniIGen_envelope`, `ExpIntIIGen_drift_pi`, `Step5CasesGen_prec_mono`, `Step5KerGen_cmp_pos`, `Step6KitGen_KerFR1_band`, `ExpIniIGen_Kb_band`, `ExpIniIGen_bandData` are used by `open private`.  Ports: none from `../RBM1D`, `../RBM2D`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private expIntIQ_star_abs expIntIQ_Psum_comb expIntIQ_Psum_mul_zero expIntIQ_Psum_pi_le expIntIQ_Pvth_le
  expIntIQ_Bctl_nonneg expIntIQ_rpow_le_cube expIntIQ_L_le_N expIntIQ_N_le_W expIntIQ_sub_Qop expIntIQ_norm_five
  expIntIQ_norm_three from RBM3D.Induction.ExpIntIQ

open private expIniI_Bctl_le from RBM3D.Induction.ExpIniI

open private ExpIniIGen_envelope from RBM3D.Chain.ExpIniIGen

open private ExpIntIIGen_drift_pi from RBM3D.Chain.ExpIntIIGen

open private Step5CasesGen_prec_mono from RBM3D.Chain.Step5CasesGen

open private Step5KerGen_cmp_pos from RBM3D.Chain.Step5KerGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The `ϑ*`-source is sum-zero (target 10, W-z) -/

section SumZero

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **Target 10, `expIntIQ_src_sumZerog`** (band `expIntIQ_src_sumZero`, `ExpIntIQ:142`): the `𝒬`-source `A*_v = 𝒬*_v D_v + [𝒬*_v, Θ^{(2)}] f_v - (𝒫 f_v) ∂_vϑ*_v` (`STExpQsrcg`) of the explicit mollifier
`ϑ*` (`expIntIQ_star`) is sum-zero for every `n` with `0 < lam_n`, `v < 1` and constant row and column sums of the generator (`ZeroModeGen_KerSums`, family row 19'): `QopAlgebra_Psum_Qop` (`𝒫∘𝒬 = 0`),
`QopAlgebra_ThetaN_sumZerog` (W-z), `QopAlgebra_Psum_deriv` with `QopAlgebra_mollifier_differentiableAt` (`𝒫 ∂_vϑ* = 0`). -/
theorem expIntIQ_src_sumZerog (n : ℕ) (hK : ZeroModeGen_KerSums C n) (hl : 0 < sz.lam n) (v : ℝ) (hv1 : v < 1)
    (σ : Fin 2 → Bool) : EKSumZero (STExpQsrcg C μ n v σ (expIntIQ_star sz n)) := by
  intro i₀ hi₀ x
  have : i₀ = 0 := Fin.ext hi₀
  subst this
  change STPsum (d := d) (STExpQsrcg C μ n v σ (expIntIQ_star sz n)) x = 0
  have hsum : ∀ (τ : ℝ) (a₁ : Zd d (sz.L n)),
      ∑ a ∈ Finset.univ.filter (fun a : Fin 2 → Zd d (sz.L n) => a 0 = a₁), expIntIQ_star sz n τ a = 1 :=
    fun τ a₁ => QopAlgebra_mollifier_sum d (sz.L n) 1 (sz.lam n) τ a₁
  have hL := sz.three_le_L n
  have h1 : STPsum (d := d) (STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpDriftg C μ n v σ c)) x = 0 :=
    QopAlgebra_Psum_Qop (expIntIQ_star sz n) (hsum v) _ x
  have h2 : STPsum (d := d) (STQop (d := d) (expIntIQ_star sz n) v
      (Step2Gen_ThetaN C n σ v (fun c => STExpErrg C μ n v σ c))) x = 0 :=
    QopAlgebra_Psum_Qop (expIntIQ_star sz n) (hsum v) _ x
  have h3 : STPsum (d := d) (Step2Gen_ThetaN C n σ v (STQop (d := d) (expIntIQ_star sz n) v
      (fun c => STExpErrg C μ n v σ c))) x = 0 :=
    QopAlgebra_ThetaN_sumZerog C n hK σ v _
      (fun a₁ => QopAlgebra_Psum_Qop (expIntIQ_star sz n) (hsum v) _ a₁) x
  have hdv : STPsum (d := d) (fun b : Fin 2 → Zd d (sz.L n) =>
      deriv (fun τ => expIntIQ_star sz n τ b) v) x = 0 :=
    QopAlgebra_Psum_deriv (m := 1) hsum (ϑ' := fun b => deriv (fun τ => expIntIQ_star sz n τ b) v)
      (fun b => (QopAlgebra_mollifier_differentiableAt d (sz.L n) 1 hL hl hv1 b).hasDerivAt) x
  have h4 := expIntIQ_Psum_mul_zero (STPsum (d := d) (fun c => STExpErrg C μ n v σ c)) _ x hdv
  refine (expIntIQ_Psum_comb _ _ _ _ x).trans ?_
  rw [h1, h2, h3, h4]
  ring

end SumZero


/-! ## 2. Polynomial envelopes along the flow (W-a) -/

section Envelopes

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The control** (copy of `ExpEtermsAGen_ctrl`, `Chain/ExpEtermsAGen.lean:139`, which is not imported; band `expLK_eta_inv_le`, `ExpEtermsA:202`; row 9' supplies `κ' ≤ Im m` and `N^{-1+δ} ≤ 1 - T0`):
eventually in `n`, `N ≥ 20` and for every `u ≤ t_n ≤ T_n`, `0 < 1 - u`, `η_u⁻¹ ≤ N` (`η_u = (1-u) Im m`, `etaOf`) and `(1-u)⁻¹ ≤ N`. -/
private theorem ExpIntIQGen_ctrl {d : ℕ} {sz : Sizes d} (hsz : sz.SizeTendsto) {m : ℕ → ℂ} {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ)
    (hm : ∀ n, κ' ≤ (m n).im) {t T : ℕ → ℝ} (htT : ∀ n, t n ≤ T n)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) :
    ∀ᶠ n in atTop, 20 ≤ ((sz.size n : ℕ) : ℝ) ∧ ∀ u : ℝ, u ≤ t n →
      0 < 1 - u ∧ (etaOf (m n) u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hNδ : ∀ᶠ n in atTop, κ'⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp hsz).eventually (eventually_ge_atTop κ'⁻¹)
  filter_upwards [hrange, hsz.eventually (eventually_ge_atTop 20), hNδ] with n hr hN hNd
  refine ⟨hN, fun u hu => ?_⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hp : 0 < N ^ (-1 + δ) := Real.rpow_pos_of_pos hNpos _
  have h1u : N ^ (-1 + δ) ≤ 1 - u := hr.trans (by linarith [htT n])
  have h0 : 0 < 1 - u := hp.trans_le h1u
  have hinv : (1 - u)⁻¹ ≤ N ^ (1 - δ) := by
    refine (inv_anti₀ hp h1u).trans (le_of_eq ?_)
    rw [show (-1 + δ : ℝ) = -(1 - δ) by ring, Real.rpow_neg hNpos.le, inv_inv]
  have hN1δ : N ^ (1 - δ) ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - δ ≤ (1 : ℝ) by linarith)
    rwa [Real.rpow_one] at this
  refine ⟨h0, ?_, hinv.trans hN1δ⟩
  have hηpos : 0 < κ' * (1 - u) := mul_pos hκ' h0
  have hη : κ' * (1 - u) ≤ etaOf (m n) u := by
    unfold etaOf
    nlinarith [hm n]
  calc (etaOf (m n) u)⁻¹ ≤ (κ' * (1 - u))⁻¹ := inv_anti₀ hηpos hη
    _ = κ'⁻¹ * (1 - u)⁻¹ := mul_inv _ _
    _ ≤ N ^ δ * N ^ (1 - δ) := mul_le_mul hNd hinv (inv_nonneg.2 h0.le) (Real.rpow_nonneg hNpos.le _)
    _ = N := by rw [← Real.rpow_add hNpos]; simp

/-- **The envelope of `f_v`** (band `expIntIQ_f_le`, `ExpIntIQ:291`; W-a): `‖f_{v,σ}‖_∞ ≤ N³` for all `v ∈ [s_n, t_n]` and `σ`, eventually.  `‖𝔼 𝓛‖ ≤ η_v⁻² ≤ N²` (`ExpIniIGen_envelope`, from `CltRepg`),
`η_v⁻¹ ≤ N` and `(1-v)⁻¹ ≤ N` from `κ' ≤ Im m` and `N^{-1+δ} ≤ 1 - t` (family row 9', `ExpIntIQGen_ctrl`), `‖𝒦^{(2)}‖ ≤ N B_v ≤ 2N²` (`stKbound_timeIccgL` at `τ = 1`, family row 17; `B ≤ 2(1-v)⁻¹`). -/
theorem expIntIQ_f_leg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto)
    {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hmn : ∀ n, κ' ≤ (C.m n).im)
    (hKb : STKboundgL C μ) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n) :
    (∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) ∧
    (∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErrg C μ n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3) := by
  have := hμ
  have hctrl := ExpIntIQGen_ctrl hsz hκ' hδ hmn (fun n => le_rfl : ∀ n, t n ≤ t n) hev
  have hK := (st6_prec_det_iffg sz μ hμ hsz (V := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p => ‖C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p => (sz.Bctl n (p.1 : ℝ)) ^ (2 - 1))).1
    (stKbound_timeIccgL sz C μ hsz hKb s t hs0 hst ht1 2 (by norm_num)) 1 one_pos
  refine ⟨hctrl.mono fun n hn v hv => (hn.2 v hv).2.2, ?_⟩
  filter_upwards [hctrl, hK] with n ⟨hN20, hc⟩ hKn
  intro v hv1 hv2 σ
  obtain ⟨h0, hη, hy⟩ := hc v hv2
  have hv0 : 0 ≤ v := (hs0 n).trans hv1
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hB : sz.Bctl n v ≤ 2 * N := by
    have := expIniI_Bctl_le sz n hvl
    linarith
  have hη0 : 0 ≤ (etaOf (C.m n) v)⁻¹ := inv_nonneg.2 (mul_pos h0 (hκ'.trans_le (hmn n))).le
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  have henv := ExpIniIGen_envelope C μ hμ hrep hκ' n (hmn n) hvl σ a
  have hKa : ‖C.K n v σ a‖ ≤ 2 * N ^ 2 := by
    have h := hKn (⟨v, hv1, hv2⟩, σ, a)
    simp only [Nat.reduceSub, pow_one, Real.rpow_one] at h
    refine h.trans ?_
    calc N * sz.Bctl n v ≤ N * (2 * N) := mul_le_mul_of_nonneg_left hB hN0.le
      _ = 2 * N ^ 2 := by ring
  have hη2 : (etaOf (C.m n) v)⁻¹ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hη0 hη 2
  calc ‖STExpErrg C μ n v σ a‖ ≤ (etaOf (C.m n) v)⁻¹ ^ 2 + ‖C.K n v σ a‖ := henv
    _ ≤ N ^ 2 + 2 * N ^ 2 := add_le_add hη2 hKa
    _ ≤ N ^ 3 := by nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.2 (by linarith : (3 : ℝ) ≤ N))]

/-- **The envelope of the drift tensor** (band `expIntIQ_D_le`, `ExpIntIQ:403`; W-a): `‖D_v^σ‖_∞ ≤ N^6` for all `v ∈ [s_n, t_n]` and `σ`, eventually (`STExpDriftHiConclgL` at `τ = 1`, `(1-v)⁻¹ ≤ N`,
`B_v ≤ 2 (1-v)⁻¹ ≤ 2N`, `ExpIntIIGen_drift_pi`). -/
theorem expIntIQ_D_leg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STExpDriftHiConclgL C μ s t)
    (hinv : ∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖fun b => STExpDriftg C μ n v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 6 := by
  filter_upwards [ExpIntIIGen_drift_pi C μ hμ hsz ht1 h one_pos, hinv, hsz.eventually (eventually_ge_atTop (16 : ℝ))]
    with n hn hi hN
  intro v hv1 hv2 σ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  have hx : (1 - v)⁻¹ ≤ N := hi v hv2
  have hx0 : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
  have hB := expIniI_Bctl_le sz n hvl
  have hB0 := expIntIQ_Bctl_nonneg sz n v
  have hM : 1 ≤ 2 * N := by linarith
  have hBM : sz.Bctl n v ≤ 2 * N := by linarith
  have h1 := expIntIQ_rpow_le_cube hB0 hBM hM (by norm_num : (11 / 5 : ℝ) ≤ 3) (by norm_num)
  have h2 := expIntIQ_rpow_le_cube hB0 hBM hM (by norm_num : (5 / 2 : ℝ) ≤ 3) (by norm_num)
  have hD := hn ⟨v, hv1, hv2⟩ σ
  refine hD.trans ?_
  have hN0 : 0 < N := by linarith
  have h3 : (1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)) ≤ N * ((2 * N) ^ 3 + (2 * N) ^ 3) := by
    gcongr
  calc N ^ (1 : ℝ) * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))
      ≤ N ^ (1 : ℝ) * (N * ((2 * N) ^ 3 + (2 * N) ^ 3)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 16 * N ^ 5 := by rw [Real.rpow_one]; ring
    _ ≤ N ^ 6 := by nlinarith [pow_pos hN0 5]

end Envelopes

/-! ## 3. Decay of the `ϑ*`-source (target 10, W-q) -/

section Decay

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- The decomposition of the `ϑ`-source `A_v = 𝒬D + [𝒬, Θ] f - (𝒫 f) ∂ϑ` into five pieces, each of which decays: `D - (D - 𝒬D)`, `Θ((𝒫f)ϑ)`, `(Θf - 𝒬(Θf))`, `(𝒫f) ∂ϑ`
(`QopAlgebra_commutator_ThetaNg`; band `expIntIQ_src_decomp`, `ExpIntIQ:456`). -/
private theorem ExpIntIQGen_src_decomp (n : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) :
    STExpQsrcg C μ n v σ ϑ a =
      (STExpDriftg C μ n v σ a -
        ((fun c => STExpDriftg C μ n v σ c) - STQop (d := d) ϑ v (fun c => STExpDriftg C μ n v σ c)) a) +
      (Step2Gen_ThetaN C n σ v (fun b => STPsum (d := d) (fun c => STExpErrg C μ n v σ c) (b 0) * ϑ v b) a -
        (Step2Gen_ThetaN C n σ v (fun c => STExpErrg C μ n v σ c) -
          STQop (d := d) ϑ v (Step2Gen_ThetaN C n σ v (fun c => STExpErrg C μ n v σ c))) a) -
      STPsum (d := d) (fun c => STExpErrg C μ n v σ c) (a 0) * deriv (fun τ => ϑ τ a) v := by
  have hcomm := QopAlgebra_commutator_ThetaNg C n σ ϑ v (fun c => STExpErrg C μ n v σ c) a
  unfold STExpQsrcg
  simp only [Pi.sub_apply]
  simp only [STQop] at hcomm ⊢
  linear_combination hcomm

/-- **Target 10, `expIntIQ_src_decayg`** (band `expIntIQ_src_decay`, `ExpIntIQ:492`; W-q): `(deccA0)` of the `ϑ*`-source on `[s,t]`, for every `σ`, at the scale `ℓ_v`, for every `ε', D > 0`, eventually.
The five pieces of `A*_v`: `D_v` (`STExpDriftDecayConclgL`, deterministic through `HighProbAt.nonempty`), `D_v - 𝒬*D_v` (`stQop_sub_fastDecay`), `Θ((𝒫f)ϑ*) = Θ(f - 𝒬*f)` (**W-q**:
`QopDecayGen_ThetaN2_fastDecayg`, the class `Step5KerGen_ThDecay` at the kernel coupling `gK ≤ sz.lam`, family row 22, after `stQop_sub_fastDecay`), `Θf - 𝒬*(Θf)` (`stQop_sub_fastDecay`), `(𝒫f) ∂ϑ*`
(`QopDecay_deriv_fastDecay`).  The side conditions `L^d ≤ W^K`, `(1-v)⁻¹ ≤ W^K` (`K = 1/𝔠`), `‖·‖ ≤ W^{6/𝔠}` follow from the envelopes `hf`, `hDe` (W-a), `hinv` and `W ≥ N^𝔠`; the row sums of the
one-index kernel (`hrow`, family row 19': `B45Gen_Facts`) bound `‖Θ^{(2)} f‖`. -/
theorem expIntIQ_src_decayg (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) (hμ : IsProbabilityMeasure μ)
    {K₆ C₆ : ℝ} (hK₆ : 0 < K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hC₆ : 0 < C₆) (gK : ℕ → ℝ) (hTh : Step5KerGen_ThDecay C gK 𝔡⁻¹ C₆)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hgl : ∀ n, 0 < gK n → gK n ≤ sz.lam n)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hinv : ∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hf : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErrg C μ n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3)
    (hDe : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖fun b => STExpDriftg C μ n v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 6)
    (hdd : STExpDriftDecayConclgL C μ s t) (ε' D : ℝ) (hε' : 0 < ε') (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (STExpQsrcg C μ n v σ (expIntIQ_star sz n)) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := id hadm
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := step34Gen_W_tendsto hadm
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  set K : ℝ := 1 / 𝔠 with hK
  set C₀ : ℝ := (6 : ℕ) / 𝔠 with hC₀
  set D₁ : ℝ := D + 1 with hD₁
  set D₂ : ℝ := D₁ + K + 1 with hD₂
  have hD₁0 : 0 < D₁ := by rw [hD₁]; linarith
  have hD₂0 : 0 < D₂ := by
    have : 0 < K := one_div_pos.2 h𝔠
    rw [hD₂]; linarith
  obtain ⟨W₁, hW₁1, hW₁⟩ := stQop_sub_fastDecay d 1 K Cs cs C₀ ε' D₁ hCs0 hcs0 hε'
  obtain ⟨W₂, hW₂1, hW₂⟩ := stQop_sub_fastDecay d 1 K Cs cs C₀ (ε' / 2) D₂ hCs0 hcs0 (half_pos hε')
  obtain ⟨W₃, hW₃1, hW₃⟩ := QopDecayGen_ThetaN2_fastDecayg d hd 𝔡⁻¹ K C₀ (ε' / 2) D₂ C₆ (inv_pos.2 h𝔡) (half_pos hε') hC₆
  obtain ⟨W₄, hW₄1, hW₄⟩ := QopDecay_deriv_fastDecay d 1 K C₀ ε' D₁ hε'
  have hdecD : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, ({ω | ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε' D₁
        (fun a => STExpDriftg C μ n (v : ℝ) σ a)} : Set sz.SeqΩ).Nonempty :=
    fun σ => HighProbAt.nonempty (tendsto_size sz hSz) hμ.measure_univ (hdd σ ε' D₁ hε' hD₁0)
  have hall := Filter.eventually_all.2 hdecD
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n := st6_lam_pos sz hWO
  filter_upwards [hstar, hinv, hf, hDe, hall, hWt.eventually (eventually_ge_atTop (max (max (max W₁ W₂) (max W₃ W₄)) 5)),
    hBw, hlam, hg, hSz.eventually (eventually_ge_atTop (max (max 16 Cs) (2 * K₆)))] with n hs hi hfn hDn hdn hW hBn hlamn hgn hN
  intro v hv1 hv2 σ a ha
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hv0 : 0 ≤ v := (hs0 n).trans hv1
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  have hW5 : 5 ≤ W := ((le_max_right _ _).trans hW)
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hWW₃ : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  have hWW₄ : W₄ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  have hW0 : 0 < W := by linarith
  have hN16 : 16 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNCs : Cs ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNK : 2 * K₆ ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN1W : N ≤ W ^ K := by
    have := expIntIQ_N_le_W sz h𝔠 n hBn 1
    simpa [hK] using this
  have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ K := (expIntIQ_L_le_N sz n).trans hN1W
  have hKv : (1 - v)⁻¹ ≤ W ^ K := (hi v hv2).trans hN1W
  have hN6W : N ^ 6 ≤ W ^ C₀ := by
    have := expIntIQ_N_le_W sz h𝔠 n hBn 6
    simpa [hC₀] using this
  have hfn' := hfn v hv1 hv2 σ
  have hLd : ((sz.L n : ℕ) : ℝ) ^ d ≤ N := expIntIQ_L_le_N sz n
  have hLd0 : 0 ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hLd2 : (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hLd0 hLd 2
  have hf3 : ‖(fun c => STExpErrg C μ n v σ c)‖ ≤ N ^ 3 := hfn'
  have hfW : ‖(fun c => STExpErrg C μ n v σ c)‖ ≤ W ^ C₀ :=
    hf3.trans ((pow_le_pow_right₀ hN1 (by norm_num : 3 ≤ 6)).trans hN6W)
  have hPf : ‖STPsum (d := d) (fun c => STExpErrg C μ n v σ c)‖ ≤ N ^ 6 := by
    refine (expIntIQ_Psum_pi_le _).trans ?_
    calc (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 * ‖(fun c => STExpErrg C μ n v σ c)‖ ≤ N ^ 2 * N ^ 3 :=
          mul_le_mul hLd2 hf3 (norm_nonneg _) (by positivity)
      _ = N ^ 5 := by ring
      _ ≤ N ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
  have hPfW : ‖STPsum (d := d) (fun c => STExpErrg C μ n v σ c)‖ ≤ W ^ C₀ := hPf.trans hN6W
  have hg6 : ‖fun b => STPsum (d := d) (fun c => STExpErrg C μ n v σ c) (b 0) * expIntIQ_star sz n v b‖ ≤ N ^ 6 := by
    refine (expIntIQ_Pvth_le hCs0.le hcs0.le hs hv0 hvl _).trans ?_
    calc (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 * ‖(fun c => STExpErrg C μ n v σ c)‖ * Cs ≤ N ^ 2 * N ^ 3 * N := by gcongr
      _ = N ^ 6 := by ring
  have hgW : ‖fun b => STPsum (d := d) (fun c => STExpErrg C μ n v σ c) (b 0) * expIntIQ_star sz n v b‖ ≤ W ^ C₀ :=
    hg6.trans hN6W
  have hΘf : ‖Step2Gen_ThetaN C n σ v (fun c => STExpErrg C μ n v σ c)‖ ≤ W ^ C₀ := by
    refine ((pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ N ^ 6)).2 fun a => ?_).trans hN6W
    have h1 := B45_norm_ThetaN_leg C n (hrow n) σ hv0 hvl (A := fun c => STExpErrg C μ n v σ c) (M := N ^ 3)
      (fun b => (norm_le_pi_norm _ b).trans hf3) a
    refine h1.trans ?_
    have hx : (1 - v)⁻¹ ≤ N := hi v hv2
    have e : K₆ / (1 - v) = K₆ * (1 - v)⁻¹ := div_eq_mul_inv _ _
    rw [e]
    have h2 : K₆ * (1 - v)⁻¹ ≤ K₆ * N := mul_le_mul_of_nonneg_left hx hK₆.le
    calc ((2 : ℕ) : ℝ) * (K₆ * (1 - v)⁻¹) * N ^ 3 ≤ 2 * (K₆ * N) * N ^ 3 := by
          push_cast; gcongr
      _ = (2 * K₆) * N ^ 4 := by ring
      _ ≤ N * N ^ 4 := by gcongr
      _ = N ^ 5 := by ring
      _ ≤ N ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
  have hDW : ‖fun c => STExpDriftg C μ n v σ c‖ ≤ W ^ C₀ := (hDn v hv1 hv2 σ).trans hN6W
  have hgl' : gK n ≤ sz.lam n := hgl n hgn.1
  -- the five decays at a far index `a`
  have b1 : ‖STExpDriftg C μ n v σ a‖ ≤ W ^ (-D₁) := by
    obtain ⟨ω, hω⟩ := hdn σ
    exact hω ⟨v, hv1, hv2⟩ a ha
  have b2 := hW₁ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn W hWW₁ hLW (expIntIQ_star sz n) hs v hv0 hvl
    (fun c => STExpDriftg C μ n v σ c) hDW a ha
  have hdecg : EKFastDecay (sz.lam n) v W (ε' / 2) D₂
      (fun b => STPsum (d := d) (fun c => STExpErrg C μ n v σ c) (b 0) * expIntIQ_star sz n v b) := by
    rw [← expIntIQ_sub_Qop]
    exact hW₂ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn W hWW₂ hLW (expIntIQ_star sz n) hs v hv0 hvl
      (fun c => STExpErrg C μ n v σ c) hfW
  have b3 := hW₃ sz C gK hTh n hgn.1 hgn.2 hgl' hWW₃ hLW v hv0 hvl hKv σ _ hgW hdecg
  have e2 : 2 * (ε' / 2) = ε' := by ring
  have e3 : D₂ - (K + 1) = D₁ := by rw [hD₂]; ring
  rw [e2, e3] at b3
  have b4 := hW₁ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn W hWW₁ hLW (expIntIQ_star sz n) hs v hv0 hvl
    (Step2Gen_ThetaN C n σ v (fun c => STExpErrg C μ n v σ c)) hΘf a ha
  have b5 : ‖STPsum (d := d) (fun c => STExpErrg C μ n v σ c) (a 0) *
      deriv (fun τ => expIntIQ_star sz n τ a) v‖ ≤ W ^ (-D₁) :=
    hW₄ (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn W hWW₄ v hv0 hvl hKv
      (STPsum (d := d) (fun c => STExpErrg C μ n v σ c)) hPfW a ha
  have b3' : ‖Step2Gen_ThetaN C n σ v (fun b => STPsum (d := d) (fun c => STExpErrg C μ n v σ c) (b 0) *
      expIntIQ_star sz n v b) a‖ ≤ W ^ (-D₁) := b3 a ha
  -- combine
  change ‖STExpQsrcg C μ n v σ (expIntIQ_star sz n) a‖ ≤ W ^ (-D)
  rw [ExpIntIQGen_src_decomp]
  have hWD : W ^ (-D₁) = W ^ (-D) * W⁻¹ := by
    rw [hD₁, show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have hWi : W⁻¹ ≤ 1 / 5 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hW5
  have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  refine (expIntIQ_norm_five).trans ?_
  calc _ ≤ 5 * W ^ (-D₁) := by linarith
    _ = 5 * (W ^ (-D) * W⁻¹) := by rw [hWD]
    _ ≤ 5 * (W ^ (-D) * (1 / 5)) := by gcongr
    _ = W ^ (-D) := by ring

end Decay

/-! ## 4. The sup bound of the `ϑ*`-source and the drift-type integral (target 11) -/

section Sup

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The sup bound of the `ϑ*`-source** (band `expIntIQ_src_sup`, `ExpIntIQ:933`): `‖A*_v‖ ≺ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2} + B_v³)`: `lem_+Q` (`stQopNorm_holds`, `m = 1`, `C_n ε` small) on the drift
tensor `D_v` (`STExpDriftDecayConclgL`, `STExpDriftHiConclgL`), and the second conjunct of `STExpWardIConclgL'` for `ϑ*` for the commutator and `(𝒫f) ∂ϑ*`. -/
private theorem ExpIntIQGen_src_sup (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) (hμ : IsProbabilityMeasure μ)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hdr : STExpDriftHiConclgL C μ s t) (hdd : STExpDriftDecayConclgL C μ s t) (hW : STExpWardIConclgL' C μ s t)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : {σ : Fin 2 → Bool // σ 0 ≠ σ 1},
      ‖STExpQsrcg C μ n v σ.1 (expIntIQ_star sz n)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) +
          sz.Bctl n v ^ 3)) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := id hadm
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := step34Gen_W_tendsto hadm
  have hd0 : 0 < d := by omega
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  set K : ℝ := 1 / 𝔠 with hK
  obtain ⟨Cn, hCn, hpin⟩ := stQopNorm_holds d hd 1 𝔡⁻¹ K Cs cs (inv_pos.2 h𝔡) (one_div_pos.2 h𝔠) hCs0 hcs0
  set τ₁ : ℝ := τ / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  set εQ : ℝ := min (1 / 2) (τ * d / (4 * Cn)) with hεQ
  have hεQ0 : 0 < εQ := lt_min (by norm_num) (by positivity)
  have hεQ1 : εQ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set DQ : ℝ := Cn + 5 / 𝔠 + 1 with hDQ
  have h5c' : 0 < 5 / 𝔠 := by positivity
  have hDQ0 : 0 < DQ := by rw [hDQ]; linarith
  have hDQ1 : 1 < DQ := by rw [hDQ]; linarith
  have hdrift := ExpIntIIGen_drift_pi C μ hμ hSz ht1 hdr hτ₁0
  have hw2 := (st6_prec_det_iffg sz μ hμ hSz
    (V := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q => ‖STQop (d := d) (expIntIQ_star sz n) (q.1 : ℝ) (Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
        (fun c => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c)) q.2.2 -
      Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (q.1 : ℝ) (fun c => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c)) q.2.2‖ +
      ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        deriv (fun τ => expIntIQ_star sz n τ q.2.2) (q.1 : ℝ)‖)
    (fun n q => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)).1
    (hW Cs cs hCs0 hcs0 (expIntIQ_star sz) hstar).2 τ₁ hτ₁0
  have hdecD : ∀ σ : Fin 2 → Bool, ∀ᶠ n in atTop, ({ω | ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) εQ DQ
        (fun a => STExpDriftg C μ n (v : ℝ) σ a)} : Set sz.SeqΩ).Nonempty :=
    fun σ => HighProbAt.nonempty (tendsto_size sz hSz) hμ.measure_univ (hdd σ εQ DQ hεQ0 hDQ0)
  have hall := Filter.eventually_all.2 hdecD
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := step34Gen_band_hg hadm
  filter_upwards [hdrift, hw2, hall, hstar, hlam, hBw,
    ((tendsto_rpow_atTop hεQ0).comp hWt).eventually (eventually_ge_atTop (4 : ℝ)),
    hSz.eventually (eventually_ge_atTop (1 : ℝ)),
    ((tendsto_rpow_atTop (half_pos hτ)).comp hSz).eventually (eventually_ge_atTop (3 : ℝ))]
    with n hdrn hw2n hdn hstn hlamn hBn h4 hN1 hN3
  intro v hv1 hv2 σ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hv0 : 0 ≤ v := (hs0 n).trans hv1
  have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
  have hN0 : 0 < N := by linarith
  have hW0 : 0 ≤ W := Nat.cast_nonneg _
  have h4' : 4 ≤ W ^ εQ := h4
  have hN3' : 3 ≤ N ^ (τ / 2) := hN3
  have hW1 : 1 < W := by
    by_contra hcon
    push Not at hcon
    have := Real.rpow_le_one hW0 hcon hεQ0.le
    linarith
  have hW0' : 0 < W := by linarith
  have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ K := by
    refine (expIntIQ_L_le_N sz n).trans ?_
    have := expIntIQ_N_le_W sz h𝔠 n hBn 1
    simpa [hK] using this
  -- `lem_+Q` on the drift tensor
  have hDdec : EKFastDecay (sz.lam n) v W εQ DQ (fun c => STExpDriftg C μ n v σ.1 c) := by
    obtain ⟨ω, hω⟩ := hdn σ.1
    exact hω ⟨v, hv1, hv2⟩
  have hQ := hpin (sz.L n) (sz.three_le_L n) (sz.lam n) hlamn.1 hlamn.2 W εQ DQ hW1 hεQ0 hεQ1 hDQ1 h4' hLW
    (expIntIQ_star sz n) hstn v hv0 hvl (fun c => STExpDriftg C μ n v σ.1 c) hDdec
  have hD := hdrn ⟨v, hv1, hv2⟩ σ.1
  have hWC : W ^ (Cn * εQ) ≤ N ^ τ₁ := by
    have h1 : W ^ (Cn * εQ) ≤ N ^ (Cn * εQ / d) := sz.W_rpow_le hd0 n (by positivity)
    refine h1.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
    rw [div_le_iff₀ hd0']
    have : Cn * εQ ≤ Cn * (τ * d / (4 * Cn)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hCn.le
    have e : Cn * (τ * d / (4 * Cn)) = τ₁ * d := by rw [hτ₁]; field_simp
    linarith
  have hTail : W ^ (-DQ + Cn) ≤ N ^ (-(5 : ℝ)) := by
    have hexp : -DQ + Cn ≤ -(5 / 𝔠) := by rw [hDQ]; linarith
    have h1 : W ^ (-DQ + Cn) ≤ W ^ (-(5 / 𝔠)) := Real.rpow_le_rpow_of_exponent_le hW1.le hexp
    have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    have h2 : W ^ (-(5 / 𝔠)) ≤ (N ^ 𝔠) ^ (-(5 / 𝔠)) :=
      Real.rpow_le_rpow_of_nonpos hNc hBn (by linarith)
    have h3 : (N ^ 𝔠) ^ (-(5 / 𝔠)) = N ^ (-(5 : ℝ)) := by
      rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
    exact h1.trans (h2.trans h3.le)
  -- the control `X_v`
  set B : ℝ := sz.Bctl n v with hBdef
  have hB0 : 0 ≤ B := expIntIQ_Bctl_nonneg sz n v
  have hBge : N⁻¹ ≤ B := expAvg_Bctl_ge sz n hv0 hvl
  have hx1 : 1 ≤ (1 - v)⁻¹ := by
    refine (one_le_inv₀ (by linarith)).2 (by linarith)
  have hx0 : 0 ≤ (1 - v)⁻¹ := by linarith
  have hr1 : 0 ≤ B ^ (11 / 5 : ℝ) := Real.rpow_nonneg hB0 _
  have hr2 : 0 ≤ B ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0 _
  have hr3 : 0 ≤ B ^ 3 := by positivity
  set Xd : ℝ := (1 - v)⁻¹ * (B ^ (11 / 5 : ℝ) + B ^ (5 / 2 : ℝ)) with hXd
  set Xw : ℝ := (1 - v)⁻¹ * B ^ 3 with hXw
  have hXd0 : 0 ≤ Xd := by positivity
  have hXw0 : 0 ≤ Xw := by positivity
  have hXe : (1 - v)⁻¹ * (B ^ (11 / 5 : ℝ) + B ^ (5 / 2 : ℝ) + B ^ 3) = Xd + Xw := by
    rw [hXd, hXw]; ring
  have hNB3 : N ^ (-(3 : ℝ)) ≤ B ^ 3 := by
    have hN1' : (1 : ℝ) ≤ N := hN1
    rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hBge 3
  have hXlow : N ^ (-(5 : ℝ)) ≤ Xd + Xw := by
    have h1 : N ^ (-(5 : ℝ)) ≤ N ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have h2 : B ^ 3 ≤ Xw := by
      rw [hXw]
      exact le_mul_of_one_le_left hr3 hx1
    linarith
  -- the pointwise bound
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  have hw := hw2n (⟨v, hv1, hv2⟩, σ, a)
  have h0 : ‖STExpQsrcg C μ n v σ.1 (expIntIQ_star sz n) a‖ ≤
      ‖STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpDriftg C μ n v σ.1 c) a‖ +
      (‖STQop (d := d) (expIntIQ_star sz n) v (Step2Gen_ThetaN C n σ.1 v
            (fun c => STExpErrg C μ n v σ.1 c)) a -
          Step2Gen_ThetaN C n σ.1 v
            (STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpErrg C μ n v σ.1 c)) a‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n v σ.1 b) (a 0) *
          deriv (fun τ => expIntIQ_star sz n τ a) v‖) := expIntIQ_norm_three
  have h1 : ‖STQop (d := d) (expIntIQ_star sz n) v (fun c => STExpDriftg C μ n v σ.1 c) a‖ ≤
      N ^ τ₁ * (N ^ τ₁ * Xd) + (Xd + Xw) := by
    refine (norm_le_pi_norm _ a).trans (hQ.trans ?_)
    have h2 : W ^ (Cn * εQ) * ‖(fun c => STExpDriftg C μ n v σ.1 c)‖ ≤ N ^ τ₁ * (N ^ τ₁ * Xd) :=
      mul_le_mul hWC hD (norm_nonneg _) (Real.rpow_nonneg hN0.le _)
    linarith [hTail.trans hXlow |>.trans le_rfl]
  have hP1 : 1 ≤ N ^ τ₁ := Real.one_le_rpow hN1 hτ₁0.le
  have hPP : N ^ τ₁ * N ^ τ₁ = N ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; rw [hτ₁]; ring
  have hQQ : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hP0 : 0 ≤ N ^ τ₁ := by linarith
  have hPP1 : 1 ≤ N ^ τ₁ * N ^ τ₁ := one_le_mul_of_one_le_of_one_le hP1 hP1
  have hPPP : N ^ τ₁ ≤ N ^ τ₁ * N ^ τ₁ := le_mul_of_one_le_right hP0 hP1
  have hPP3 : 3 ≤ N ^ τ₁ * N ^ τ₁ := by rw [hPP]; exact hN3'
  have hfin : N ^ τ₁ * (N ^ τ₁ * Xd) + (Xd + Xw) + N ^ τ₁ * Xw ≤ N ^ τ * (Xd + Xw) := by
    have e1 : 1 * Xd ≤ (N ^ τ₁ * N ^ τ₁) * Xd := mul_le_mul_of_nonneg_right hPP1 hXd0
    have e2 : 1 * Xw ≤ (N ^ τ₁ * N ^ τ₁) * Xw := mul_le_mul_of_nonneg_right hPP1 hXw0
    have e3 : N ^ τ₁ * Xw ≤ (N ^ τ₁ * N ^ τ₁) * Xw := mul_le_mul_of_nonneg_right hPPP hXw0
    have e0 : 0 ≤ (N ^ τ₁ * N ^ τ₁) * (Xd + Xw) := by positivity
    have e4 : (N ^ τ₁ * N ^ τ₁) * 3 ≤ (N ^ τ₁ * N ^ τ₁) * (N ^ τ₁ * N ^ τ₁) :=
      mul_le_mul_of_nonneg_left hPP3 (by positivity)
    have e5 : (N ^ τ₁ * N ^ τ₁) * (N ^ τ₁ * N ^ τ₁) = N ^ τ := by rw [hPP, hQQ]
    have e6 : (N ^ τ₁ * N ^ τ₁) * 3 * (Xd + Xw) ≤ N ^ τ * (Xd + Xw) := by
      rw [← e5]
      exact mul_le_mul_of_nonneg_right e4 (by positivity)
    linarith
  calc ‖STExpQsrcg C μ n v σ.1 (expIntIQ_star sz n) a‖
      ≤ _ := h0
    _ ≤ (N ^ τ₁ * (N ^ τ₁ * Xd) + (Xd + Xw)) + N ^ τ₁ * Xw := add_le_add h1 hw
    _ ≤ N ^ τ * (Xd + Xw) := hfin
    _ = N ^ τ * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3)) := by
        rw [← hXe]

/-- **The drift-type integral at one size** (band `expIntIQ_integral_le`, `ExpIntIQ:856`; `6:97`, `6:132`): a kernel bound `‖𝒰_{v,u} 𝒜_v‖_∞ ≤ M (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2} + B_v³)` on `[s,u]` gives
`‖∫_s^u 𝒰_{v,u} 𝒜_v dv‖ ≤ M · 4 T_u · 2 log L` (`B_v ≤ B_u`, `B_u^{11/5} + B_u^{5/2} ≤ 3 T_u`, `B_u³ ≤ T_u`, `∫_s^u (1-v)⁻¹ ≤ 2 log L`) over the carrier kernel `Step2Gen_UN C`. -/
private theorem ExpIntIQGen_integral_le (n : ℕ) {s u M : ℝ} (hd : 2 ≤ d) (hM : 0 ≤ M)
    (hsu : s ≤ u) (hu : u < 1) (hwin : 1 - s ≤ sz.lam n ^ 2)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u) (σ : Fin 2 → Bool)
    (𝒜 : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hker : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖Step2Gen_UN C n σ v u (𝒜 v)‖ ≤
        M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3)))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ v in s..u, Step2Gen_UN C n σ v u (𝒜 v) a‖ ≤
      M * (4 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by
  have hx : 0 < 1 - u := by linarith
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hLr : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL1
  have hl : sz.lam n ≠ 0 := by
    intro h0
    rw [h0] at hwin
    norm_num at hwin
    linarith
  have hlo' : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u := by
    refine le_trans ?_ hlo
    have h2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hLr hd
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h2
  have hT0 : 0 ≤ STExpTarget sz n u := st6_target_nonneg sz n hu
  have hrate := expIntII_rates_le_target sz n hu hl hlo'
  have hcube := st6_cube_le_target sz n hu
  have hlogL : 0 ≤ 2 * Real.log ((sz.L n : ℕ) : ℝ) := mul_nonneg (by norm_num) (Real.log_nonneg hLr)
  have hbound : ∀ v : ℝ, s ≤ v → v ≤ u →
      M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3)) ≤
        (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹ := by
    intro v hv1 hv2
    have hvu : v < 1 := lt_of_le_of_lt hv2 hu
    have hmono := STBctl_mono sz n hv2 hu
    have hBv := (STBctl_pos sz n hvu).le
    have h1 : sz.Bctl n v ^ (11 / 5 : ℝ) ≤ sz.Bctl n u ^ (11 / 5 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have h2 : sz.Bctl n v ^ (5 / 2 : ℝ) ≤ sz.Bctl n u ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow hBv hmono (by norm_num)
    have h3 : sz.Bctl n v ^ 3 ≤ sz.Bctl n u ^ 3 := pow_le_pow_left₀ hBv hmono 3
    have hinv : 0 ≤ (1 - v)⁻¹ := inv_nonneg.2 (by linarith)
    calc M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3))
        ≤ M * ((1 - v)⁻¹ * (4 * STExpTarget sz n u)) := by
          gcongr
          linarith
      _ = (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹ := by ring
  have hint : IntervalIntegrable (fun v : ℝ => (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹) volume s u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro v hv
    rw [Set.uIcc_of_le hsu] at hv
    have : v ≤ u := hv.2
    change 1 - v ≠ 0
    linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun v => Step2Gen_UN C n σ v u (𝒜 v) a)
    (g := fun v : ℝ => (M * (4 * STExpTarget sz n u)) * (1 - v)⁻¹) hsu
    (Filter.Eventually.of_forall fun v hv =>
      ((norm_le_pi_norm _ a).trans (hker v hv.1.le hv.2)).trans (hbound v hv.1.le hv.2)) hint
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hlog := expIntI_log_ratio (L := sz.L n) (g := sz.lam n) hL1 hsu hu hwin hlo
  calc M * (4 * STExpTarget sz n u) * ∫ v in s..u, (1 - v)⁻¹
      ≤ M * (4 * STExpTarget sz n u) * (2 * Real.log ((sz.L n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = M * (4 * STExpTarget sz n u * (2 * Real.log ((sz.L n : ℕ) : ℝ))) := by ring

end Sup

/-! ## 5. The initial term for `ϑ*` and the `ϑ*` bound (target 11) -/

section Star

variable {d : ℕ} {sz : Sizes d} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **Target 11, `expIntIQ_inig` (the initial term for `ϑ*`)** (band `expIntIQ_ini`, `ExpIntIQ:638`; `(sum_res_2)` `3_5:1659`): from the bound `F` on `𝒰_{s,u} 𝒬^ϑ_s f_s` (any admissible `ϑ`, `0 < Cq`, `0 < c`, eventually)
to the bound `F + B_u³` on `𝒰_{s,u} 𝒬^{ϑ*}_s f_s`.  `𝒬*_s f_s = 𝒬^ϑ_s f_s + R_s` with `R_s = (𝒫 f_s)(ϑ_s - ϑ*_s)` (`expIntIQ_Qop_sub`), which is sum-zero (`expIntIQ_diff_sumZero`), deterministic,
`(s, ε', D)`-decaying (`stQop_sub_fastDecay` twice, `‖f_s‖ ≤ N³ ≤ W^{3/𝔠}`, the envelope `hfenv`) and `‖R_s‖ ≤ 2 N^τ B_s³` (first Ward conjunct of `STExpWardIConclgL'` at `u = s` for `ϑ` and for `ϑ*`).
The sum-zero branch of `expIntI_kernel_unifg` (kernel pin `STEKSumRes2gL` at the coupling `gK`; ratio `≤ 2A`, constant `4 A²`, `A = Aof κm`) then gives `‖𝒰_{s,u} R_s‖ ≤ N^τ · 8 A² B_s³ ≤ N^τ · 8 A² B_u³`. -/
theorem expIntIQ_inig (hSR2 : STEKSumRes2gL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 𝔠d : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm)
    (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ)
    (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t)
    (hfenv : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErrg C (law sz) n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3)
    (hW : STExpWardIConclgL' C (law sz) s t) (Cq c : ℝ) (hC : 0 < Cq) (hc : 0 < c)
    (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n))
    (F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ) (hF : ∀ n p, 0 ≤ F n p)
    (hF1 : PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p)) :
    PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p + sz.Bctl n (p.1 : ℝ) ^ 3) := by
  classical
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := id hadm
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := step34Gen_W_tendsto hadm
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  set K : ℝ := 1 / 𝔠 with hK
  set C₀ : ℝ := (3 : ℕ) / 𝔠 with hC₀
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n := st6_lam_pos sz hWO
  have hA2 : 1 ≤ Aof κm ^ 2 := one_le_pow₀ hAof
  -- the Ward bounds (first conjunct) for `ϑ` and `ϑ*`, in deterministic form
  have hw1 := (st6_prec_det_iffg sz (law sz) hμ hSz
    (V := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q => ‖STPsum (d := d) (fun b => STExpErrg C (law sz) n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
      ϑ n (q.1 : ℝ) q.2.2‖) (fun n q => (sz.Bctl n (q.1 : ℝ)) ^ 3)).1 (hW Cq c hC hc ϑ hϑ).1
  have hw2 := (st6_prec_det_iffg sz (law sz) hμ hSz
    (V := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n q => ‖STPsum (d := d) (fun b => STExpErrg C (law sz) n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
      expIntIQ_star sz n (q.1 : ℝ) q.2.2‖) (fun n q => (sz.Bctl n (q.1 : ℝ)) ^ 3)).1
    (hW Cs cs hCs0 hcs0 (expIntIQ_star sz) hstar).1
  -- the difference tensor `R_s = (𝒫 f_s)(ϑ_s - ϑ*_s)`
  obtain ⟨R, hRdef⟩ : ∃ R : ∀ n : ℕ, (Fin 2 → Bool) → (Fin 2 → Zd d (sz.L n)) → ℂ, ∀ n σ a,
      R n σ a = STPsum (d := d) (fun b => STExpErrg C (law sz) n (s n) σ b) (a 0) *
        (ϑ n (s n) a - expIntIQ_star sz n (s n) a) := ⟨_, fun _ _ _ => rfl⟩
  -- the kernel bound for `R_s`, one sign vector at a time
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigMixed σ}, ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      ∀ (u : TimeIcc s t n) (a : Fin 2 → Zd d (sz.L n)),
        ‖Step2Gen_UN C n σ.1 (s n) (u : ℝ) (R n σ.1) a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (8 * Aof κm ^ 2 * sz.Bctl n (u : ℝ) ^ 3) := by
    intro σ τ hτ
    obtain ⟨𝒜, h𝒜⟩ : ∃ 𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ, ∀ n v, 𝒜 n v =
        if (0 < sz.lam n ∧ STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n) ∧
            STMollifierProps (d := d) (sz.lam n) Cs cs (expIntIQ_star sz n) ∧ v = s n)
        then R n σ.1 else 0 := ⟨_, fun _ _ => rfl⟩
    have hcase : ∀ n v, EKSumZero (𝒜 n v) := by
      intro n v
      rw [h𝒜]
      split_ifs with hg
      · obtain ⟨-, h1, h2, -⟩ := hg
        have : R n σ.1 = fun a : Fin 2 → Zd d (sz.L n) =>
            STPsum (d := d) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) (a 0) *
              (ϑ n (s n) a - expIntIQ_star sz n (s n) a) := funext (hRdef n σ.1)
        rw [this]
        exact expIntIQ_diff_sumZero d (sz.L n) (sz.lam n) Cq c Cs cs (ϑ n) (expIntIQ_star sz n) h1 h2 (s n) _
      · intro i₀ hi₀ x
        simp
    have hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v) := by
      intro ε' D hε' hD
      obtain ⟨W₁, hW₁1, hW₁⟩ := stQop_sub_fastDecay d 1 K Cq c C₀ ε' (D + 1) hC hc hε'
      obtain ⟨W₂, hW₂1, hW₂⟩ := stQop_sub_fastDecay d 1 K Cs cs C₀ ε' (D + 1) hCs0 hcs0 hε'
      filter_upwards [hfenv, hBw, hϑ, hstar, hlam,
        hWt.eventually (eventually_ge_atTop (max (max W₁ W₂) 2))] with n hfn hBn hϑn hsn hln hWn
      intro v hv1 hv2
      rw [h𝒜]
      split_ifs with hg
      · obtain ⟨hl, h1, h2, hvs⟩ := hg
        subst hvs
        set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
        have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWn)
        have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWn)
        have hW2 : 2 ≤ W := (le_max_right _ _).trans hWn
        have hW0 : 0 < W := by linarith
        have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
        have hN1W : ((sz.size n : ℕ) : ℝ) ≤ W ^ K := by
          have := expIntIQ_N_le_W sz h𝔠 n hBn 1
          simpa [hK] using this
        have hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ K := (expIntIQ_L_le_N sz n).trans hN1W
        have hfW : ‖(fun b => STExpErrg C (law sz) n (s n) σ.1 b)‖ ≤ W ^ C₀ := by
          refine (hfn (s n) le_rfl (hst n).le σ.1).trans ?_
          have := expIntIQ_N_le_W sz h𝔠 n hBn 3
          simpa [hC₀] using this
        have e1 := hW₁ (sz.L n) (sz.three_le_L n) (sz.lam n) hl W hWW₁ hLW (ϑ n) h1 (s n) (hs0 n) (hs1 n)
          (fun b => STExpErrg C (law sz) n (s n) σ.1 b) hfW
        have e2 := hW₂ (sz.L n) (sz.three_le_L n) (sz.lam n) hl W hWW₂ hLW (expIntIQ_star sz n) h2 (s n) (hs0 n) (hs1 n)
          (fun b => STExpErrg C (law sz) n (s n) σ.1 b) hfW
        intro a ha
        have hRa : R n σ.1 a = ((fun b => STExpErrg C (law sz) n (s n) σ.1 b) -
              STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a -
            ((fun b => STExpErrg C (law sz) n (s n) σ.1 b) -
              STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a := by
          rw [hRdef, expIntIQ_sub_Qop, expIntIQ_sub_Qop]
          ring
        rw [hRa]
        have hWD : W ^ (-(D + 1)) = W ^ (-D) * W⁻¹ := by
          rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
        have hWi : W⁻¹ ≤ 1 / 2 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hW2
        have hWD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
        have b1 := e1 a ha
        have b2 := e2 a ha
        calc _ ≤ _ := norm_sub_le _ _
          _ ≤ 2 * W ^ (-(D + 1)) := by linarith
          _ = 2 * (W ^ (-D) * W⁻¹) := by rw [hWD]
          _ ≤ 2 * (W ^ (-D) * (1 / 2)) := by gcongr
          _ = W ^ (-D) := by ring
      · intro a _
        have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        simpa using hW0
    have hX0 : ∀ n (v : ℝ), 0 ≤ 2 * sz.Bctl n (s n) ^ 3 := fun n v => by
      have := expIntIQ_Bctl_nonneg sz n (s n)
      positivity
    have hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ 2 * sz.Bctl n (s n) ^ 3 := by
      refine ⟨3, Filter.Eventually.of_forall fun n v _ _ => ?_⟩
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hB := expAvg_Bctl_ge sz n (hs0 n) (hs1 n)
      have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (sz.Bctl n (s n)) ^ 3 := by
        rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB 3
      have h2 : 0 ≤ (sz.Bctl n (s n)) ^ 3 := by
        have := expIntIQ_Bctl_nonneg sz n (s n)
        positivity
      linarith
    have hbd : ∀ τ' : ℝ, 0 < τ' → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (2 * sz.Bctl n (s n) ^ 3) := by
      intro τ' hτ'
      filter_upwards [hw1 τ' hτ', hw2 τ' hτ'] with n h1 h2
      intro v hv1 hv2
      rw [h𝒜]
      split_ifs with hg
      · obtain ⟨-, -, -, hvs⟩ := hg
        subst hvs
        have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hB0 : 0 ≤ sz.Bctl n (s n) ^ 3 := by
          have := expIntIQ_Bctl_nonneg sz n (s n)
          positivity
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
        have q1 := h1 (⟨s n, le_rfl, (hst n).le⟩, ⟨σ.1, σ.2⟩, a)
        have q2 := h2 (⟨s n, le_rfl, (hst n).le⟩, ⟨σ.1, σ.2⟩, a)
        rw [hRdef, mul_sub]
        calc ‖STPsum (d := d) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) (a 0) * ϑ n (s n) a -
              STPsum (d := d) (fun b => STExpErrg C (law sz) n (s n) σ.1 b) (a 0) * expIntIQ_star sz n (s n) a‖
            ≤ _ := norm_sub_le _ _
          _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n (s n) ^ 3 + ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n (s n) ^ 3 :=
            add_le_add q1 q2
          _ = ((sz.size n : ℕ) : ℝ) ^ τ' * (2 * sz.Bctl n (s n) ^ 3) := by ring
      · rw [norm_zero]
        have hB0 : 0 ≤ sz.Bctl n (s n) ^ 3 := by
          have := expIntIQ_Bctl_nonneg sz n (s n)
          positivity
        positivity
    have hk := expIntI_kernel_unifg hd hκm hAof h𝔠d hdc hadm C gK hKer hg hcmp hμ hs0 hst ht1 hR hcon σ.1 𝒜
      (fun n _ => 2 * sz.Bctl n (s n) ^ 3) (Or.inr ⟨hcase, hSR2⟩) hdec hX0 hlow hbd τ hτ
    filter_upwards [hk, hϑ, hstar, hlam] with n hkn hϑn hsn hln u a
    have h0 := hkn u (s n) le_rfl u.2.1
    rw [h𝒜, ite_eq_left ⟨hln, hϑn, hsn, rfl⟩] at h0
    have hsu : s n ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have hmono := STBctl_mono sz n hsu hu1
    have hB0 := expIntIQ_Bctl_nonneg sz n (s n)
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    refine (norm_le_pi_norm _ a).trans (h0.trans ?_)
    have h3 : sz.Bctl n (s n) ^ 3 ≤ sz.Bctl n (u : ℝ) ^ 3 := pow_le_pow_left₀ hB0 hmono 3
    calc ((sz.size n : ℕ) : ℝ) ^ τ * (4 * Aof κm ^ 2 * (2 * sz.Bctl n (s n) ^ 3))
        = ((sz.size n : ℕ) : ℝ) ^ τ * (8 * Aof κm ^ 2 * sz.Bctl n (s n) ^ 3) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (8 * Aof κm ^ 2 * sz.Bctl n (u : ℝ) ^ 3) := by gcongr
  -- the family of `PrecL`
  have hRprec : PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (R n p.2.1.1) p.2.2‖)
      (fun n p _ => 8 * Aof κm ^ 2 * sz.Bctl n (p.1 : ℝ) ^ 3) := by
    refine (st6_prec_det_iffg sz (law sz) hμ hSz (V := STIdx2P sz STSigMixed s t)
      (fun n p => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (R n p.2.1.1) p.2.2‖)
      (fun n p => 8 * Aof κm ^ 2 * sz.Bctl n (p.1 : ℝ) ^ 3)).2 ?_
    intro τ hτ
    filter_upwards [Filter.eventually_all.2 (fun σ => key σ τ hτ)] with n hn p
    exact hn p.2.1 p.1 p.2.2
  have hsum := StochDomAt.add (tendsto_size sz hSz) hF1 hRprec
  refine Step5CasesGen_prec_mono sz (law sz) hSz (c := 8 * Aof κm ^ 2)
    (StochDomAt.of_le_left (fun n p ω => ?_) hsum) (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have e : STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b) =
        STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b) + R n p.2.1.1 := by
      funext a
      rw [Pi.add_apply, expIntIQ_Qop_sub d (sz.L n) (ϑ n) (expIntIQ_star sz n) (s n), hRdef]
    change ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖ ≤
      ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖ +
      ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (R n p.2.1.1) p.2.2‖
    rw [e, Step2Gen_UN_add]
    exact norm_add_le _ _
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hF n p
    change F n p + 8 * Aof κm ^ 2 * sz.Bctl n (p.1 : ℝ) ^ 3 ≤ 8 * Aof κm ^ 2 * (F n p + sz.Bctl n (p.1 : ℝ) ^ 3)
    nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ 8 * Aof κm ^ 2 - 1)]
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hF n p
    change 0 ≤ F n p + sz.Bctl n (p.1 : ℝ) ^ 3
    linarith

end Star

section StarBound

variable {d : ℕ} {sz : Sizes d} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **Target 11, `expIntIQ_star_boundg` (the `ϑ*` bound)** (band `expIntIQ_star_bound`, `ExpIntIQ:1104`): the paper's route `6:109-132` for `ϑ*`.  The `𝒬`-Duhamel identity of `ϑ*` (`hDuQ`, from the family pin
`STExpDuhamelQgL`, row 8, through `st6_duhEqQ_of_ping`), every source sum-zero (`expIntIQ_src_sumZerog`) and decaying (`expIntIQ_src_decayg`), the sup bound `‖A*_v‖ ≺ (1-v)⁻¹ (B_v^{11/5} + B_v^{5/2} + B_v³)`
(`ExpIntIQGen_src_sup`), the sum-zero branch of `expIntI_kernel_unifg` (constant `4 A²`, `A = Aof κm`), `∫_s^u (1-v)⁻¹ ≤ 2 log L` (`expIntI_log_ratio`), the rates `B_v^{11/5} + B_v^{5/2} + B_v³ ≤ 4 T_u`
(`expIntII_rates_le_target`, `st6_cube_le_target`) and `log L ≺ 1` (`expIntII_log_eventually`, constant `32 A²`): `‖𝒰_{s,u} 𝒬*_s f_s‖ ≺ G` gives `‖𝒬*_u f_u‖ ≺ G + T_u`.  The sum-zero and decaying families
are guarded by `0 < lam_n ∧ s_n ≤ v ≤ t_n`. -/
theorem expIntIQ_star_boundg (hSR2 : STEKSumRes2gL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 𝔠d K₆ C₆ : ℝ} (hκm : 0 < κm)
    (hAof : 1 ≤ Aof κm) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz)
    (gK : ℕ → ℝ) (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hgl : ∀ n, 0 < gK n → gK n ≤ sz.lam n) (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t)
    (hK₆ : 0 < K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hKS : ∀ n, ZeroModeGen_KerSums C n) (hC₆ : 0 < C₆) (hTh : Step5KerGen_ThDecay C gK 𝔡⁻¹ C₆)
    (hinv : ∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hfenv : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErrg C (law sz) n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3)
    (hDenv : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖fun b => STExpDriftg C (law sz) n v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 6)
    (hdr : STExpDriftHiConclgL C (law sz) s t) (hdd : STExpDriftDecayConclgL C (law sz) s t)
    (hW : STExpWardIConclgL' C (law sz) s t)
    (hDuQ : ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
      (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C (law sz) s t ϑ)
    (G : ∀ n, STIdx2P sz STSigMixed s t n → ℝ)
    (hG1 : PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => G n p)) :
    PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
        (fun b => STExpErrg C (law sz) n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p + STExpTarget sz n (p.1 : ℝ)) := by
  classical
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := id hadm
  have hs1 : ∀ n, s n < 1 := fun n => lt_trans (hst n) (ht1 n)
  obtain ⟨Cs, cs, hCs0, hcs0, hstar⟩ := expIntIQ_star_abs d sz 𝔡 hWO
  have hduh := hDuQ Cs cs (expIntIQ_star sz) hstar
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n := st6_lam_pos sz hWO
  -- the kernel bound, integrated, one sign vector at a time
  have key : ∀ σ : {σ : Fin 2 → Bool // STSigMixed σ}, ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      ∀ (u : TimeIcc s t n) (a : Fin 2 → Zd d (sz.L n)),
        ‖∫ v in (s n)..(u : ℝ), Step2Gen_UN C n σ.1 v (u : ℝ)
            (STExpQsrcg C (law sz) n v σ.1 (expIntIQ_star sz n)) a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            (32 * Aof κm ^ 2 * (STExpTarget sz n (u : ℝ) * Real.log ((sz.L n : ℕ) : ℝ))) := by
    intro σ τ hτ
    obtain ⟨𝒜, h𝒜⟩ : ∃ 𝒜 : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ, ∀ n v, 𝒜 n v =
        if (0 < sz.lam n ∧ s n ≤ v ∧ v ≤ t n)
        then STExpQsrcg C (law sz) n v σ.1 (expIntIQ_star sz n) else 0 := ⟨_, fun _ _ => rfl⟩
    obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ → ℝ, ∀ n v, X n v = |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) +
        sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3) := ⟨_, fun _ _ => rfl⟩
    have hcase : ∀ n v, EKSumZero (𝒜 n v) := by
      intro n v
      rw [h𝒜]
      split_ifs with hg
      · exact expIntIQ_src_sumZerog C (law sz) n (hKS n) hg.1 v (lt_of_le_of_lt hg.2.2 (ht1 n)) σ.1
      · intro i₀ hi₀ x
        simp
    have hdec : ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (𝒜 n v) := by
      intro ε' D hε' hD
      filter_upwards [expIntIQ_src_decayg C (law sz) hd hadm hμ hK₆ hrow hC₆ gK hTh hg hgl hs0 ht1 hinv hfenv hDenv hdd
        ε' D hε' hD, hlam] with n hn hl
      intro v hv1 hv2
      rw [h𝒜, ite_eq_left ⟨hl, hv1, hv2⟩]
      exact hn v hv1 hv2 σ.1
    have hX0 : ∀ n v, 0 ≤ X n v := by
      intro n v
      rw [hXdef]
      have hB0 := expIntIQ_Bctl_nonneg sz n v
      positivity
    have hlow : ∃ b : ℝ, ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v := by
      refine ⟨3, Filter.Eventually.of_forall fun n v hv1 hv2 => ?_⟩
      have hv0 : 0 ≤ v := (hs0 n).trans hv1
      have hvl : v < 1 := lt_of_le_of_lt hv2 (ht1 n)
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hB := expAvg_Bctl_ge sz n hv0 hvl
      have hB0 := expIntIQ_Bctl_nonneg sz n v
      have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (sz.Bctl n v) ^ 3 := by
        rw [Real.rpow_neg hN0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB 3
      have hx1 : 1 ≤ |1 - v|⁻¹ := by
        rw [abs_of_pos (by linarith : 0 < 1 - v)]
        exact (one_le_inv₀ (by linarith)).2 (by linarith)
      have h5 : 0 ≤ sz.Bctl n v ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0 _
      have h6 : 0 ≤ sz.Bctl n v ^ (11 / 5 : ℝ) := Real.rpow_nonneg hB0 _
      have h7 : 0 ≤ sz.Bctl n v ^ 3 := by positivity
      rw [hXdef]
      calc ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ sz.Bctl n v ^ 3 := h1
        _ ≤ sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3 := by linarith
        _ ≤ |1 - v|⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ) + sz.Bctl n v ^ 3) :=
            le_mul_of_one_le_left (by linarith) hx1
    have hbd : ∀ τ' : ℝ, 0 < τ' → ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n →
        ‖𝒜 n v‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * X n v := by
      intro τ' hτ'
      filter_upwards [ExpIntIQGen_src_sup C (law sz) hd hadm hμ hs0 ht1 hdr hdd hW τ' hτ', hlam] with n hn hl
      intro v hv1 hv2
      rw [h𝒜, ite_eq_left ⟨hl, hv1, hv2⟩, hXdef, abs_of_pos (by linarith [ht1 n] : 0 < 1 - v)]
      exact hn v hv1 hv2 σ
    have hk := expIntI_kernel_unifg hd hκm hAof h𝔠d hdc hadm C gK hKer hg hcmp hμ hs0 hst ht1 hR hcon σ.1 𝒜 X
      (Or.inr ⟨hcase, hSR2⟩) hdec hX0 hlow hbd τ hτ
    filter_upwards [hk, hlam] with n hkn hln
    intro u a
    have hsu : s n ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - (u : ℝ) := by
      have := (hR n).1
      have h2 : (u : ℝ) ≤ t n := u.2.2
      linarith
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hA0 : 0 ≤ Aof κm ^ 2 := sq_nonneg _
    have hint := ExpIntIQGen_integral_le C n (s := s n) (u := (u : ℝ))
      (M := ((sz.size n : ℕ) : ℝ) ^ τ * (4 * Aof κm ^ 2)) (by omega) (by positivity) hsu hu1 (hR n).2 hlo σ.1
      (fun v => STExpQsrcg C (law sz) n v σ.1 (expIntIQ_star sz n)) ?_ a
    · refine hint.trans (le_of_eq ?_)
      ring
    · intro v hv1 hv2
      have h0 := hkn u v hv1 hv2
      have hvl : 0 < 1 - v := by linarith [hu1]
      rw [h𝒜, ite_eq_left ⟨hln, hv1, hv2.trans u.2.2⟩, hXdef, abs_of_pos hvl] at h0
      refine h0.trans (le_of_eq ?_)
      ring
  -- assembly
  refine (st6_prec_det_iffg sz (law sz) hμ hSz (V := STIdx2P sz STSigMixed s t)
    (fun n p => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
      (fun b => STExpErrg C (law sz) n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
    (fun n p => G n p + STExpTarget sz n (p.1 : ℝ))).2 ?_
  intro τ hτ
  have hGdet := ((st6_prec_det_iffg sz (law sz) hμ hSz (V := STIdx2P sz STSigMixed s t)
    (fun n p => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
      (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖)
    (fun n p => G n p)).1 hG1) τ hτ
  have hlog := expIntII_log_eventually sz hSz (by omega : 1 ≤ d) (32 * Aof κm ^ 2) (half_pos hτ)
  filter_upwards [hduh, hGdet, Filter.eventually_all.2 (fun σ => key σ (τ / 2) (half_pos hτ)), hlog]
    with n hd1 hG2 hk hlg
  intro p
  obtain ⟨u, σ, a⟩ := p
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
  have hT0 : 0 ≤ STExpTarget sz n (u : ℝ) := st6_target_nonneg sz n hu1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hxx : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hP0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  change ‖STQop (d := d) (expIntIQ_star sz n) (u : ℝ) (fun b => STExpErrg C (law sz) n (u : ℝ) σ.1 b) a‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (G n (u, σ, a) + STExpTarget sz n (u : ℝ))
  rw [hd1 u σ.1 a]
  refine (norm_add_le _ _).trans ?_
  have h1 := hG2 (u, σ, a)
  have h2 := hk σ u a
  calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (u, σ, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          (32 * Aof κm ^ 2 * (STExpTarget sz n (u : ℝ) * Real.log ((sz.L n : ℕ) : ℝ))) :=
        add_le_add h1 h2
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * G n (u, σ, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) * (32 * Aof κm ^ 2 * Real.log ((sz.L n : ℕ) : ℝ))) := by
        ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (u, σ, a) +
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STExpTarget sz n (u : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) := by
        gcongr
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (G n (u, σ, a) + STExpTarget sz n (u : ℝ)) := by
        rw [← hxx]; ring

end StarBound

/-! ## 6. Back to `ϑ`, the assembly, and the pin (targets 11, 12) -/

section Assembly

variable {d : ℕ} {sz : Sizes d} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **Target 11, `expIntIQ_backg` (back to `ϑ`)** (band `expIntIQ_back`, `ExpIntIQ:1252`): `𝒬^ϑ_u f_u = 𝒬^{ϑ*}_u f_u + (𝒫 f_u)ϑ*_u - (𝒫 f_u)ϑ_u` (`expIntIQ_Qop_sub` at time `u`), the last two terms `≺ B_u³` by
the first Ward conjunct of `STExpWardIConclgL'` (`(eq:EPL-K)` `6:104-107`) for `ϑ*` and for `ϑ`; only `ϑ_u` and `ϑ*_u` occur, never `∂ϑ`. -/
theorem expIntIQ_backg (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ}
    (hW : STExpWardIConclgL' C μ s t) (Cq c : ℝ) (hC : 0 < Cq) (hc : 0 < c)
    (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n))
    (hstar : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) ((1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1)) (1 / 2)
      (expIntIQ_star sz n))
    (G : ∀ n, STIdx2P sz STSigMixed s t n → ℝ) (hG : ∀ n p, 0 ≤ G n p)
    (hG1 : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ)
        (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p)) :
    PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
        (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
      (fun n p _ => G n p + sz.Bctl n (p.1 : ℝ) ^ 3) := by
  have hCs0 : 0 < (1 + 40 * ((d * 1 : ℕ) : ℝ)) * 6 ^ (d * 1) := by positivity
  have hw1 := (hW Cq c hC hc ϑ hϑ).1
  have hw2 := (hW _ (1 / 2) hCs0 (by norm_num) (expIntIQ_star sz) hstar).1
  have hsum := StochDomAt.add (tendsto_size sz hsz) (StochDomAt.add (tendsto_size sz hsz) hG1 hw2) hw1
  refine Step5CasesGen_prec_mono sz μ hsz (c := 2) (StochDomAt.of_le_left (fun n p ω => ?_) hsum)
    (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have e : STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2 =
        STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2 +
          (STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
            expIntIQ_star sz n (p.1 : ℝ) p.2.2 -
          STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2) := by
      rw [expIntIQ_Qop_sub d (sz.L n) (expIntIQ_star sz n) (ϑ n) (p.1 : ℝ)]
      ring
    change ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖ ≤
      ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) *
          expIntIQ_star sz n (p.1 : ℝ) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2‖
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (norm_sub_le _ _)
      _ = _ := by ring
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hG n p
    change G n p + sz.Bctl n (p.1 : ℝ) ^ 3 + sz.Bctl n (p.1 : ℝ) ^ 3 ≤ 2 * (G n p + sz.Bctl n (p.1 : ℝ) ^ 3)
    linarith
  · have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) ^ 3 := by
      have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
      positivity
    have := hG n p
    change 0 ≤ G n p + sz.Bctl n (p.1 : ℝ) ^ 3
    linarith

/-- **Target 11, `expIntIQ_conclg` (assembly)** (band `expIntIQ_concl`, `ExpIntIQ:1306`): the second conjunct `STExpIntQConclgL'` of `STExpIntIgL'` under the premises of `STIngR6gL`, regime (i): `expIntIQ_inig` (`G = F + B³`),
`expIntIQ_star_boundg`, `expIntIQ_backg`, then `F + B³ + T + B³ ≤ 3 (F + T)` (`B_u³ ≤ T_u`, `st6_cube_le_target`) absorbed by `PrecL`.  The `𝒬`-Duhamel premise for the given `ϑ` is not used: the identity is the one of
`ϑ*` (`hDuQ` inside `expIntIQ_star_boundg`). -/
theorem expIntIQ_conclg (hSR2 : STEKSumRes2gL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 𝔠d K₆ C₆ : ℝ} (hκm : 0 < κm)
    (hAof : 1 ≤ Aof κm) (h𝔠d : 0 < 𝔠d) (hdc : (d : ℝ) * 𝔠d < 1) (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz)
    (gK : ℕ → ℝ) (hKer : Ker sz C gK κm) (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hgl : ∀ n, 0 < gK n → gK n ≤ sz.lam n) (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t) (hcon : STConStInd sz 𝔠d s t)
    (hK₆ : 0 < K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hKS : ∀ n, ZeroModeGen_KerSums C n) (hC₆ : 0 < C₆) (hTh : Step5KerGen_ThDecay C gK 𝔡⁻¹ C₆)
    (hinv : ∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hfenv : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖(fun b => STExpErrg C (law sz) n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3)
    (hDenv : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool,
      ‖fun b => STExpDriftg C (law sz) n v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 6)
    (hdr : STExpDriftHiConclgL C (law sz) s t) (hdd : STExpDriftDecayConclgL C (law sz) s t)
    (hW : STExpWardIConclgL' C (law sz) s t)
    (hDuQ : ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
      (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C (law sz) s t ϑ) :
    STExpIntQConclgL' C (law sz) s t := by
  intro Cq c hC hc ϑ hϑ _ F hF hini
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hstar := expIntIQ_star_props d sz 𝔡 hadm.2.2.2.2
  have hB : ∀ n (p : STIdx2P sz STSigMixed s t n), 0 ≤ F n p + sz.Bctl n (p.1 : ℝ) ^ 3 := fun n p => by
    have := expIntIQ_Bctl_nonneg sz n (p.1 : ℝ)
    have := hF n p
    positivity
  have h6 := expIntIQ_inig hSR2 hd hκm hAof h𝔠d hdc hadm C gK hKer hg hcmp hμ hs0 hst ht1 hR hcon hfenv hW Cq c hC hc ϑ hϑ
    F hF hini
  have h7 := expIntIQ_star_boundg hSR2 hd hκm hAof h𝔠d hdc hadm C gK hKer hg hcmp hgl hμ hs0 hst ht1 hR hcon hK₆ hrow hKS
    hC₆ hTh hinv hfenv hDenv hdr hdd hW hDuQ (fun n p => F n p + sz.Bctl n (p.1 : ℝ) ^ 3) h6
  have hT : ∀ n (p : STIdx2P sz STSigMixed s t n),
      0 ≤ F n p + sz.Bctl n (p.1 : ℝ) ^ 3 + STExpTarget sz n (p.1 : ℝ) := fun n p => by
    have := st6_target_nonneg sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    have := hB n p
    linarith
  have h8 := expIntIQ_backg C (law sz) hsz hW Cq c hC hc ϑ hϑ hstar
    (fun n p => F n p + sz.Bctl n (p.1 : ℝ) ^ 3 + STExpTarget sz n (p.1 : ℝ)) hT h7
  refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 3) h8 (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have h2 := st6_cube_le_target sz n hu1
    have h3 := hF n p
    change F n p + sz.Bctl n (p.1 : ℝ) ^ 3 + STExpTarget sz n (p.1 : ℝ) + sz.Bctl n (p.1 : ℝ) ^ 3 ≤
      3 * (F n p + STExpTarget sz n (p.1 : ℝ))
    linarith
  · have := st6_target_nonneg sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    have := hF n p
    change 0 ≤ F n p + STExpTarget sz n (p.1 : ℝ)
    linarith

end Assembly

section Pin

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
  {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
  {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} {Ker : STEKKer d} {Aof : ℝ → ℝ}

/-- **Target 12, the pin `STExpIntIgL'`** (`T2508_RowBOf`; band `stExpIntI'_holds`, `ExpIntIQ:1346`) from the family premises: probability law (row 1), flow facts (row 3), the class `IniTermGen_CltFlow` (row 9': `κ' ≤ Im m`,
`N^{-1+δ} ≤ 1 - T0`, `CltRepg`; BA `baIniTermGen_cltFlow`), `STKboundgL` along the flow (row 17; BA `baKbound_holds`), the kernel pins `STEKSumRes2NALgL`, `STEKSumRes2gL` with the class `Ker` at the coupling `gK`, the
comparison R1 `∃ A` (written `Aof κm`, `κm` before `(sz, z)`; row 16; U3-BA (a)), the class `Step5KerGen_ThDecay` at `gK` with `∃ C₆` after `(𝔡, κ)` (row 22; BA `baStep5KerGen_thDecay`), `B45Gen_Facts` (row 19': the constant
row sums and the `ZeroModeGen_KerSums`; BA `baB45Gen_facts`) and the Duhamel family `STExpDuhamelQgL` (row 8; V1-BA).  The constant is `𝔠_d = 1/(100 d)` (`𝔠_d ≤ 1/100`, `d 𝔠_d = 1/100 < 1`): the first conjunct is
`expIntI_sameg` (`STEKSumRes2NALgL`), the second is `expIntIQ_conclg`.  `STExpDuhEqgL`, `STExpDriftHiConclgL`, `STExpDriftDecayConclgL`, `STExpWardIConclgL'` are the premises of the pin's own slot. -/
theorem stExpIntIgL'_of (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz, IsProbabilityMeasure (law sz))
    (hFF : Step5CasesGen_FlowFacts d Flow mk T0) (hClt : IniTermGen_CltFlow d law Flow mk T0)
    (hKb : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz))
    (hSR : STEKSumRes2NALgL d law Ker) (hSR2 : STEKSumRes2gL d law Ker) (hAof : ∀ κm : ℝ, 0 < κm → 1 ≤ Aof κm)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ (∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) ∧
        ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK sz z n ^ 2)
    (hTh : ∀ 𝔡 : ℝ, 0 < 𝔡 → ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ),
      Flow sz κ ε 𝔠 𝔡 z → Step5KerGen_ThDecay (mk sz z) (gK sz z) 𝔡⁻¹ C₆)
    (hB45 : B45Gen_Facts d Flow mk) (hDuQ : STExpDuhamelQgL d law Flow mk) :
    STExpIntIgL' d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have h𝔠d : 0 < 1 / (100 * (d : ℝ)) := by positivity
  have hdc : (d : ℝ) * (1 / (100 * (d : ℝ))) < 1 := by
    rw [show (d : ℝ) * (1 / (100 * (d : ℝ))) = 1 / 100 by field_simp]; norm_num
  obtain ⟨κ', δ, hκ', -, hδ, HC⟩ := hClt hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨C₆, hC₆, hTh'⟩ := hTh 𝔡 h𝔡 κ hκ
  obtain ⟨K₆, hK₆, G⟩ := hB45 κ hκ
  refine ⟨1 / (100 * (d : ℝ)), h𝔠d, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · intro 𝔠 sz z hflow s t hs0 hst htT hR _ _ _ hcon _ _ _ _ hduh hdr hdd hward
    obtain ⟨_, _, hFl⟩ := hFF κ hκ
    obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
    obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
    obtain ⟨-, hKer', hg', hR1'⟩ := hKF sz ε 𝔠 𝔡 z hflow
    obtain ⟨H₀, g', E, hm', hev', hrep, -⟩ := HC 𝔠 sz z hflow
    obtain ⟨-, -, -, hKS, hrow'⟩ := G sz ε 𝔠 𝔡 z hflow
    have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
    have hev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n :=
      hev'.mono fun n hn => hn.trans (by linarith [htT n])
    have hsz : sz.SizeTendsto := hadm.2.2.1
    obtain ⟨hinv, hfenv⟩ := expIntIQ_f_leg (mk sz z) (law sz) (hμ sz) hsz hrep hκ' hδ hm' (hKb sz κ ε 𝔠 𝔡 z hκ hflow) hs0
      (fun n => (hst n).le) ht1 hev
    have hDenv := expIntIQ_D_leg (mk sz z) (law sz) (hμ sz) hsz ht1 hdr hinv
    have hgl : ∀ n, 0 < gK sz z n → gK sz z n ≤ sz.lam n := fun n hgn => (Step5KerGen_cmp_pos (hR1' n) hgn).2
    exact ⟨expIntI_sameg hSR hd hκm (hAof κm hκm) h𝔠d hdc hadm (mk sz z) (gK sz z) hKer' hg' hR1' (hμ sz) hs0 hst ht1 hR hcon
        hduh hdr hdd,
      expIntIQ_conclg hSR2 hd hκm (hAof κm hκm) h𝔠d hdc hadm (mk sz z) (gK sz z) hKer' hg' hR1' hgl (hμ sz) hs0 hst ht1 hR hcon
        hK₆ (fun n σ σ' t ht0 ht1 a => (hrow' n σ σ' t ht0 ht1).1 a) hKS hC₆ (hTh' sz ε 𝔠 z hflow) hinv hfenv hDenv hdr hdd hward
        (fun Cq c ϑ hϑ => st6_duhEqQ_of_ping hDuQ hκ hflow hs0 ht1 Cq c ϑ hϑ)⟩

end Pin

/-! ## 7. The band re-derivation (V1L-C1 (ii)) -/

/-! ## 8. Compiled nonempty instances at `d = 3` (regime (i) data of the band: `szB`, `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/300`, `(s, t) = (7/8, 15/16)`, `gK = lam`, `Aof = 1`)

`szB`: `L = 4`, `W_n = n + 4`, `lam = 1`.  Discharged at every example: flow, times, regime, `(con_st_ind)` (`conStInd_const`), admissibility, probability law, the class `IniTermGen_CltFlow` (`κ'`, `δ`, `CltRepg`, the range),
`STKboundgL` (`stKbound_holds`), the kernel pins `stek_sumRes2gL_band` with the class `STEKBandKer` and R1 at `Aof = 1`, `step5KerGen_thDecay_band`, `b45Gen_facts_band` (row sums, `ZeroModeGen_KerSums`), the mollifier `ϑ*`
(`expIntIQ_star_props`) and the `𝒬`-Duhamel identity (`stExpDuhamelQ_holds`).  What stays a hypothesis is another gate's pin: `STExpDriftHiConclgL`, `STExpDriftDecayConclgL`, `STExpWardIConclgL'` (T2506 rows a, c) and the
initial-term bound `PrecL …` of `𝒬_s f_s` (`STExpIniIConclgL'`, T2506 row b). -/

end RBM.BA

end
