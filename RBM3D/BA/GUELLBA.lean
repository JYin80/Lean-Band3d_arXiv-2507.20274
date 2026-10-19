/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEEntryGridBA
import RBM3D.BA.GUEProcBA
import RBM3D.BA.RandomLayerBGBA
import RBM3D.Universality.GUEPhase.LLTransfer

/-!
# The `UNOULLk` transfer of the random layer of [YY_25, §7.2] at block Anderson

Band counterpart: `Universality/GUEPhase/LLTransfer.lean` (`oull_of_pathBounds`, `LLTransfer_main`).  Paper:
the GUE phase of Theorem 2.4 (`Thm: B_Univ`; "essentially identical to [YY_25, Theorem 2.6]"); the equation
numbers (7.26)-(7.29), (7.47) and the lemma number 2.8 below are those of [YY_25, §7.2].

* §1 the flow data of the BA producers at one point `z` with `0 < Im z`: `GUELLBA_flow_data` (the
  real-axis solution at the flow coupling is `m(z)/√t₀`, `z_{t₀} = √t₀ z`; `BAzztE_data`,
  `BASelf_unique`), `GUELLBA_EdReal` (the margin datum `BAEd κ'` is
  `BAReal` at the flow point), `GUELLBA_flowEta` (`η_{t₀} = √t₀ Im z`).
  Used by `BA/GUEHyp`.
* §2 the real-analysis steps of the band proof with the constants of `ba_flowG` (`t₀ ≥ cT`, so
  `√t₀ ≥ √cT =: c₁` replaces `1/4 ≤ √t₀`: `GUELLBA_scale_bound`, `GUELLBA_envelope`,
  `GUELLBA_bad_term`), the pointwise scaling `G(H, z) = r G(r H, r z)`, and the one-time law at
  the last grid step: `√t₀ 𝐇_t` is `mixMatBA (√t₀ λ) t₁ (t₀ - t₁)` with `t₁ = e^{-t} t₀`
  (`GUEEntry_ouMatC_ba_eq_mixMatBA`), whose law under the BA carrier `ouP (UNModelC.ba sz)` is
  that of `gueHBA … K` under `Pgue (sz.withLam 0)` (`map_gueHBA_eq_mixMatBA`).
* §3 `oull_of_pathBoundsBA`: the moment bound `E ‖G(𝐇_t, z)_{xx}‖^{2p} ≤ N^δ` for the centred OU
  flow of the block Anderson model at `z = E + i N^{-1+2τ_U}` from `BAPB` (the `localLaw` field at
  the last grid step, cutoff `τ' = τ_U/2`, failure rate `D = 2p + 1`): off the bad event `|G_{xx}|
  ≤ |M_{xx}| + 1 ≤ 2` (`M_{xx} = m`, `‖m‖ ≤ 1`), on it `|G_{xx}| ≤ (Im z_{t₀})⁻¹ ≤ c₁⁻¹ N`.

Departures from the band statement: the energies are in the ρ-bulk `BAbulk κ` instead of `|E| ≤ 2
- κ`; the Lemma 2.8 facts are those of `ba_flowG` (`κ'`, `cT`) instead of `lemma28_quant`; the
conclusion is the body of `UNOULLk (UNKind.ba d)` (`RandomLayerB_LLAt`) with the centred flow
`ouMatC`. Helpers are `private` or carry the prefix GUELLBA_; the
private helpers of `LLTransfer` are used through `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private LLTransfer_size_pos LLTransfer_one_le_size LLTransfer_etaLL_pos LLTransfer_etaLL_le_one
  LLTransfer_inv_size_le_etaLL LLTransfer_size_mul_etaLL LLTransfer_green_smul_mul LLTransfer_Gres_true
  LLTransfer_measurable_green LLTransfer_split_bound from RBM3D.Universality.GUEPhase.LLTransfer

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

/-! ## 1. The flow data of the BA producers at one point -/

/-- The flow data of (8.1) `eq:t0E0_BA` at one point `z` with `0 < Im z`: the real-axis solution at the flow coupling `√t₀ λ` and the
energy `E' = BAfE` is `m(z)/√t₀`, and `z_{t₀} = √t₀ z` (`BAzztE_data`, `BASelf_unique`). -/
theorem GUELLBA_flow_data (d : ℕ) (sz : Sizes d) (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ) =
        BAm d (sz.L n) (sz.lam n) z / (Real.sqrt (BAfT d sz n z) : ℂ) ∧
      ztOf (BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ)) (BAfE d sz n z) (BAfT d sz n z) =
        (Real.sqrt (BAfT d sz n z) : ℂ) * z := by
  obtain ⟨-, -, hself, hzt, -⟩ := BAzztE_data d (sz.L n) (sz.lam n) hz (BAm_self d (sz.L n) (sz.lam n) z hz)
  have hm : BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ) =
      BAm d (sz.L n) (sz.lam n) z / (Real.sqrt (BAfT d sz n z) : ℂ) :=
    BASelf_unique d (sz.L n) _ _ _ _ (by simp) (BAm_spec ⟨_, hself⟩) hself
  exact ⟨hm, by rw [hm]; exact hzt⟩

/-- **The margin datum gives the real-axis datum**: `BAEd κ'` at `z` is `BAReal` at the flow
point `(√t₀ λ, BAfE, BAm …)` (`BASelf_unique`). -/
theorem GUELLBA_EdReal :
    ∀ (d : ℕ) (κ' : ℝ) (sz : Sizes d) (n : ℕ) (z : ℂ), BAEd d κ' sz n z →
      BAReal d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) κ' (BAfE d sz n z)
        (BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ)) := by
  intro d κ' sz n z ⟨m₀, hm₀⟩
  have h := BASelf_unique d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ) _ _ (by simp)
    (BAm_spec ⟨m₀, hm₀.1⟩) hm₀.1
  rw [h]
  exact hm₀

/-- **The scale of the random-layer statements is the flow scale**: `η_{t₀} = √t₀ Im z` at the flow point
(`BAt0_mul`). -/
theorem GUELLBA_flowEta :
    ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im →
      etaOf (BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ)) (BAfT d sz n z) =
        Real.sqrt (BAfT d sz n z) * z.im := by
  intro d sz n z hz
  rw [(GUELLBA_flow_data d sz n hz).1]
  have hm := (BAm_self d (sz.L n) (sz.lam n) z hz).1
  have ht0 : 0 < BAfT d sz n z := BAt0_pos hz hm
  have hmul : BAfT d sz n z * z.im = (1 - BAfT d sz n z) * (BAm d (sz.L n) (sz.lam n) z).im := BAt0_mul hz hm
  have hs : 0 < Real.sqrt (BAfT d sz n z) := Real.sqrt_pos.2 ht0
  have hss : Real.sqrt (BAfT d sz n z) * Real.sqrt (BAfT d sz n z) = BAfT d sz n z := Real.mul_self_sqrt ht0.le
  unfold etaOf
  rw [Complex.div_ofReal_im]
  field_simp
  nlinarith [hmul, hss]

/-! ## 2. Real-analysis steps and the one-time law -/

/-- The scale step: `a² ≤ gs` (from `1 ≤ c₁ a²`, `c₁ a⁴ ≤ gs`) gives `a gs^{-1/2} ≤ 1` (band: `LLTransfer_scale_bound`, `c₁ = 1/4`). -/
private lemma GUELLBA_scale_bound {a gs c1 : ℝ} (ha0 : 0 < a) (ha : 1 ≤ c1 * a ^ 2) (hgs : c1 * a ^ 4 ≤ gs) :
    a * gs⁻¹ ^ ((1 : ℝ) / 2) ≤ 1 := by
  have ha2 : 0 < a ^ 2 := pow_pos ha0 2
  have h1 : a ^ 2 ≤ gs := by nlinarith [mul_le_mul_of_nonneg_right ha ha2.le]
  have hgs0 : 0 < gs := lt_of_lt_of_le ha2 h1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_inv, ← div_eq_mul_inv, div_le_one (Real.sqrt_pos.2 hgs0)]
  exact Real.le_sqrt_of_sq_le h1

open scoped Matrix.Norms.L2Operator in
/-- The deterministic envelope: `|G_{xx}(w)| ≤ (Im w)⁻¹ ≤ c₁⁻¹ N` for Hermitian `H`, `Im w ≥ c₁ η`, `η ≥ N⁻¹`
(band: `LLTransfer_envelope`, `c₁ = 1/4`). -/
private lemma GUELLBA_envelope {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w : ℂ}
    {S η c1 : ℝ} (hS : 1 ≤ S) (hη : S⁻¹ ≤ η) (hη0 : 0 < η) (hc1 : 0 < c1) (hw : c1 * η ≤ w.im) (x : ι) :
    ‖green H w x x‖ ≤ c1⁻¹ * S := by
  have hS0 : 0 < S := by linarith
  have h1 : ‖green H w x x‖ ≤ (c1 * η)⁻¹ := by
    rw [← LLTransfer_Gres_true]
    exact (RBM.Ind.norm_apply_le_l2_opNorm (Gres H w true) x x).trans
      (norm_Gsig_le_inv_eta hH (by positivity : 0 < c1 * η) (hw.trans (le_abs_self _)) true)
  have h2 : η⁻¹ ≤ S := by
    have := inv_anti₀ (inv_pos.2 hS0) hη
    rwa [inv_inv] at this
  calc ‖green H w x x‖ ≤ (c1 * η)⁻¹ := h1
    _ = c1⁻¹ * η⁻¹ := mul_inv c1 η
    _ ≤ c1⁻¹ * S := by gcongr

/-- The bad-event term: `(C N)^{2p} N^{-(2p+1)} ≤ C^{2p}` (band: `LLTransfer_bad_term`, `C = 4`). -/
private lemma GUELLBA_bad_term {S C : ℝ} (hS : 1 ≤ S) (hC : 0 ≤ C) (p : ℕ) :
    (C * S) ^ (2 * p) * S ^ (-((2 * p + 1 : ℕ) : ℝ)) ≤ C ^ (2 * p) := by
  have hS0 : 0 < S := by linarith
  rw [Real.rpow_neg hS0.le, Real.rpow_natCast, ← div_eq_mul_inv, div_le_iff₀ (by positivity), mul_pow, pow_succ]
  have h0 : (0 : ℝ) ≤ C ^ (2 * p) * S ^ (2 * p) := by positivity
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hS)]

/-- The mixture scales: `r (g Ψ + √a X + √b Y) = (r g) Ψ + (r √a) X + (r √b) Y` (generic matrices). -/
private theorem GUELLBA_smul_aux {ι : Type*} (r g a b : ℝ) (Ψ X Y : Matrix ι ι ℂ) :
    ((r : ℝ) : ℂ) • (((g : ℝ) : ℂ) • Ψ + (Real.sqrt a • X + Real.sqrt b • Y)) =
      (((r * g : ℝ)) : ℂ) • Ψ + ((r * Real.sqrt a) • X + (r * Real.sqrt b) • Y) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The BA mixture scales as a mixture: `r (g Ψ + √a X + √b Y) = (r g) Ψ + √(r² a) X + √(r² b) Y`, `r ≥ 0`. -/
private theorem GUELLBA_smul_mixMatBA {d : ℕ} (sz : Sizes d) (n : ℕ) {r a b g : ℝ} (hr : 0 ≤ r)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ((r : ℝ) : ℂ) • mixMatBA sz n g a b ω = mixMatBA sz n (r * g) (r ^ 2 * a) (r ^ 2 * b) ω := by
  unfold mixMatBA mixMat
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
  exact GUELLBA_smul_aux r g a b _ _ _

/-- The BA grid path is a measurable matrix-valued map. -/
private theorem GUELLBA_measurable_gueHBA {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (gueHBA sz g t1 t0 K n k) :=
  ((continuous_const.add continuous_id).measurable : Measurable
    (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => ((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M)).comp
    (gueH_measurable (sz.withLam 0) t1 t0 K n k)

/-- `|G| ≤ |G - m| + |m| ≤ 2` on the good event (`|m| ≤ 1`, `|G - m| ≤ 1`). -/
private lemma GUELLBA_norm_le_two {G m : ℂ} (hm : ‖m‖ ≤ 1) (h : ‖G - m‖ ≤ 1) : ‖G‖ ≤ 2 := by
  calc ‖G‖ = ‖(G - m) + m‖ := by rw [sub_add_cancel]
    _ ≤ ‖G - m‖ + ‖m‖ := norm_add_le _ _
    _ ≤ 2 := by linarith

/-- The pointwise scaling `G(H, z) = r G(r H, r z)` in moment form (`r > 0`; band: `LLTransfer_green_scale`). -/
private lemma GUELLBA_green_scale {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (hr : 0 < r) {z w : ℂ}
    (hw : w = (r : ℂ) * z) (H : Matrix ι ι ℂ) (x : ι) (p : ℕ) :
    ‖green H z x x‖ ^ (2 * p) = r ^ (2 * p) * ‖green ((r : ℂ) • H) w x x‖ ^ (2 * p) := by
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hg : green ((r : ℂ) • H) w x x = (r : ℂ)⁻¹ * green H z x x := by
    rw [hw, LLTransfer_green_smul_mul hc]; rfl
  rw [hg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hr.ne', one_pow, one_mul]

/-- **The one-time law of the BA grid path at the last step, integrated** (band: `LLTransfer_integral_transfer`; `map_gueHBA_eq_mixMatBA`,
`GUEEntry_ouMatC_ba_eq_mixMatBA`): with `t₁ = e^{-τ} t₀` and `g = √t₀ λ`, the integral of a measurable matrix functional of
`√t₀ 𝐇_τ` under the BA carrier is the integral of the same functional of the last grid matrix under `Pgue (sz.withLam 0)`. -/
private theorem GUELLBA_integral_transfer {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] (sz : Sizes d) (g t0 t1 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {τ : ℝ}
    (hK : K n ≠ 0) (ht0 : 0 ≤ t0 n) (hτ : 0 ≤ τ) (ht1 : t1 n = Real.exp (-τ) * t0 n) (hg : g n = Real.sqrt (t0 n) * sz.lam n)
    (f : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → V) (hf : Measurable f) :
    ∫ ω, f (((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMatC (UNModelC.ba sz) n τ ω) ∂(ouP (UNModelC.ba sz).toUNModel n) =
      ∫ ω, f (gueHBA sz g t1 t0 K n (K n) ω) ∂(Pgue (sz.withLam 0)) := by
  have he1 : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 : 0 ≤ Real.exp (-τ) := (Real.exp_pos _).le
  have hs0 : 0 ≤ Real.sqrt (t0 n) := Real.sqrt_nonneg _
  have hss : Real.sqrt (t0 n) ^ 2 = t0 n := Real.sq_sqrt ht0
  have ht10 : t1 n ≤ t0 n := by rw [ht1]; nlinarith
  have ht1n : 0 ≤ t1 n := by rw [ht1]; positivity
  have hlast : gridTime t1 t0 K n (K n) = t0 n := gridTime_last t1 t0 K n hK
  have hfun : (fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMatC (UNModelC.ba sz) n τ ω) =
      mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n (K n) - t1 n) := by
    funext ω
    rw [GUEEntry_ouMatC_ba_eq_mixMatBA, GUELLBA_smul_mixMatBA sz n hs0, hg, hlast]
    congr 1
    · rw [hss, ht1]; ring
    · rw [hss, ht1]; ring
  set sh : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    fun M => ((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M with hsh
  have hshm : Measurable sh := (continuous_const.add continuous_id).measurable
  have hmeas : Measurable (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n (K n) - t1 n)) :=
    hshm.comp (measurable_mixMat (sz.withLam 0) n _ _)
  have h1 : Measurable fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
      ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMatC (UNModelC.ba sz) n τ ω := by rw [hfun]; exact hmeas
  have hmap := map_gueHBA_eq_mixMatBA sz g t1 t0 K n (K n) ht1n ht10
  have hI : ∫ y, f y ∂((ouP (UNModelC.ba sz).toUNModel n).map
      (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n (K n) - t1 n))) =
      ∫ y, f y ∂((Pgue (sz.withLam 0)).map (gueHBA sz g t1 t0 K n (K n))) :=
    congrArg (fun μ => ∫ y, f y ∂μ) hmap.symm
  rw [← integral_map h1.aemeasurable hf.aestronglyMeasurable, hfun, hI]
  exact integral_map (GUELLBA_measurable_gueHBA sz g t1 t0 K n (K n)).aemeasurable hf.aestronglyMeasurable

/-- The diagonal of the BA centre: `M_{xx} = m` for a solution of `(self_m)` at the real energy `E` (`BAMres_fine_apply`, `BAMB_diag_eq`). -/
private theorem GUELLBA_Mres_diag {d L W : ℕ} [NeZero L] [NeZero W] {g E : ℝ} {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (x : Idx d L W) :
    Mres (((g : ℝ) : ℂ) • PsiI d L W) (E : ℂ) m x x = m := by
  have hEm : ((E : ℂ) + m).im ≠ 0 := by simpa using hm.1.ne'
  rw [BAMres_fine_apply d L W g (E : ℂ) m hEm x x]
  simp only [↓reduceIte]
  exact BAMB_diag_eq d L g (E : ℂ) m hm _

/-! ## 3. The moment estimate: the `UNOULLk` transfer at block Anderson -/

/-- **`oull_of_pathBoundsBA`: the moment bound of `UNOULLk (UNKind.ba d)` for the centred OU flow from `BAPB`** (the analogue of
`oull_of_pathBounds`).  For a sequence of energies in the ρ-bulk `BAbulk κ`, times `t_n ≥ 0` and
`z_n = E_n + i η_n`, `η_n = ouEtaLL sz τU n = N^{-1+2τ_U}`, `0 < τ_U < 1/2`: if the BA path bounds `BAPB` hold at the Lemma 2.8 data of
`ba_flowG` (`E' = BAfE z_n`, `t₀ = BAfT z_n`, `t₁ = (1 - ζ(t_n)) t₀`, the grid `gueGridK sz 4`, the flow coupling `g = √t₀ λ`), then for every
`δ > 0` and `p`, eventually in `n` and for every `x`, `E ‖G(𝐇_{t_n}, z_n)_{xx}‖^{2p} ≤ N^δ` under the BA carrier `ouP (UNModelC.ba sz)`,
`𝐇_t = λΨ + e^{-t/2} V + √(1 - e^{-t}) X`.  The Lemma 2.8 facts are those of `ba_flowG` (`Ed κ'`, `cT ≤ t₀ < 1`) and `η_{t₀} = √t₀ η`
(`GUELLBA_flowEta`); the proof is the band one with `‖M_{xx}‖ = ‖m‖ ≤ 1` (`BAm_norm_le_one`) and `1/4 ≤ √t₀` replaced by `√cT ≤ √t₀`:
the one-time law is `map_gueHBA_eq_mixMatBA` at the last grid step, the local law at `k = K`, the cutoff `τ' = τ_U/2`, `D = 2p + 1`. -/
theorem oull_of_pathBoundsBA {d : ℕ} (sz : Sizes d) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (hτU1 : τU < 1 / 2)
    (hsize : Tendsto sz.size atTop atTop) {E t : ℕ → ℝ} (hE : ∀ n, BAbulk d (sz.L n) (sz.lam n) κ (E n)) (ht : ∀ n, 0 ≤ t n)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hP : GUEPathBoundsBA sz
      (fun n => Real.sqrt (BAfT d sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) * sz.lam n)
      (fun n => BAfE d sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
      (fun n => (1 - ouZeta (t n)) * BAfT d sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
      (fun n => BAfT d sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I))
      (fun n => BAm d (sz.L n)
        (Real.sqrt (BAfT d sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) * sz.lam n)
        (BAfE d sz n ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) : ℂ)) (gueGridK sz 4) 4 Kt)
    (δ : ℝ) (hδ : 0 < δ) (p : ℕ) :
    ∀ᶠ n in atTop, ∀ x : Idx d (sz.L n) (sz.W n),
      ∫ ω, ‖Gres (ouMatC (UNModelC.ba sz) n (t n) ω) ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
        ∂(ouP (UNModelC.ba sz).toUNModel n) ≤ Nsz sz n ^ δ := by
  obtain ⟨κ', c, cT, hκ', hc, hcT, hF⟩ := ba_flowG d κ hκ
  set zq : ℕ → ℂ := fun n => (E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I with hzq
  have hzim : ∀ n, (zq n).im = ouEtaLL sz τU n := fun n => by simp [hzq]
  have hzre : ∀ n, (zq n).re = E n := fun n => by simp [hzq]
  have hη0 : ∀ n, 0 < ouEtaLL sz τU n := fun n => LLTransfer_etaLL_pos sz n
  have hη1 : ∀ n, ouEtaLL sz τU n ≤ 1 := fun n => LLTransfer_etaLL_le_one sz hτU1 n
  have hflow : ∀ n, BAEd d κ' sz n (zq n) ∧ cT ≤ BAfT d sz n (zq n) ∧ BAfT d sz n (zq n) < 1 ∧
      1 - BAfT d sz n (zq n) ≤ (zq n).im / c := fun n =>
    hF sz n (zq n) (by rw [hzre]; exact hE n) (by rw [hzim]; exact hη0 n) (by rw [hzim]; exact hη1 n)
  have hc1 : 0 < Real.sqrt cT := Real.sqrt_pos.2 hcT
  -- the Lemma 2.8 data along the sequence, and `BAPB` in these terms
  set ft : ℕ → ℝ := fun n => BAfT d sz n (zq n) with hft
  set fE : ℕ → ℝ := fun n => BAfE d sz n (zq n) with hfE
  set t1 : ℕ → ℝ := fun n => (1 - ouZeta (t n)) * ft n with ht1d
  set gq : ℕ → ℝ := fun n => Real.sqrt (ft n) * sz.lam n with hgq
  set mq : ℕ → ℂ := fun n => BAm d (sz.L n) (gq n) (fE n : ℂ) with hmq
  have hP' : GUEPathBoundsBA sz gq fE t1 ft mq (gueGridK sz 4) 4 Kt := hP
  have hbad := hP'.2 (τU / 2) (by positivity) ((2 * p + 1 : ℕ) : ℝ) (by positivity)
  have hSat : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hsize
  have hCev : ∀ᶠ n in atTop, (2 : ℝ) ^ (2 * p) + ((Real.sqrt cT)⁻¹) ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp hSat).eventually_ge_atTop _
  have h2ev : ∀ᶠ n in atTop, (Real.sqrt cT)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ τU :=
    ((tendsto_rpow_atTop hτU).comp hSat).eventually_ge_atTop _
  filter_upwards [hbad, hCev, h2ev] with n hbadn hCn h2n x
  set S : ℝ := ((sz.size n : ℕ) : ℝ) with hSdef
  have hS0 : 0 < S := LLTransfer_size_pos sz n
  have hS1 : 1 ≤ S := LLTransfer_one_le_size sz n
  have hη0n : 0 < ouEtaLL sz τU n := hη0 n
  obtain ⟨hEd, hcTle, hft1, -⟩ := hflow n
  have hzimn : 0 < (zq n).im := by rw [hzim]; exact hη0n
  have hReal : BAReal d (sz.L n) (gq n) κ' (fE n) (mq n) := GUELLBA_EdReal d κ' sz n (zq n) hEd
  have hη_t0 : etaOf (mq n) (ft n) = Real.sqrt (ft n) * ouEtaLL sz τU n := by
    have := GUELLBA_flowEta d sz n (zq n) hzimn
    rwa [hzim] at this
  have hzt : ztOf (mq n) (fE n) (ft n) = (Real.sqrt (ft n) : ℂ) * zq n := (GUELLBA_flow_data d sz n hzimn).2
  have hft0 : 0 < ft n := lt_of_lt_of_le hcT hcTle
  have hs0 : 0 < Real.sqrt (ft n) := Real.sqrt_pos.2 hft0
  have hs1 : Real.sqrt cT ≤ Real.sqrt (ft n) := Real.sqrt_le_sqrt hcTle
  have hsle : Real.sqrt (ft n) ≤ 1 := Real.sqrt_le_one.mpr hft1.le
  have hm0norm : ‖mq n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hReal.1
  have hKne : gueGridK sz 4 n ≠ 0 := gueGridK_ne_zero sz 4 n
  have hti1 : t1 n = Real.exp (-(t n)) * ft n := by simp [ht1d, ouZeta]
  -- the pointwise scaling and the one-time law
  have hstep1 : ∫ ω, ‖Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (zq n) true x x‖ ^ (2 * p)
        ∂(ouP (UNModelC.ba sz).toUNModel n) =
      Real.sqrt (ft n) ^ (2 * p) *
        ∫ ω, ‖green (gueHBA sz gq t1 ft (gueGridK sz 4) n (gueGridK sz 4 n) ω) (ztOf (mq n) (fE n) (ft n)) x x‖ ^ (2 * p)
          ∂(Pgue (sz.withLam 0)) := by
    have hsc : ∀ ω, ‖Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (zq n) true x x‖ ^ (2 * p) =
        Real.sqrt (ft n) ^ (2 * p) *
          ‖green (((Real.sqrt (ft n) : ℝ) : ℂ) • ouMatC (UNModelC.ba sz) n (t n) ω) (ztOf (mq n) (fE n) (ft n)) x x‖ ^ (2 * p) :=
      fun ω => by rw [LLTransfer_Gres_true]; exact GUELLBA_green_scale hs0 hzt _ x p
    simp_rw [hsc]
    rw [integral_const_mul]
    congr 1
    exact GUELLBA_integral_transfer sz gq ft t1 (gueGridK sz 4) n hKne hft0.le (ht n) hti1 rfl
      (fun M => ‖green M (ztOf (mq n) (fE n) (ft n)) x x‖ ^ (2 * p)) ((LLTransfer_measurable_green _ x x).norm.pow_const _)
  -- the bound on the `Pgue` side
  have hgmeas : Measurable fun ω => ‖green (gueHBA sz gq t1 ft (gueGridK sz 4) n (gueGridK sz 4 n) ω)
      (ztOf (mq n) (fE n) (ft n)) x x‖ ^ (2 * p) :=
    ((LLTransfer_measurable_green _ x x).norm.pow_const _).comp (GUELLBA_measurable_gueHBA sz gq t1 ft (gueGridK sz 4) n _)
  have hwim : Real.sqrt cT * ouEtaLL sz τU n ≤ (ztOf (mq n) (fE n) (ft n)).im := by
    rw [ztOf_im, hη_t0]; exact mul_le_mul_of_nonneg_right hs1 hη0n.le
  have hevery : ∀ ω, ‖green (gueHBA sz gq t1 ft (gueGridK sz 4) n (gueGridK sz 4 n) ω) (ztOf (mq n) (fE n) (ft n)) x x‖ ≤
      (Real.sqrt cT)⁻¹ * S := fun ω =>
    GUELLBA_envelope (gueHBA_isHermitian sz gq t1 ft (gueGridK sz 4) n (gueGridK sz 4 n) ω) hS1
      (LLTransfer_inv_size_le_etaLL sz hτU n) hη0n hc1 hwim x
  have ha0 : 0 < S ^ (τU / 2) := Real.rpow_pos_of_pos hS0 _
  have ha2 : (S ^ (τU / 2)) ^ 2 = S ^ τU := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; congr 1; push_cast; ring
  have ha4 : (S ^ (τU / 2)) ^ 4 = S ^ (2 * τU) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; congr 1; push_cast; ring
  have hone : 1 ≤ Real.sqrt cT * (S ^ (τU / 2)) ^ 2 := by
    rw [ha2]; exact (inv_le_iff_one_le_mul₀' hc1).1 h2n
  have hgs : Real.sqrt cT * (S ^ (τU / 2)) ^ 4 ≤ S * etaOf (mq n) (ft n) := by
    rw [ha4, hη_t0, ← LLTransfer_size_mul_etaLL sz (τU := τU) n]
    nlinarith [mul_le_mul_of_nonneg_right hs1 (mul_pos hS0 hη0n).le]
  have hint : ∫ ω, ‖green (gueHBA sz gq t1 ft (gueGridK sz 4) n (gueGridK sz 4 n) ω) (ztOf (mq n) (fE n) (ft n)) x x‖ ^ (2 * p)
      ∂(Pgue (sz.withLam 0)) ≤ (2 : ℝ) ^ (2 * p) + ((Real.sqrt cT)⁻¹) ^ (2 * p) := by
    have hNp := GUELLBA_bad_term hS1 (inv_nonneg.2 hc1.le) p
    have ha : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * p) := pow_nonneg (by norm_num) _
    have hA : (0 : ℝ) ≤ ((Real.sqrt cT)⁻¹ * S) ^ (2 * p) := pow_nonneg (mul_nonneg (inv_nonneg.2 hc1.le) hS0.le) _
    have hq : (0 : ℝ) ≤ S ^ (-((2 * p + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hS0.le _
    have hg0 : ∀ ω, 0 ≤ ‖green (gueHBA sz gq t1 ft (gueGridK sz 4) n (gueGridK sz 4 n) ω) (ztOf (mq n) (fE n) (ft n)) x x‖ ^ (2 * p) :=
      fun ω => pow_nonneg (norm_nonneg _) _
    refine (LLTransfer_split_bound (Pgue (sz.withLam 0)) hgmeas (a := (2 : ℝ) ^ (2 * p))
      (A := ((Real.sqrt cT)⁻¹ * S) ^ (2 * p)) (q := S ^ (-((2 * p + 1 : ℕ) : ℝ))) ha hA hq hg0
      (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hevery ω) _) ?_ hbadn).trans ?_
    · intro ω hω
      simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hω
      have hu := hω (Fin.last (gueGridK sz 4 n), (x, x))
      simp only [Fin.val_last] at hu
      rw [gridTime_last t1 ft (gueGridK sz 4) n hKne] at hu
      have hdev := hu.trans (GUELLBA_scale_bound ha0 hone hgs)
      rw [GUELLBA_Mres_diag hReal.1 x] at hdev
      exact pow_le_pow_left₀ (norm_nonneg _) (GUELLBA_norm_le_two hm0norm hdev) _
    · linarith
  rw [hstep1]
  have hsp : Real.sqrt (ft n) ^ (2 * p) ≤ 1 := pow_le_one₀ hs0.le hsle
  have hI0 : 0 ≤ ∫ ω, ‖green (gueHBA sz gq t1 ft (gueGridK sz 4) n (gueGridK sz 4 n) ω) (ztOf (mq n) (fE n) (ft n)) x x‖ ^ (2 * p)
      ∂(Pgue (sz.withLam 0)) := integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  calc _ ≤ 1 * ((2 : ℝ) ^ (2 * p) + ((Real.sqrt cT)⁻¹) ^ (2 * p)) := mul_le_mul hsp hint hI0 zero_le_one
    _ = _ := one_mul _
    _ ≤ S ^ δ := hCn


end RBM.BA

end
