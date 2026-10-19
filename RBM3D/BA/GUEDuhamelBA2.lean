/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEDuhamelBA

/-!
# The Duhamel tail of the loops on the block Anderson grid: the main theorem

Continuation of `BA/GUEDuhamelBA`: the telescope of the pathwise one-step decomposition,
the pathwise bound on the good event, the four good events holding with high probability, and the
main theorem **`gueGrid_loop_duhamelBA`**, the block Anderson version of `gueGrid_loop_duhamel`
(`DuhamelC.lean`) on the grid path `gueHBA` along `ztOf (m n) (E n)`.  The generic privates of
`DuhamelC.lean` (the elementary eventual inequalities, the exponent
bounds, the label count) are used through `open private … from`.  The private
development (§6-§8) is generic in the model `sz` and the Hermitian shift `A n` of the path; the
public statement (§9) is at `sz.withLam 0`, `A n = g Ψ_I` (`gueHBA`), and takes the a.s. remainder
bound from `Duhamel_drift_remainder_aeBA`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

open private DuhamelC_sqrt_add_le DuhamelC_lam0 DuhamelC_epsY DuhamelC_size_pos DuhamelC_card_le
  DuhamelC_card_le' DuhamelC_lam0_pos DuhamelC_K_cast DuhamelC_loopOf_wf DuhamelC_loopOf_length DuhamelC_num_step
  DuhamelC_num_Q DuhamelC_num_E1 DuhamelC_num_E2 DuhamelC_num_E3 DuhamelC_num_E4 DuhamelC_num_E5 DuhamelC_num_Y
  DuhamelC_num_tau DuhamelC_ev_exp_rpow DuhamelC_ev_exp_lin from RBM3D.Universality.GUEPhase.DuhamelC
open private GUEDuhamelBA_gH GUEDuhamelBA_gPhi GUEDuhamelBA_gVp GUEDuhamelBA_gZinc GUEDuhamelBA_gZst GUEDuhamelBA_gYst
  GUEDuhamelBA_gr GUEDuhamelBA_gH_isHermitian GUEDuhamelBA_step_decomp
  GUEDuhamelBA_bddC2C_Phi GUEDuhamelBA_grid_facts GUEDuhamelBA_azuma_Z GUEDuhamelBA_azuma_Y GUEDuhamelBA_Ash
  GUEDuhamelBA_Ash_isHermitian from RBM3D.BA.GUEDuhamelBA

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path RBM.Loop RBM.Univ
  RBM.Univ.GUEPhase
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 6. The pathwise assembly on the good event (private, generic in the Hermitian shift) -/

/-- The envelope constant of the one-step expansion along `ztOf μ` (`envConst`, with `etaOf μ` for
`etaT E`): the constant of `condExp_loop_drift_gueBA`. -/
private def GUEDuhamelBA_env (d L W : ℕ) (μ : ℂ) (k : ℕ) (v : ℝ) : ℝ :=
  16 * ((k : ℝ) + 3) ^ 4 * (((W * L) ^ d : ℕ) : ℝ) ^ 4 * (1 + (etaOf μ v)⁻¹) ^ (k + 4)

/-- `etaOf μ u` is the imaginary part of the spectral parameter `ztOf μ e u`. -/
private theorem GUEDuhamelBA_etaOf_eq (e : ℝ) (μ : ℂ) (u : ℝ) : etaOf μ u = (ztOf μ e u).im :=
  (ztOf_im μ e u).symm

section Pathwise

variable {d : ℕ} {sz : Sizes d} {A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {μ : ℂ} {I : LoopIdx (Zd d (sz.L n))}

/-- **Telescoping** the pathwise one-step decomposition. -/
private theorem GUEDuhamelBA_telescope (hA : ∀ n, (A n).IsHermitian) (hμ : 0 < μ.im) (hwf : I.WF)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) {ω : PathΩ sz}
    (htr : ∀ j < K n, ω (j + 1) ∈ DuhamelGood sz n) {k : ℕ} (hk : k ≤ K n) :
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n k ω)) (ztOf μ e (gridTime t1 t0 K n k)) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n 0 ω))
            (ztOf μ e (gridTime t1 t0 K n 0)) I
        - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
            genMatGUEOf d (sz.L n) (sz.W n) μ e (gridTime t1 t0 K n j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω) I
      = ∑ j ∈ Finset.range k, GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j ω
        + ∑ j ∈ Finset.range k, GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω
        - ∑ j ∈ Finset.range k, DuhamelB sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
            (Duhamelv sz t1 t0 K n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)
        + ∑ j ∈ Finset.range k, GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω := by
  set L : ℕ → ℂ := fun j =>
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
      (ztOf μ e (gridTime t1 t0 K n j)) I with hL
  have htel : L k - L 0 = ∑ j ∈ Finset.range k, (L (j + 1) - L j) :=
    (Finset.sum_range_sub L k).symm
  have hstep : ∀ j ∈ Finset.range k, L (j + 1) - L j
      - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) μ e (gridTime t1 t0 K n j)
          (GUEDuhamelBA_gH sz A t1 t0 K n j ω) I
      = GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j ω + GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω
        - DuhamelB sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n)
            (GUEDuhamelBA_gH sz A t1 t0 K n j ω)
        + GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω := by
    intro j hj
    have hjK : j < K n := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    exact GUEDuhamelBA_step_decomp hA hμ hwf hst ht0 hjK ω (htr j hjK)
  change L k - L 0 - _ = _
  rw [htel, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hstep]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]


end Pathwise

section Pathwise2

variable {d : ℕ} {sz : Sizes d} {A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {μ : ℂ} {I : LoopIdx (Zd d (sz.L n))}

/-- **The linear part on the good event**:
`L₀` is the number of dyadic levels, `x` the scale `x⁻¹ ≤ η_{t₀}`. -/
private theorem GUEDuhamelBA_Z_bound (hA : ∀ n, (A n).IsHermitian) (hμ : 0 < μ.im) (hμ1 : ‖μ‖ ≤ 1)
    (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n) {lam0 : ℝ} (hlam0 : 0 < lam0)
    {x : ℝ} (hx1 : 1 ≤ x) (heta : x⁻¹ ≤ etaOf μ (t0 n))
    (hxΔ : x * gridStep t1 t0 K n ≤ 1) {L₀ : ℕ}
    (hQ : 32 * (I.length : ℝ) ^ 2 * gridStep t1 t0 K n * (x ^ (2 * I.length + 2)
      + 2 * I.length * x ^ (2 * I.length + 4) * gridStep t1 t0 K n) < 2 ^ L₀ * lam0)
    {c : ℝ} (hc : 0 ≤ c) {ω : PathΩ sz} {k : ℕ} (hk : k ≤ K n)
    (hZ : ∀ ℓ ≤ L₀, ‖∑ j ∈ Finset.range k,
        GUEDuhamelBA_gZst sz A t1 t0 K n e μ I (2 ^ ℓ * lam0) (j + 1) ω‖
      ≤ c * Real.sqrt (k * (2 ^ ℓ * lam0))) :
    ‖∑ j ∈ Finset.range k, GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j ω‖
      ≤ c * Real.sqrt (k * lam0)
        + 8 * I.length * c * Real.sqrt (gridTime t1 t0 K n k - t1 n)
          * (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ)) : ℝ)⁻¹
              * (etaOf μ (gridTime t1 t0 K n j))⁻¹ ^ 2
              * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
                  (ztOf μ e (gridTime t1 t0 K n j)) (2 * I.length)))
        + 8 * I.length * c * Real.sqrt (2 * I.length * x ^ (2 * I.length + 4)
            * gridStep t1 t0 K n) := by
  classical
  obtain ⟨hΔ0, hKΔ, hη, hzd, hmono, htk⟩ :=
    GUEDuhamelBA_grid_facts (e := e) hμ hμ1 ht1 hst ht0 hK heta
  set m : ℕ := I.length with hm
  set S : ℝ := (((sz.size n : ℕ)) : ℝ) with hS
  set Δ := gridStep t1 t0 K n with hΔ
  have hx0 : 0 < x := by linarith
  have hΔx : Δ ≤ x⁻¹ := by
    calc Δ = x⁻¹ * (x * Δ) := by field_simp
      _ ≤ x⁻¹ * 1 := mul_le_mul_of_nonneg_left hxΔ (by positivity)
      _ = x⁻¹ := mul_one _
  set a : ℕ → ℝ := fun j => Real.sqrt (S⁻¹ * (etaOf μ (gridTime t1 t0 K n j))⁻¹ ^ 2
    * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
        (ztOf μ e (gridTime t1 t0 K n j)) (2 * m)) with ha
  set Mk : ℝ := ⨆ j : Fin k, a j with hMk
  have hsum0 : 0 ≤ c * Real.sqrt (k * lam0) := by positivity
  have hlast0 : 0 ≤ 8 * (m : ℝ) * c * Real.sqrt (2 * m * x ^ (2 * m + 4) * Δ) := by positivity
  have hMk0 : 0 ≤ Mk := Real.iSup_nonneg fun j => Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    have : 0 ≤ 8 * (m : ℝ) * c * Real.sqrt (gridTime t1 t0 K n 0 - t1 n) * Mk := by positivity
    linarith
  -- deterministic facts for `j < k`
  have hkK : ∀ j < k, j < K n := fun j hj => lt_of_lt_of_le hj hk
  have hηj : ∀ j < k, x⁻¹ ≤ (ztOf μ e (gridTime t1 t0 K n j)).im ∧
      (ztOf μ e (gridTime t1 t0 K n (j + 1))).im ≥ x⁻¹ ∧
        (ztOf μ e (gridTime t1 t0 K n (j + 1))).im ≤ 1 :=
    fun j hj => ⟨(hη j (le_of_lt (hkK j hj))).1, (hη (j + 1) (hkK j hj)).1,
      (hη (j + 1) (hkK j hj)).2⟩
  have hinvx : ∀ {y : ℝ}, x⁻¹ ≤ y → y⁻¹ ≤ x := fun {y} hy => by
    have hy0 : 0 < y := lt_of_lt_of_le (inv_pos.2 hx0) hy
    rw [inv_le_comm₀ hy0 hx0]; exact hy
  -- `a j ≤ M_k` and `a j ≤ x^{m+1}`
  have haM : ∀ j < k, a j ≤ Mk := fun j hj =>
    le_ciSup (f := fun j : Fin k => a j) (Set.finite_range _).bddAbove ⟨j, hj⟩
  have hsqa : ∀ j < k, a j ^ 2 = S⁻¹ * (etaOf μ (gridTime t1 t0 K n j))⁻¹ ^ 2
      * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
          (ztOf μ e (gridTime t1 t0 K n j)) (2 * m) := by
    intro j hj
    rw [ha]; dsimp only
    rw [Real.sq_sqrt]
    have : 0 ≤ RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
        (ztOf μ e (gridTime t1 t0 K n j)) (2 * m) := RBM.Ind.loopMax_nonneg _
    positivity
  have haX : ∀ j < k, a j ≤ x ^ (m + 1) := by
    intro j hj
    have hpos : 0 < (ztOf μ e (gridTime t1 t0 K n j)).im :=
      lt_of_lt_of_le (inv_pos.2 hx0) (hηj j hj).1
    have hc' := Duhamel_qv_le_crude (sz := sz) (n := n) (GUEDuhamelBA_gH_isHermitian A hA t1 t0 K n j ω) hpos
      (2 * m)
    rw [ztOf_im] at hc'
    have h1 : (etaOf μ (gridTime t1 t0 K n j))⁻¹ ≤ x := by
      rw [GUEDuhamelBA_etaOf_eq e]; exact hinvx (hηj j hj).1
    have h2 : (etaOf μ (gridTime t1 t0 K n j))⁻¹ ^ (2 * m + 2) ≤ x ^ (2 * m + 2) :=
      pow_le_pow_left₀ (by rw [GUEDuhamelBA_etaOf_eq e]; positivity) h1 _
    have h3 : a j ^ 2 ≤ (x ^ (m + 1)) ^ 2 := by
      rw [hsqa j hj, ← pow_mul]
      calc _ ≤ _ := hc'
        _ ≤ x ^ (2 * m + 2) := h2
        _ = x ^ ((m + 1) * 2) := by ring_nf
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 h3
  have hMX : Mk ≤ x ^ (m + 1) := by
    have : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
    exact ciSup_le fun j => haX j j.2
  -- the proxy bound `V_j ≤ Q`
  set esh : ℝ := 2 * m * x ^ (2 * m + 4) * Δ with hesh
  have hesh0 : 0 ≤ esh := mul_nonneg (by positivity) hΔ0
  set Q : ℝ := 32 * (m : ℝ) ^ 2 * Δ * (Mk ^ 2 + esh) with hQdef
  have h32 : 0 ≤ 32 * (m : ℝ) ^ 2 * Δ := mul_nonneg (by positivity) hΔ0
  have hQ0 : 0 ≤ Q := mul_nonneg h32 (by positivity)
  have hVQ : ∀ j < k, GUEDuhamelBA_gVp sz A t1 t0 K n e μ I j ω ≤ Q := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hηj j hj
    have hz'pos : 0 < (ztOf μ e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (inv_pos.2 hx0) h2
    have hz2 : (ztOf μ e (gridTime t1 t0 K n j)).im
        ≤ 2 * (ztOf μ e (gridTime t1 t0 K n (j + 1))).im := by
      have := (hmono j).2
      have hΔle : Δ ≤ (ztOf μ e (gridTime t1 t0 K n (j + 1))).im := le_trans hΔx h2
      linarith
    have hV := Duhamel_Vp_le (GUEDuhamelBA_gH_isHermitian A hA t1 t0 K n j ω) hz'pos (hmono j).1 hz2 h3 hΔ0
      (hzd j) hwf
    have hVeq : GUEDuhamelBA_gVp sz A t1 t0 K n e μ I j ω
        = Δ / S * max (vGue sz n (gradMat (fun M' => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M')
            (ztOf μ e (gridTime t1 t0 K n (j + 1))) I) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) : ℝ)
          (vGue sz n (-Complex.I • gradMat (fun M' => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M')
            (ztOf μ e (gridTime t1 t0 K n (j + 1))) I) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) : ℝ) := rfl
    rw [hVeq]
    refine hV.trans ?_
    have hinv' : ((ztOf μ e (gridTime t1 t0 K n (j + 1))).im)⁻¹ ^ (2 * m + 4)
        ≤ x ^ (2 * m + 4) :=
      pow_le_pow_left₀ (by positivity) (hinvx h2) _
    have ha2 : S⁻¹ * ((ztOf μ e (gridTime t1 t0 K n j)).im)⁻¹ ^ 2
        * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
            (ztOf μ e (gridTime t1 t0 K n j)) (2 * m)
        ≤ Mk ^ 2 := by
      rw [ztOf_im, ← hsqa j hj]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (haM j hj) 2
    refine mul_le_mul_of_nonneg_left (add_le_add ha2 ?_) h32
    have : (0 : ℝ) ≤ 2 * m := by positivity
    have := mul_le_mul_of_nonneg_left hinv' this
    exact mul_le_mul_of_nonneg_right this hΔ0
  have hQlt : Q < 2 ^ L₀ * lam0 := by
    refine lt_of_le_of_lt ?_ hQ
    have hM2 : Mk ^ 2 ≤ x ^ (2 * m + 2) := by
      calc Mk ^ 2 ≤ (x ^ (m + 1)) ^ 2 := pow_le_pow_left₀ hMk0 hMX 2
        _ = x ^ (2 * m + 2) := by rw [← pow_mul]; ring_nf
    exact mul_le_mul_of_nonneg_left (by linarith) h32
  obtain ⟨ℓ, hℓN, hσ, hlam⟩ := Duhamel_exists_level (J := GUEDuhamelBA_gVp sz A t1 t0 K n e μ I)
    (K' := K n) (L₀ := L₀) (ω := ω) hlam0 hQ0 hQlt hk hVQ
  -- the stopped sum is the full sum
  have hfull : ∑ j ∈ Finset.range k, GUEDuhamelBA_gZst sz A t1 t0 K n e μ I (2 ^ ℓ * lam0) (j + 1) ω
      = ∑ j ∈ Finset.range k, GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j ω := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjs : j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I) (2 ^ ℓ * lam0) (K n) ω :=
      lt_of_lt_of_le (Finset.mem_range.1 hj) hσ
    simp only [GUEDuhamelBA_gZst]
    rw [Set.indicator_of_mem (show ω ∈ {ω | j < firstHit (GUEDuhamelBA_gVp sz A t1 t0 K n e μ I)
      (2 ^ ℓ * lam0) (K n) ω} from hjs)]
  have hmain := hZ ℓ hℓN
  rw [hfull] at hmain
  refine hmain.trans ?_
  -- `√(k λ_ℓ) ≤ √(kλ₀) + 8m √(kΔ) M_k + 8m √(esh)`
  have hkΔ : (k : ℝ) * Δ = gridTime t1 t0 K n k - t1 n := (htk k).symm
  have hkΔ1 : (k : ℝ) * Δ ≤ 1 := by
    have : (k : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hk
    nlinarith
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg k) hΔ0
  have hsq1 : Real.sqrt (k * (2 ^ ℓ * lam0))
      ≤ Real.sqrt (k * lam0) + 8 * m * Real.sqrt (k * Δ) * Mk + 8 * m * Real.sqrt esh := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hb1 : k * (2 ^ ℓ * lam0) ≤ k * lam0 + (64 * m ^ 2 * (k * Δ) * Mk ^ 2
        + 64 * m ^ 2 * (k * Δ) * esh) := by
      have := mul_le_mul_of_nonneg_left hlam hk0
      rw [hQdef] at this
      nlinarith
    have hA : 0 ≤ (k : ℝ) * lam0 := by positivity
    have hB : 0 ≤ 64 * (m : ℝ) ^ 2 * (k * Δ) * Mk ^ 2 :=
      mul_nonneg (mul_nonneg (by positivity) hkΔ0) (sq_nonneg _)
    have hC : 0 ≤ 64 * (m : ℝ) ^ 2 * (k * Δ) * esh :=
      mul_nonneg (mul_nonneg (by positivity) hkΔ0) hesh0
    have e1 : Real.sqrt (64 * (m : ℝ) ^ 2 * (k * Δ) * Mk ^ 2)
        = 8 * m * Real.sqrt (k * Δ) * Mk := by
      rw [show 64 * (m : ℝ) ^ 2 * (k * Δ) * Mk ^ 2 = (8 * m * Mk) ^ 2 * (k * Δ) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring
    have e2 : Real.sqrt (64 * (m : ℝ) ^ 2 * (k * Δ) * esh)
        = 8 * m * Real.sqrt (k * Δ) * Real.sqrt esh := by
      rw [show 64 * (m : ℝ) ^ 2 * (k * Δ) * esh = (8 * m) ^ 2 * ((k * Δ) * esh) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hkΔ0]
      ring
    have hsk : Real.sqrt (k * Δ) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hkΔ1
    calc Real.sqrt (k * (2 ^ ℓ * lam0))
        ≤ Real.sqrt (k * lam0 + (64 * m ^ 2 * (k * Δ) * Mk ^ 2
            + 64 * m ^ 2 * (k * Δ) * esh)) :=
          Real.sqrt_le_sqrt hb1
      _ ≤ Real.sqrt (k * lam0) + (Real.sqrt (64 * m ^ 2 * (k * Δ) * Mk ^ 2)
            + Real.sqrt (64 * m ^ 2 * (k * Δ) * esh)) := by
          refine (DuhamelC_sqrt_add_le hA (by positivity)).trans (add_le_add le_rfl ?_)
          exact DuhamelC_sqrt_add_le hB hC
      _ = Real.sqrt (k * lam0) + 8 * m * Real.sqrt (k * Δ) * Mk
            + 8 * m * Real.sqrt (k * Δ) * Real.sqrt esh := by rw [e1, e2]; ring
      _ ≤ _ := by
          have : 8 * (m : ℝ) * Real.sqrt (k * Δ) * Real.sqrt esh
              ≤ 8 * m * 1 * Real.sqrt esh := by
            have h0 : 0 ≤ 8 * (m : ℝ) := by positivity
            have := mul_le_mul_of_nonneg_left hsk h0
            exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
          linarith
  rw [← hkΔ]
  calc c * Real.sqrt (k * (2 ^ ℓ * lam0))
      ≤ c * (Real.sqrt (k * lam0) + 8 * m * Real.sqrt (k * Δ) * Mk
          + 8 * m * Real.sqrt esh) :=
        mul_le_mul_of_nonneg_left hsq1 hc
    _ = _ := by rw [hesh]; ring


end Pathwise2

section Pathwise3

variable {d : ℕ} {sz : Sizes d} {A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {μ : ℂ} {I : LoopIdx (Zd d (sz.L n))}

/-- **The pathwise bound on the good event**, at the scale `x = N = sz.size n` and with `sz.size n`
dyadic levels. -/
private theorem GUEDuhamelBA_pathwise (hA : ∀ n, (A n).IsHermitian) (hμ : 0 < μ.im) (hμ1 : ‖μ‖ ≤ 1)
    (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n) {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (heta : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaOf μ (t0 n))
    (hNΔ : ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1)
    (hQ : 32 * (I.length : ℝ) ^ 2 * gridStep t1 t0 K n
      * (((sz.size n : ℕ) : ℝ) ^ (2 * I.length + 2)
        + 2 * I.length * ((sz.size n : ℕ) : ℝ) ^ (2 * I.length + 4) * gridStep t1 t0 K n)
        < 2 ^ (sz.size n) * lam0)
    {c epsY : ℝ} (hc : 0 ≤ c) {ω : PathΩ sz}
    (htr : ∀ j < K n, ω (j + 1) ∈ DuhamelGood sz n)
    (hr : ∀ j < K n, ‖GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω‖
      ≤ GUEDuhamelBA_env d (sz.L n) (sz.W n) μ I.length (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2))
    {k : ℕ} (hk : k ≤ K n)
    (hZ : ∀ ℓ ≤ sz.size n, ‖∑ j ∈ Finset.range k,
        GUEDuhamelBA_gZst sz A t1 t0 K n e μ I (2 ^ ℓ * lam0) (j + 1) ω‖
      ≤ c * Real.sqrt (k * (2 ^ ℓ * lam0)))
    (hY : ‖∑ j ∈ Finset.range k, GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω‖ ≤ epsY) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n k ω))
          (ztOf μ e (gridTime t1 t0 K n k)) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n 0 ω))
            (ztOf μ e (gridTime t1 t0 K n 0)) I
        - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
            genMatGUEOf d (sz.L n) (sz.W n) μ e (gridTime t1 t0 K n j) (GUEDuhamelBA_gH sz A t1 t0 K n j ω) I‖
      ≤ c * Real.sqrt (k * lam0)
        + 8 * I.length * c * Real.sqrt (gridTime t1 t0 K n k - t1 n)
          * (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ)) : ℝ)⁻¹
              * (etaOf μ (gridTime t1 t0 K n j))⁻¹ ^ 2
              * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
                  (ztOf μ e (gridTime t1 t0 K n j)) (2 * I.length)))
        + 8 * I.length * c * Real.sqrt (2 * I.length * ((sz.size n : ℕ) : ℝ) ^ (2 * I.length + 4)
            * gridStep t1 t0 K n)
        + epsY
        + (K n : ℝ) * (16 * Real.exp 2 * ((I.length : ℝ) * ((I.length : ℝ) + 1)
            * ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (I.length + 2))
            * (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ 4
            * Real.exp (-((sz.size n : ℕ) : ℝ) / 4))
        + (K n : ℝ) * (16 * ((I.length : ℝ) + 3) ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 4
            * (1 + ((sz.size n : ℕ) : ℝ)) ^ (I.length + 4) * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)) := by
  obtain ⟨hΔ0, hKΔ, hη, _, _, _⟩ :=
    GUEDuhamelBA_grid_facts (e := e) hμ hμ1 ht1 hst ht0 hK heta
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  rw [GUEDuhamelBA_telescope hA hμ hwf hst ht0 htr hk]
  have hZb := GUEDuhamelBA_Z_bound (I := I) hA hμ hμ1 hwf ht1 hst ht0 hK hlam0 hN1 heta hNΔ hQ hc hk hZ
  have hkK : (k : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hk
  have hinvN : ∀ j < K n, ((ztOf μ e (gridTime t1 t0 K n (j + 1))).im)⁻¹ ≤ N := by
    intro j hj
    have h := (hη (j + 1) hj).1
    have hpos : 0 < (ztOf μ e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (by positivity) h
    rw [inv_le_comm₀ hpos hN0]; exact h
  -- the bias sum
  set EBt : ℝ := 16 * Real.exp 2 * ((I.length : ℝ) * ((I.length : ℝ) + 1) * N * N ^ (I.length + 2))
      * (gridStep t1 t0 K n / N) * N ^ 4 * Real.exp (-N / 4) with hEBt
  have hv0 : 0 ≤ Duhamelv sz t1 t0 K n := div_nonneg hΔ0 (Nat.cast_nonneg _)
  have hB : ∀ j ∈ Finset.range k, ‖DuhamelB sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
      (Duhamelv sz t1 t0 K n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)‖ ≤ EBt := by
    intro j hj
    have hjK : j < K n := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    obtain ⟨hz, hΦ, hC₂⟩ := GUEDuhamelBA_bddC2C_Phi (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
      (e := e) (μ := μ) (I := I) hμ hwf hst ht0 hjK
    refine (Duhamel_norm_B_le hΦ hC₂ hv0 (GUEDuhamelBA_gH_isHermitian A hA t1 t0 K n j ω)).trans ?_
    rw [hEBt]
    have hpos : 0 < (ztOf μ e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (by positivity) (hη (j + 1) hjK).1
    have hinv : (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ ≤ N := by
      rw [GUEDuhamelBA_etaOf_eq e]; exact hinvN j hjK
    have hetapos : 0 < etaOf μ (gridTime t1 t0 K n (j + 1)) := by
      rw [GUEDuhamelBA_etaOf_eq e]; exact hpos
    have hcast : ((I.length * (I.length + 1) : ℕ) : ℝ) = (I.length : ℝ) * ((I.length : ℝ) + 1) := by
      push_cast; ring
    have hC2 : ((I.length * (I.length + 1) : ℕ) : ℝ) * N
        * (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2)
        ≤ (I.length : ℝ) * ((I.length : ℝ) + 1) * N * N ^ (I.length + 2) := by
      have := pow_le_pow_left₀ (inv_nonneg.2 hetapos.le) hinv (I.length + 2)
      have h0 : 0 ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) * N := by positivity
      rw [hcast]
      rw [hcast] at h0
      exact mul_le_mul_of_nonneg_left this h0
    have hE : 0 ≤ Real.exp (-N / 4) := (Real.exp_pos _).le
    have hc4 : 0 ≤ N ^ 4 := by positivity
    have h16 : (0 : ℝ) ≤ 16 * Real.exp 2 := by positivity
    have hv : Duhamelv sz t1 t0 K n = gridStep t1 t0 K n / N := rfl
    rw [hv]
    have h1 := mul_le_mul_of_nonneg_left hC2 h16
    have h2 := mul_le_mul_of_nonneg_right h1 (div_nonneg hΔ0 hN0.le)
    have h3 := mul_le_mul_of_nonneg_right h2 hc4
    have h4 := mul_le_mul_of_nonneg_right h3 hE
    exact h4
  have hEBt0 : 0 ≤ EBt := by
    rw [hEBt]
    have h1 : 0 ≤ (I.length : ℝ) * ((I.length : ℝ) + 1) * N * N ^ (I.length + 2) := by positivity
    have h2 := (Real.exp_pos (-N / 4)).le
    have h16 : (0 : ℝ) ≤ 16 * Real.exp 2 := by positivity
    have hv : 0 ≤ gridStep t1 t0 K n / N := div_nonneg hΔ0 hN0.le
    positivity
  have hBsum : ‖∑ j ∈ Finset.range k, DuhamelB sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
      (Duhamelv sz t1 t0 K n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)‖ ≤ (K n : ℝ) * EBt := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hB).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hkK hEBt0
  -- the sum of the one-step remainders `r_j`
  set ERt : ℝ := 16 * ((I.length : ℝ) + 3) ^ 4 * N ^ 4 * (1 + N) ^ (I.length + 4)
      * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) with hERt
  have hr' : ∀ j ∈ Finset.range k, ‖GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω‖ ≤ ERt := by
    intro j hj
    have hjK : j < K n := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    refine (hr j hjK).trans ?_
    rw [hERt]
    have hpos : 0 < (ztOf μ e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (by positivity) (hη (j + 1) hjK).1
    have hinv : (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ ≤ N := by
      rw [GUEDuhamelBA_etaOf_eq e]; exact hinvN j hjK
    have hetapos : 0 < etaOf μ (gridTime t1 t0 K n (j + 1)) := by
      rw [GUEDuhamelBA_etaOf_eq e]; exact hpos
    have h1 : (1 + (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹) ^ (I.length + 4)
        ≤ (1 + N) ^ (I.length + 4) := by
      have : 0 ≤ 1 + (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ := by positivity
      gcongr
    have h2 : 0 ≤ gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ0 _
    have hmat : GUEDuhamelBA_env d (sz.L n) (sz.W n) μ I.length (gridTime t1 t0 K n (j + 1))
        = 16 * ((I.length : ℝ) + 3) ^ 4 * N ^ 4
          * (1 + (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹) ^ (I.length + 4) := rfl
    rw [hmat]
    have h3 : 0 ≤ 16 * ((I.length : ℝ) + 3) ^ 4 * N ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2
  have hERt0 : 0 ≤ ERt := by
    rw [hERt]
    have := Real.rpow_nonneg hΔ0 ((3 : ℝ) / 2)
    positivity
  have hrsum : ‖∑ j ∈ Finset.range k, GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω‖ ≤ (K n : ℝ) * ERt := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hr').trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hkK hERt0
  -- combine
  set SZ := ∑ j ∈ Finset.range k, GUEDuhamelBA_gZinc sz A t1 t0 K n e μ I j ω
  set SY := ∑ j ∈ Finset.range k, GUEDuhamelBA_gYst sz A t1 t0 K n e μ I (j + 1) ω
  set SB := ∑ j ∈ Finset.range k, DuhamelB sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j)
      (Duhamelv sz t1 t0 K n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)
  set SR := ∑ j ∈ Finset.range k, GUEDuhamelBA_gr sz A t1 t0 K n e μ I j ω
  have htri : ‖SZ + SY - SB + SR‖ ≤ ‖SZ‖ + ‖SY‖ + ‖SB‖ + ‖SR‖ := by
    calc ‖SZ + SY - SB + SR‖ ≤ ‖SZ + SY - SB‖ + ‖SR‖ := norm_add_le _ _
      _ ≤ ‖SZ + SY‖ + ‖SB‖ + ‖SR‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖SZ‖ + ‖SY‖ + ‖SB‖ + ‖SR‖ := by gcongr; exact norm_add_le _ _
  refine htri.trans ?_
  linarith


end Pathwise3

/-! ## 7. The good events hold with high probability (private) -/

section Events

variable {d : ℕ} (sz : Sizes d) (A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- **The dyadic Azuma events**: all the dyadic Azuma events hold simultaneously, w.h.p. -/
private theorem GUEDuhamelBA_highProb_Z {E t1 t0 : ℕ → ℝ} {μ : ℕ → ℂ}
    (hsize : Tendsto (fun n => sz.size n) atTop atTop) (ht10 : ∀ n, t1 n ≤ t0 n) (n0 m : ℕ)
    (K : ℕ → ℕ) (hKn : ∀ n, K n = (sz.size n + 1) ^ (32 * n0 + 64))
    {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (Pgue sz) sz.size (fun n =>
      ⋂ u : Fin (sz.size n + 1) × Fin (K n + 1)
          × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))),
      {ω | ‖∑ j ∈ Finset.range (u.2.1 : ℕ), GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n)
          (loopOf u.2.2.1 u.2.2.2) (2 ^ (u.1 : ℕ) * DuhamelC_lam0 n0 (sz.size n)) (j + 1) ω‖
        ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * Real.sqrt ((u.2.1 : ℕ)
            * (2 ^ (u.1 : ℕ) * DuhamelC_lam0 n0 (sz.size n)))}) := by
  refine RBM.Path.highProbAt_iInter (Pgue sz) sz.size
    (C := ((2 * (32 * n0 + 64) + 2 * m + 3 : ℕ) : ℝ)) (by positivity)
    ((hsize.eventually (eventually_ge_atTop 2)).mono fun n hN =>
      DuhamelC_card_le sz n0 m n K hN (hKn n)) ?_
  intro D hD
  filter_upwards [hsize.eventually (DuhamelC_ev_exp_rpow (a := τ / 2) (by positivity) D),
    hsize.eventually (eventually_ge_atTop 1)] with n hN hN1
  intro u
  obtain ⟨ℓ, k, x⟩ := u
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set lam := 2 ^ (ℓ : ℕ) * DuhamelC_lam0 n0 (sz.size n) with hlamdef
  have hlam : 0 < lam := mul_pos (by positivity) (DuhamelC_lam0_pos n0 _ hN1)
  have hv : 0 ≤ Duhamelv sz t1 t0 K n := by
    unfold Duhamelv gridStep
    exact div_nonneg (div_nonneg (by linarith [ht10 n]) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
  · have huniv : {ω | ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n)
          (loopOf x.1 x.2) lam (j + 1) ω‖
        ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * Real.sqrt ((k : ℕ) * lam)} = Set.univ := by
      ext ω; simp [hk0]
    simp only [hlamdef] at huniv
    rw [huniv, Set.compl_univ, measure_empty]; exact zero_le
  · set ε := 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * Real.sqrt ((k : ℕ) * lam) with hεdef
    have hε0 : 0 ≤ ε := by positivity
    have hsub : {ω | ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n)
          (loopOf x.1 x.2) lam (j + 1) ω‖ ≤ ε}ᶜ
        ⊆ {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n)
          (loopOf x.1 x.2) lam (j + 1) ω‖} := fun ω hω => le_of_lt (not_le.1 (by simpa using hω))
    have haz := GUEDuhamelBA_azuma_Z (sz := sz) (A := A) (t1 := t1) (t0 := t0) (K := K) (n := n)
      (e := E n) (μ := μ n) (I := loopOf x.1 x.2) hlam hv (k : ℕ) hε0
    have hkl : (0 : ℝ) < (k : ℕ) * lam := mul_pos (by exact_mod_cast hkpos) hlam
    have hexp : -ε ^ 2 / (4 * ((k : ℕ) * lam)) = -((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      have hq : (((sz.size n : ℕ) : ℝ) ^ (τ / 4)) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
      rw [hεdef, mul_pow, mul_pow, hq, Real.sq_sqrt hkl.le]
      field_simp
      ring
    rw [hexp] at haz
    calc (Pgue sz) {ω | ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n)
          (loopOf x.1 x.2) lam (j + 1) ω‖ ≤ ε}ᶜ
        ≤ (Pgue sz) {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2) lam (j + 1) ω‖} := measure_mono hsub
      _ = ENNReal.ofReal ((Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2) lam (j + 1) ω‖}) :=
          (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (4 * Real.exp (-((sz.size n : ℕ) : ℝ) ^ (τ / 2))) :=
          ENNReal.ofReal_le_ofReal haz
      _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hN

end Events

section Events2

variable {d : ℕ} (sz : Sizes d) (A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- **The uniform truncation bound** of `T` along the grid: `‖T‖ ≤ n(n+1)/2 · N^{n+6} Δ` at
Hermitian base points, `x = N = sz.size n`. -/
private theorem GUEDuhamelBA_T_le_uniform {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {μ : ℂ}
    {I : LoopIdx (Zd d (sz.L n))} (hμ : 0 < μ.im) (hμ1 : ‖μ‖ ≤ 1) (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n)
    (heta : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaOf μ (t0 n)) {j : ℕ} (hj : j < K n)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    (y : Sizes.SeqΩ sz) :
    ‖DuhamelT sz n (GUEDuhamelBA_gPhi sz t1 t0 K n e μ I j) (Duhamelv sz t1 t0 K n) M y‖
      ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) / 2 * ((sz.size n : ℕ) : ℝ) ^ (I.length + 6)
          * gridStep t1 t0 K n := by
  obtain ⟨hΔ0, _, hη, _, _, _⟩ := GUEDuhamelBA_grid_facts (e := e) hμ hμ1 ht1 hst ht0 hK heta
  obtain ⟨hz, hΦ, hC₂⟩ := GUEDuhamelBA_bddC2C_Phi (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
    (e := e) (μ := μ) (I := I) hμ hwf hst ht0 hj
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast DuhamelC_size_pos sz n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hv : 0 ≤ Duhamelv sz t1 t0 K n := div_nonneg hΔ0 (Nat.cast_nonneg _)
  refine (Duhamel_norm_T_le hΦ hC₂ hv hM y).trans ?_
  have hpos : 0 < (ztOf μ e (gridTime t1 t0 K n (j + 1))).im :=
    lt_of_lt_of_le (by positivity) (hη (j + 1) hj).1
  have hetapos : 0 < etaOf μ (gridTime t1 t0 K n (j + 1)) := by
    rw [GUEDuhamelBA_etaOf_eq e]; exact hpos
  have hinv : (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ ≤ N := by
    rw [GUEDuhamelBA_etaOf_eq e, inv_le_comm₀ hpos hN0]; exact (hη (j + 1) hj).1
  have hpow : (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2) ≤ N ^ (I.length + 2) :=
    pow_le_pow_left₀ (inv_nonneg.2 hetapos.le) hinv _
  have hvN : Duhamelv sz t1 t0 K n = gridStep t1 t0 K n / N := rfl
  have hc0 : (0 : ℝ) ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) * N := by positivity
  calc ((I.length * (I.length + 1) : ℕ) : ℝ) * N
          * (etaOf μ (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2) / 2
          * Duhamelv sz t1 t0 K n * N ^ 4
      ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) * N * N ^ (I.length + 2) / 2
          * (gridStep t1 t0 K n / N) * N ^ 4 := by
        rw [hvN]
        have h1 := mul_le_mul_of_nonneg_left hpow hc0
        have h2 : 0 ≤ gridStep t1 t0 K n / N := div_nonneg hΔ0 hN0.le
        have h3 : 0 ≤ N ^ 4 := by positivity
        gcongr
    _ = ((I.length * (I.length + 1) : ℕ) : ℝ) / 2 * N ^ (I.length + 6) * gridStep t1 t0 K n := by
        field_simp
        ring

/-- **The Azuma events of `Ỹ`** hold simultaneously, w.h.p. -/
private theorem GUEDuhamelBA_highProb_Y (hA : ∀ n, (A n).IsHermitian)
    (hsize : Tendsto (fun n => sz.size n) atTop atTop) (n0 m : ℕ) (hm : m ≤ 2 * n0)
    (K : ℕ → ℕ) (hKn : ∀ n, K n = (sz.size n + 1) ^ (32 * n0 + 64)) (hKpos : ∀ n, 0 < K n)
    {E t1 t0 : ℕ → ℝ} {μ : ℕ → ℂ} (hμ : ∀ n, 0 < (μ n).im) (hμ1 : ∀ n, ‖μ n‖ ≤ 1) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (heta : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaOf (μ n) (t0 n)) :
    HighProbAt (Pgue sz) sz.size (fun n =>
      ⋂ u : Fin (K n + 1) × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))),
      {ω | ‖∑ j ∈ Finset.range (u.1 : ℕ), GUEDuhamelBA_gYst sz A t1 t0 K n (E n) (μ n)
          (loopOf u.2.1 u.2.2) (j + 1) ω‖ ≤ DuhamelC_epsY n0 (sz.size n)}) := by
  refine RBM.Path.highProbAt_iInter (Pgue sz) sz.size
    (C := ((2 * (32 * n0 + 64) + 2 * m + 3 : ℕ) : ℝ)) (by positivity)
    ((hsize.eventually (eventually_ge_atTop 2)).mono fun n hN =>
      DuhamelC_card_le' sz n0 m n K hN (hKn n)) ?_
  intro D hD
  filter_upwards [heta, hsize.eventually (DuhamelC_num_step n0),
    hsize.eventually (DuhamelC_num_Y (n := m) hm), hsize.eventually (DuhamelC_ev_exp_lin D)]
    with n hηN hstep hY hexpN
  intro u
  obtain ⟨k, x⟩ := u
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast DuhamelC_size_pos sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hwf : (loopOf x.1 x.2).WF := DuhamelC_loopOf_wf x.1 x.2
  have hlen : (loopOf x.1 x.2).length = m := DuhamelC_loopOf_length x.1 x.2
  have hK : 0 < K n := hKpos n
  obtain ⟨hΔ0, hKΔ, _, _, _, _⟩ := GUEDuhamelBA_grid_facts (e := E n) (hμ n) (hμ1 n) (ht1 n)
    (ht10 n) (ht0 n) hK hηN
  set S : ℝ := ((sz.size n : ℕ) : ℝ) with hSdef
  set Δ := gridStep t1 t0 K n with hΔdef
  have hKcast := DuhamelC_K_cast sz n0 n K (hKn n)
  have hTu := fun j (hj : j < K n) (M : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian) (y : Sizes.SeqΩ sz) =>
    GUEDuhamelBA_T_le_uniform sz (e := E n) (μ := μ n) (I := loopOf x.1 x.2) (hμ n) (hμ1 n) hwf (ht1 n) (ht10 n) (ht0 n) hK hηN hj hM y
  rw [hlen] at hTu
  have hl0 := DuhamelC_lam0_pos n0 (sz.size n) (DuhamelC_size_pos sz n)
  set l0 := DuhamelC_lam0 n0 (sz.size n) with hl0def
  set b := ((m * (m + 1) : ℕ) : ℝ) / 2 * S ^ (m + 6) * Δ + l0 with hbdef
  have hb0 : 0 < b := by
    have hcm : 0 ≤ ((m * (m + 1) : ℕ) : ℝ) / 2 := by positivity
    have h1 : 0 ≤ ((m * (m + 1) : ℕ) : ℝ) / 2 * S ^ (m + 6) * Δ :=
      mul_nonneg (mul_nonneg hcm (pow_nonneg hN0.le _)) hΔ0
    rw [hbdef]; linarith
  have hb : ∀ j < K n, ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → ∀ y, ‖DuhamelT sz n (GUEDuhamelBA_gPhi sz t1 t0 K n (E n) (μ n)
        (loopOf x.1 x.2) j) (Duhamelv sz t1 t0 K n) M y‖ ≤ b := by
    intro j hj M hM y
    refine (hTu j hj M hM y).trans ?_
    rw [hbdef]; linarith
  have hεY : 0 ≤ DuhamelC_epsY n0 (sz.size n) := by unfold DuhamelC_epsY; positivity
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
  · have huniv : {ω | ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gYst sz A t1 t0 K n (E n) (μ n)
          (loopOf x.1 x.2) (j + 1) ω‖ ≤ DuhamelC_epsY n0 (sz.size n)} = Set.univ := by
      ext ω; simp [hk0, hεY]
    rw [huniv, Set.compl_univ, measure_empty]; exact zero_le
  · have hkK : (k : ℕ) ≤ K n := Nat.lt_succ_iff.1 k.2
    have haz := GUEDuhamelBA_azuma_Y (sz := sz) (A := A) (t1 := t1) (t0 := t0) (K := K) (n := n)
      (e := E n) (μ := μ n) (I := loopOf x.1 x.2) hA hb0.le hb hkK hεY
    have hkR : ((k : ℕ) : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hkK
    have hΔa := (hstep Δ hΔ0 (by rw [← hKcast]; exact hKΔ)).1
    have hkΔ : ((k : ℕ) : ℝ) * Δ ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hkR hΔ0) hKΔ
    have hY' := hY Δ ((k : ℕ) : ℝ) hΔ0 (Nat.cast_nonneg _) hkΔ hΔa
      (by rw [← hKcast]; exact hkR)
    have hden : 0 < 16 * ((k : ℕ) : ℝ) * b ^ 2 := by
      have : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hkpos
      exact mul_pos (mul_pos (by norm_num) this) (pow_pos hb0 2)
    have hexp : -(DuhamelC_epsY n0 (sz.size n)) ^ 2 / (4 * (((k : ℕ) : ℝ) * (4 * b ^ 2)))
        ≤ -S := by
      have e : 4 * (((k : ℕ) : ℝ) * (4 * b ^ 2)) = 16 * ((k : ℕ) : ℝ) * b ^ 2 := by ring
      rw [e, neg_div, neg_le_neg_iff, le_div_iff₀ hden]
      have h1 := hY'
      rw [show ((S : ℝ) ^ (40 * n0 + 80))⁻¹ = l0 by rw [hl0def]; rfl, ← hbdef] at h1
      unfold DuhamelC_epsY
      rw [le_div_iff₀ hN0] at h1
      linarith
    have hsub : {ω | ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gYst sz A t1 t0 K n (E n) (μ n)
          (loopOf x.1 x.2) (j + 1) ω‖ ≤ DuhamelC_epsY n0 (sz.size n)}ᶜ
        ⊆ {ω | DuhamelC_epsY n0 (sz.size n) ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          GUEDuhamelBA_gYst sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2) (j + 1) ω‖} :=
      fun ω hω => le_of_lt (not_le.1 (by simpa using hω))
    calc (Pgue sz) {ω | ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gYst sz A t1 t0 K n (E n) (μ n)
          (loopOf x.1 x.2) (j + 1) ω‖ ≤ DuhamelC_epsY n0 (sz.size n)}ᶜ
        ≤ (Pgue sz) {ω | DuhamelC_epsY n0 (sz.size n) ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          GUEDuhamelBA_gYst sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2) (j + 1) ω‖} :=
          measure_mono hsub
      _ = ENNReal.ofReal ((Pgue sz).real {ω | DuhamelC_epsY n0 (sz.size n) ≤ ‖∑ j ∈
          Finset.range (k : ℕ), GUEDuhamelBA_gYst sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2)
          (j + 1) ω‖}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(DuhamelC_epsY n0 (sz.size n)) ^ 2
          / (4 * (((k : ℕ) : ℝ) * (4 * b ^ 2))))) := ENNReal.ofReal_le_ofReal haz
      _ ≤ ENNReal.ofReal (4 * Real.exp (-S)) := by
          apply ENNReal.ofReal_le_ofReal
          have := Real.exp_le_exp.2 hexp
          linarith
      _ ≤ ENNReal.ofReal (S ^ (-D)) := ENNReal.ofReal_le_ofReal hexpN

/-- **The drift remainder bounds** hold almost surely, hence w.h.p.: `hdr` is the almost-sure bound of the remainder
of one step (`Duhamel_drift_remainder_aeBA` at `sz.withLam 0`, `A n = g Ψ_I`). -/
private theorem GUEDuhamelBA_highProb_AE (m : ℕ) (K : ℕ → ℕ)
    {E t1 t0 : ℕ → ℝ} {μ : ℕ → ℂ}
    (hdr : ∀ n, ∀ j < K n, ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → ∀ᵐ ω ∂(Pgue sz),
      ‖GUEDuhamelBA_gr sz A t1 t0 K n (E n) (μ n) I j ω‖
        ≤ GUEDuhamelBA_env d (sz.L n) (sz.W n) (μ n) I.length (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)) :
    HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ j < K n,
      ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖GUEDuhamelBA_gr sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2) j ω‖
        ≤ GUEDuhamelBA_env d (sz.L n) (sz.W n) (μ n) (loopOf x.1 x.2).length
            (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)}) := by
  intro D _
  refine Eventually.of_forall fun n => ?_
  have hae : ∀ᵐ ω ∂(Pgue sz), ∀ j : Fin (K n), ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖GUEDuhamelBA_gr sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2) j ω‖
        ≤ GUEDuhamelBA_env d (sz.L n) (sz.W n) (μ n) (loopOf x.1 x.2).length
            (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro x
    exact hdr n j j.2 (loopOf x.1 x.2) (DuhamelC_loopOf_wf x.1 x.2)
  have hnull : (Pgue sz) {ω | ∀ j < K n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖GUEDuhamelBA_gr sz A t1 t0 K n (E n) (μ n) (loopOf x.1 x.2) j ω‖
        ≤ GUEDuhamelBA_env d (sz.L n) (sz.W n) (μ n) (loopOf x.1 x.2).length
            (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)}ᶜ = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun ω hω => ?_) hae
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hω ⊢
    intro hall
    exact hω fun j hj x => hall ⟨j, hj⟩ x
  rw [hnull]; exact zero_le

end Events2

/-! ## 8. The main theorem (private, generic in the Hermitian shift) -/

section Main

variable {d : ℕ} (sz : Sizes d) (A : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- **The discrete Duhamel remainder of the GUE-phase loops**, for a grid length `K`
with `K n = (N+1)^{32n₀+64}`
(`K = gueGridK sz n₀`; a variable so that nothing unfolds the power). -/
private theorem GUEDuhamelBA_main {τU : ℝ} (hτU : 0 < τU) (n0 : ℕ) (K : ℕ → ℕ)
    (hKn : ∀ n, K n = (sz.size n + 1) ^ (32 * n0 + 64)) (hA : ∀ n, (A n).IsHermitian) {E t1 t0 : ℕ → ℝ} {μ : ℕ → ℂ}
    (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hμ : ∀ n, 0 < (μ n).im) (hμ1 : ∀ n, ‖μ n‖ ≤ 1) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (hdr : ∀ n, ∀ j < K n, ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → ∀ᵐ ω ∂(Pgue sz),
      ‖GUEDuhamelBA_gr sz A t1 t0 K n (E n) (μ n) I j ω‖
        ≤ GUEDuhamelBA_env d (sz.L n) (sz.W n) (μ n) I.length (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2))
    (hscale : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (m : ℕ) (hm : m ≤ 2 * n0) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (K n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n p.1 ω))
            (ztOf (μ n) (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n 0 ω))
            (ztOf (μ n) (E n) (gridTime t1 t0 K n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUEOf d (sz.L n) (sz.W n) (μ n) (E n) (gridTime t1 t0 K n j)
                (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => Real.sqrt (gridTime t1 t0 K n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (μ n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) (ztOf (μ n) (E n) (gridTime t1 t0 K n j)) (2 * m)))
        + (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n p.1))⁻¹ ^ m) := by
  have hKpos : ∀ n, 0 < K n := fun n => by rw [hKn n]; positivity
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by
    exact_mod_cast DuhamelC_size_pos sz n
  -- `η_{t₀} ≥ N⁻¹`
  have heta : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaOf (μ n) (t0 n) := by
    filter_upwards [hscale] with n hs
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith [hN1 n]
    have hη0 : 0 < etaOf (μ n) (t0 n) := mul_pos (sub_pos.2 (ht0 n)) (hμ n)
    have hpow : ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) * etaOf (μ n) (t0 n) := by
      have hpos : 0 < ((sz.size n : ℕ) : ℝ) * etaOf (μ n) (t0 n) := mul_pos hN0 hη0
      have := hs.trans hpow
      rwa [inv_le_one_iff₀, or_iff_right (not_le.2 hpos)] at this
    rw [inv_le_iff_one_le_mul₀ hN0]
    nlinarith
  -- `ζ ≥ 0`
  have hζ0 : ∀ n (p : Fin (K n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (ω : PathΩ sz),
      0 ≤ Real.sqrt (gridTime t1 t0 K n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (μ n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) (ztOf (μ n) (E n) (gridTime t1 t0 K n j)) (2 * m)))
        + (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n p.1))⁻¹ ^ m := by
    intro n p ω
    have h1 : 0 ≤ ⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (μ n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) (ztOf (μ n) (E n) (gridTime t1 t0 K n j)) (2 * m)) :=
      Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
    have hle : gridTime t1 t0 K n p.1 ≤ t0 n := by
      have hk : (p.1 : ℝ) ≤ (K n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 p.1.2
      have hKp : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast hKpos n
      unfold gridTime gridStep
      have : (p.1 : ℝ) * ((t0 n - t1 n) / (K n : ℝ)) ≤ t0 n - t1 n := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hKp]
        nlinarith [ht10 n]
      linarith
    have hη : 0 < etaOf (μ n) (gridTime t1 t0 K n p.1) :=
      mul_pos (sub_pos.2 (lt_of_le_of_lt hle (ht0 n))) (hμ n)
    have h2 : 0 ≤ (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n p.1))⁻¹ ^ m := by
      have : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith [hN1 n]
      positivity
    have h3 := Real.sqrt_nonneg (gridTime t1 t0 K n p.1 - t1 n)
    positivity
  -- reduction to `τ ≤ 1`
  suffices hmain : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ p :
      Fin (K n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n p.1 ω))
            (ztOf (μ n) (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n 0 ω))
            (ztOf (μ n) (E n) (gridTime t1 t0 K n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUEOf d (sz.L n) (sz.W n) (μ n) (E n) (gridTime t1 t0 K n j)
                (GUEDuhamelBA_gH sz A t1 t0 K n j ω) (loopOf p.2.1 p.2.2)‖
        ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (Real.sqrt (gridTime t1 t0 K n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (μ n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω)) (ztOf (μ n) (E n) (gridTime t1 t0 K n j)) (2 * m)))
        + (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n p.1))⁻¹ ^ m)}) by
    intro τ hτ D hD
    filter_upwards [hmain (min τ 1) (lt_min hτ one_pos) (min_le_right _ _) D hD] with n hN
    refine le_trans (measure_mono ?_) hN
    intro ω hω hgood
    obtain ⟨p, hp⟩ := hω
    have h1 := hgood p
    have hpow : ((sz.size n : ℕ) : ℝ) ^ (min τ 1) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (hN1 n) (min_le_left _ _)
    have := mul_le_mul_of_nonneg_right hpow (hζ0 n p ω)
    simp only at hp
    linarith
  intro τ hτ hτ1
  have hT' : HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ k, 1 ≤ k → k ≤ K n →
      ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)}) :=
    RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (gue_highProb_incr_le sz n0 hsize)
      (Eventually.of_forall fun n ω hω k hk1 hkK i j => hω k hk1 (by rw [hKn n] at hkK; exact hkK) i j)
  have hAE := GUEDuhamelBA_highProb_AE sz A m K hdr
  have hZ := GUEDuhamelBA_highProb_Z sz A (E := E) (μ := μ) hsize ht10 n0 m K hKn hτ
  have hY := GUEDuhamelBA_highProb_Y sz A hA (E := E) hsize n0 m hm K hKn hKpos hμ hμ1 ht1 ht10 ht0 heta
  refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsize
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsize
        (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsize hT' hAE) hZ) hY) ?_
  filter_upwards [heta, hsize.eventually (DuhamelC_num_step n0),
    hsize.eventually (DuhamelC_num_Q (n := m) hm), hsize.eventually (DuhamelC_num_E1 hm hτ1),
    hsize.eventually (DuhamelC_num_E2 hm hτ1), hsize.eventually (DuhamelC_num_E3 hm),
    hsize.eventually (DuhamelC_num_E4 (n := m)), hsize.eventually (DuhamelC_num_E5 hm),
    hsize.eventually (DuhamelC_num_tau m hτ)]
    with n hηN hstep hQ hE1 hE2 hE3 hE4 hE5 htau
  rintro ω ⟨⟨⟨hωT, hωAE⟩, hωZ⟩, hωY⟩ ⟨k, x⟩
  dsimp only
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith [hN1 n]
  have hwf := DuhamelC_loopOf_wf x.1 x.2
  have hIlen : (loopOf x.1 x.2).length = m := DuhamelC_loopOf_length x.1 x.2
  obtain ⟨hΔ0, hKΔ, hη, _, _, _⟩ := GUEDuhamelBA_grid_facts (e := E n) (hμ n) (hμ1 n) (ht1 n)
    (ht10 n) (ht0 n) (hKpos n) hηN
  have hKcast := DuhamelC_K_cast sz n0 n K (hKn n)
  obtain ⟨hΔa, hNΔ⟩ := hstep _ hΔ0 (by rw [← hKcast]; exact hKΔ)
  have hkK : (k : ℕ) ≤ K n := Nat.lt_succ_iff.1 k.2
  have htr : ∀ j < K n, ω (j + 1) ∈ DuhamelGood sz n :=
    fun j hj i l => hωT (j + 1) (by omega) (by omega) i l
  have hr := fun j (hj : j < K n) => hωAE j hj x
  have hZω : ∀ ℓ ≤ sz.size n, ‖∑ j ∈ Finset.range (k : ℕ), GUEDuhamelBA_gZst sz A t1 t0 K n (E n) (μ n)
      (loopOf x.1 x.2) (2 ^ ℓ * DuhamelC_lam0 n0 (sz.size n)) (j + 1) ω‖
      ≤ (2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4))
        * Real.sqrt ((k : ℕ) * (2 ^ ℓ * DuhamelC_lam0 n0 (sz.size n))) := by
    intro ℓ hℓ
    exact Set.mem_iInter.1 hωZ ⟨⟨ℓ, Nat.lt_succ_of_le hℓ⟩, k, x⟩
  have hYω := Set.mem_iInter.1 hωY ⟨k, x⟩
  have hQ' : 32 * ((loopOf x.1 x.2).length : ℝ) ^ 2 * gridStep t1 t0 K n
      * (((sz.size n : ℕ) : ℝ) ^ (2 * (loopOf x.1 x.2).length + 2)
        + 2 * (loopOf x.1 x.2).length * ((sz.size n : ℕ) : ℝ) ^ (2 * (loopOf x.1 x.2).length + 4)
          * gridStep t1 t0 K n) < 2 ^ (sz.size n) * DuhamelC_lam0 n0 (sz.size n) := by
    rw [hIlen]; exact hQ _ hΔ0 hΔa
  have hc : 0 ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := by positivity
  have hpath := GUEDuhamelBA_pathwise (A := A) (e := E n) (μ := μ n) (I := loopOf x.1 x.2) hA (hμ n) (hμ1 n) hwf (ht1 n) (ht10 n) (ht0 n)
    (hKpos n) (DuhamelC_lam0_pos n0 _ (DuhamelC_size_pos sz n)) (hN1 n) hηN hNΔ
    hQ' hc htr hr hkK hZω hYω
  rw [hIlen] at hpath
  refine hpath.trans ?_
  -- the scalar bookkeeping
  set Δ := gridStep t1 t0 K n with hΔdef
  set sq := Real.sqrt (gridTime t1 t0 K n (k : ℕ) - t1 n) with hsqdef
  set M := ⨆ j : Fin (k : ℕ), Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
      (etaOf (μ n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
      RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (GUEDuhamelBA_gH sz A t1 t0 K n j ω))
        (ztOf (μ n) (E n) (gridTime t1 t0 K n j)) (2 * m)) with hMdef
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hK0 : (0 : ℝ) ≤ (K n : ℝ) := Nat.cast_nonneg _
  -- the five error terms
  have hT1 : 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)
      * Real.sqrt ((k : ℕ) * DuhamelC_lam0 n0 (sz.size n)) ≤ (((sz.size n : ℕ) : ℝ) ^ m)⁻¹ / 5 := by
    refine le_trans ?_ hE1
    have hkR : ((k : ℕ) : ℝ) ≤ (((sz.size n : ℕ) : ℝ) + 1) ^ (32 * n0 + 64) := by
      rw [← hKcast]; exact_mod_cast hkK
    have hl := DuhamelC_lam0_pos n0 (sz.size n) (DuhamelC_size_pos sz n)
    have : Real.sqrt ((k : ℕ) * DuhamelC_lam0 n0 (sz.size n))
        ≤ Real.sqrt ((((sz.size n : ℕ) : ℝ) + 1) ^ (32 * n0 + 64)
          * (((sz.size n : ℕ) : ℝ) ^ (40 * n0 + 80))⁻¹) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hkR hl.le)
    exact mul_le_mul_of_nonneg_left this hc
  have hT2 : 8 * (m : ℝ) * (2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4))
      * Real.sqrt (2 * m * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4) * Δ)
      ≤ (((sz.size n : ℕ) : ℝ) ^ m)⁻¹ / 5 := by
    have := hE2 Δ hΔ0 hΔa
    calc 8 * (m : ℝ) * (2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4))
          * Real.sqrt (2 * m * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4) * Δ)
        = 16 * m * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)
          * Real.sqrt (2 * m * ((sz.size n : ℕ) : ℝ) ^ (2 * m + 4) * Δ) := by ring
      _ ≤ _ := this
  have hT3 : DuhamelC_epsY n0 (sz.size n) ≤ (((sz.size n : ℕ) : ℝ) ^ m)⁻¹ / 5 := hE3
  have hT4 := hE4 Δ (K n : ℝ) hΔ0 hK0 hKΔ
  have hT5 := hE5 Δ (K n : ℝ) hΔ0 hK0 hKΔ hΔa
  -- the prefactor and the bound
  have hT6 : 8 * (m : ℝ) * (2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) * sq * M
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (sq * M) := by
    have h := mul_le_mul_of_nonneg_right htau (mul_nonneg hsq0 hM0)
    calc 8 * (m : ℝ) * (2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) * sq * M
        = 16 * m * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * (sq * M) := by ring
      _ ≤ _ := h
  have hT7 : (((sz.size n : ℕ) : ℝ) ^ m)⁻¹
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n (k : ℕ)))⁻¹ ^ m := by
    have hηk := hη (k : ℕ) hkK
    have hSc : 0 < ((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n (k : ℕ)) := by
      rw [GUEDuhamelBA_etaOf_eq (E n)]
      exact mul_pos hN0 (lt_of_lt_of_le (by positivity) hηk.1)
    have hScN : ((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n (k : ℕ)) ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [GUEDuhamelBA_etaOf_eq (E n)]
      calc ((sz.size n : ℕ) : ℝ) * (ztOf (μ n) (E n) (gridTime t1 t0 K n (k : ℕ))).im
          ≤ ((sz.size n : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hηk.2 hN0.le
        _ = ((sz.size n : ℕ) : ℝ) := mul_one _
    have hinv : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n (k : ℕ)))⁻¹ :=
      inv_anti₀ hSc hScN
    have hpow : (((sz.size n : ℕ) : ℝ) ^ m)⁻¹
        ≤ (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n (k : ℕ)))⁻¹ ^ m := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hinv m
    have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow (hN1 n) hτ.le
    have h0 : 0 ≤ (((sz.size n : ℕ) : ℝ) * etaOf (μ n) (gridTime t1 t0 K n (k : ℕ)))⁻¹ ^ m :=
      pow_nonneg (inv_nonneg.2 hSc.le) m
    exact hpow.trans (le_mul_of_one_le_left h0 hNτ)
  rw [mul_add]
  linarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7]


end Main

/-! ## 9. The public statement `gueGrid_loop_duhamelBA` -/

section Public

/-- **`gueGrid_loop_duhamelBA`: the discrete Duhamel remainder of the loops on the BA grid** (the block Anderson version of
`gueGrid_loop_duhamel`).  For loops of length `1 ≤ ℓ ≤ 2 n₀`, uniformly in the grid step
`k ≤ K = gueGridK sz n₀ n` and the loop `(σ, a)`, along the BA grid path `gueHBA` (`g Ψ_I + H_k`) at the flow
`ztOf (m n) (E n)`:
`‖L_k - L_0 - Δ Σ_{j<k} 𝓖_GUE(u_j, H_j)‖ ≺ √(u_k - t₁) · max_{j<k} √(N⁻¹ η_{u_j}^{-2} L^{(2ℓ)}_j) + (N η_{u_k})^{-ℓ}`,
`N = sz.size n = (W L)^d`, `L^{(2ℓ)}_j = RBM.Ind.loopMax … (blockMat (gueHBA … j ω)) (ztOf (m n) (E n) u_j) (2ℓ)`: the
band `gueLmax` is by definition this expression at the band path `gueH` and flow `zt`, and it is written inline
here.  Unstopped, unconditional; the band hypothesis `|E n| ≤ 2 - κ` is replaced by `0 < Im m n` and `‖m n‖ ≤ 1` (for
block Anderson `m = m(E, ilambda₀)`, `BAReal`, `BAm_norm_le_one`), `hscale` is `(N η_{t₀})⁻¹ ≤ N^{-τ_U}` at `η = etaOf (m n)`.
`1 ≤ ℓ` is not used (as in the band). -/
theorem gueGrid_loop_duhamelBA {d : ℕ} (sz : Sizes d) {τU : ℝ} (hτU : 0 < τU) (n0 : ℕ)
    {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hm : ∀ n, 0 < (m n).im) (hm1 : ∀ n, ‖m n‖ ≤ 1) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (hscale : ∀ᶠ n in atTop,
      (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (ℓ : ℕ) (_hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 2 * n0) :
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × (Fin ℓ → Bool) × (Fin ℓ → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
              (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
              (gueHBA sz g t1 t0 (gueGridK sz n0) n 0 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 (gueGridK sz n0) n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
                (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω) (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => Real.sqrt (gridTime t1 t0 (gueGridK sz n0) n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
              (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω))
              (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * ℓ)))
        + (((sz.size n : ℕ) : ℝ) *
            etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹ ^ ℓ) :=
  GUEDuhamelBA_main (sz.withLam 0) (GUEDuhamelBA_Ash sz g) hτU n0 (gueGridK sz n0) (fun _ => rfl)
    (GUEDuhamelBA_Ash_isHermitian sz g) hsize hm hm1 ht1 ht10 ht0
    (fun n j hj I hwf => Duhamel_drift_remainder_aeBA sz g t1 t0 (gueGridK sz n0) n j (E n) (m n) (hm n) (hm1 n)
      hwf (ht1 n) (ht10 n) (ht0 n) hj)
    hscale ℓ hℓ

end Public

end RBM.BA


end
