/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.DuhamelA2
import RBM3D.Universality.GUEPhase.DuhamelB
import RBM3D.Universality.GUEPhase.Markov
import RBM3D.Universality.GUEPhase.Proc
import RBM3D.Induction.PerTimeCalc
import RBM3D.Green.Pins

/-!
# The loop Duhamel tail of the GUE phase, part III (`d ≥ 3`)

Ticket T2351 (UN-39/40, merged into one row, DECISIONS §159 (1)).  Port of RBM2D
`Universality/GUEPhase/DuhamelC.lean` (1521 lines, RBM2D commit `9e0f275`; cited `DC:<line>`): the
telescope of the pathwise one-step decomposition, the pathwise bound on the good event (dyadic
level choice, bias and remainder sums), the elementary eventual inequalities and the exponent
bounds, the four good events holding with high probability, and the main theorem
`gueGrid_loop_duhamel`.  It is written against the public declarations of `DuhamelA2`
(`Duhamel_norm_T_le`, `Duhamel_norm_B_le`, `Duhamel_drift_remainder_ae`, `DuhamelGood`) and of
`DuhamelB` (`DuhamelPhi`, `Duhamelv`, `DuhamelVp`, `DuhamelZinc`, `DuhamelZst`, `DuhamelYst`,
`Duhamelr`, `Duhamel_azuma_Z/Y`, `Duhamel_bddC2C_Phi`, `Duhamel_step_decomp`,
`Duhamel_exists_level`, `Duhamel_Vp_le`, `Duhamel_qv_le_crude`, `Duhamel_grid_facts`), on
`gue_highProb_incr_le` (`Markov.lean`) and `gueLmax` (`Proc.lean`).

## Main result

* `RBM.Univ.GUEPhase.gueGrid_loop_duhamel`: for loops of length `m ≤ 2 n₀`, uniformly in the grid
  step `k ≤ K = gueGridK sz n₀ n` and the loop `(σ, a)`,
  `‖L_k − L_0 − Δ Σ_{j<k} 𝓖_GUE(u_j, H_j)‖ ≺
    √(u_k − t₁) · max_{j<k} √(N⁻¹ η_{u_j}^{-2} L^{(2m)}_j) + (N η_{u_k})^{-m}`,
  `N = sz.size n = (W L)^d`.  The statement is unstopped and unconditional: the hypotheses are the
  data assumptions `hκ`, `hτU`, `hE`, `ht1`, `ht10`, `ht0`, then `hsize`, `hscale` and `m ≤ 2 n₀`.

## Renaming (as T2330, T2343, T2345, T2349)

`d : Sizes` is `sz : Sizes d`; `d.L n`, `d.W n`, `d.size n` are `sz.L n`, `sz.W n`, `sz.size n`
(`= (W L)^d`); `Idx L W` is `Idx d L W`; `Z2 L` is `Zd d L`; `BlockIndex L W` is `Vtx d L W`;
`gloop L W (blockMat M)` is `loopL d L W (blockMat d L W M)`; `spectralZ` is `zt`;
`RBM.Ind.loopMax L W` is `RBM.Ind.loopMax d L W`; `envConst L W` is `envConst d L W`;
`RBM.Path.etaT` is `RBM.Gauss.etaT`; `gueUnit d`, `Pgue d`, `PathΩ d`, `gueH d`, `gueScale d`,
`gueGridK d` are the same with `sz`.

## `d`-dependent lines

* The size `N = sz.size n = (W L)^d` enters the variance proxy, the dyadic levels, the Taylor and
  drift constants and the union over grid times only through `N`; the exponent bounds
  (`DuhamelC_num_*`) are the `d = 2` ones in `N`.
* The label count is `2^m (L^d)^m ≤ N^{2m}` (`L^d ≤ (W L)^d`; source `L·L ≤ (W L)²`,
  `DuhamelC_L_pow_le`); the card of `Zd d L` is `L^d` (`ZMod.card`, `Fintype.card_pi`).
* `Sizes d` does not carry `1 ≤ d`, so `2 ≤ N` is not available for every `n` (at `d = 0`,
  `N = 1`).  The only uses of `2 ≤ N` (`DuhamelC_card_le`, `DuhamelC_card_le'`, the union bound over
  the label set) are made eventually in `n`, from `hsize` (`DuhamelC_size_pos : 1 ≤ N` holds for
  every `n` and `d`).  No statement carries a `1 ≤ d` hypothesis.
* Compiled nonempty instances: namespace `RBM.Univ.GUEPhase.DuhamelCInst` (last section).

## The exponent bounds (`N = sz.size n`, `a₀ = 32 n₀ + 64`, `K = (N+1)^{a₀}`, `m = |I| ≤ 2 n₀`)

* `K Δ ≤ 1 ⇒ Δ ≤ N^{-a₀}`, `N Δ ≤ 1`;
* `32 m² Δ (N^{2m+2} + 2m N^{2m+4} Δ) < 2^N N^{-(40 n₀+80)}` (the top dyadic level exceeds every
  proxy);
* `2 N^{τ/4} √(K λ₀) ≤ N^{-m}/5`, `λ₀ = N^{-(40 n₀+80)}` (the dyadic floor);
* `16 m N^{τ/4} √(2m N^{2m+4} Δ) ≤ N^{-m}/5` (the shift term);
* `ε_Y = N^{-(2 n₀+2)} ≤ N^{-m}/5` and `16 K (b_T + λ₀)² ≤ ε_Y²/N` (the remainder martingale);
* `K ‖B‖ ≤ N^{-m}/5` (the truncation bias) and `K · envConst · Δ^{3/2} ≤ N^{-m}/5` (the drift
  remainder);
* the prefactor `16 m N^{τ/4} ≤ N^τ`.

Each holds eventually in `N` (`τ ≤ 1`; the reduction from `τ > 0` is by `min τ 1`).  The five
error terms sum to `N^{-m}`, and `N^{-m} ≤ N^τ (N η_{u_k})^{-m}` because `η ≤ 1`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.LinearForm RBM.Path
  RBM.Loop
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### 1. The pathwise assembly on the good event -/

section Pathwise

variable {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))}

/-- `etaT e u` is the imaginary part of the spectral parameter. -/
private theorem DuhamelC_etaT_eq (e u : ℝ) : etaT e u = (zt e u).im :=
  (zt_im e u).symm

/-- **Telescoping** the pathwise one-step decomposition. -/
private theorem DuhamelC_telescope (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) {ω : PathΩ sz}
    (htr : ∀ j < K n, ω (j + 1) ∈ DuhamelGood sz n) {k : ℕ} (hk : k ≤ K n) :
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω)) (zt e (gridTime t1 t0 K n k)) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
            (zt e (gridTime t1 t0 K n 0)) I
        - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
            genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) I
      = ∑ j ∈ Finset.range k, DuhamelZinc sz t1 t0 K n e I j ω
        + ∑ j ∈ Finset.range k, DuhamelYst sz t1 t0 K n e I (j + 1) ω
        - ∑ j ∈ Finset.range k, DuhamelB sz n (DuhamelPhi sz t1 t0 K n e I j)
            (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω)
        + ∑ j ∈ Finset.range k, Duhamelr sz t1 t0 K n e I j ω := by
  set L : ℕ → ℂ := fun j =>
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
      (zt e (gridTime t1 t0 K n j)) I with hL
  have htel : L k - L 0 = ∑ j ∈ Finset.range k, (L (j + 1) - L j) :=
    (Finset.sum_range_sub L k).symm
  have hstep : ∀ j ∈ Finset.range k, L (j + 1) - L j
      - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j)
          (gueH sz t1 t0 K n j ω) I
      = DuhamelZinc sz t1 t0 K n e I j ω + DuhamelYst sz t1 t0 K n e I (j + 1) ω
        - DuhamelB sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n)
            (gueH sz t1 t0 K n j ω)
        + Duhamelr sz t1 t0 K n e I j ω := by
    intro j hj
    have hjK : j < K n := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    exact Duhamel_step_decomp he hwf ht1 hst ht0 hjK ω (htr j hjK)
  change L k - L 0 - _ = _
  rw [htel, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hstep]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- `√(a+b) ≤ √a + √b`. -/
private theorem DuhamelC_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a)
      (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (by positivity)

end Pathwise

section Pathwise2

variable {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))}

/-- **The linear part on the good event**:
`L₀` is the number of dyadic levels, `x` the scale `x⁻¹ ≤ η_{t₀}`. -/
private theorem DuhamelC_Z_bound (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n) {lam0 : ℝ} (hlam0 : 0 < lam0)
    {x : ℝ} (hx1 : 1 ≤ x) (heta : x⁻¹ ≤ etaT e (t0 n))
    (hxΔ : x * gridStep t1 t0 K n ≤ 1) {L₀ : ℕ}
    (hQ : 32 * (I.length : ℝ) ^ 2 * gridStep t1 t0 K n * (x ^ (2 * I.length + 2)
      + 2 * I.length * x ^ (2 * I.length + 4) * gridStep t1 t0 K n) < 2 ^ L₀ * lam0)
    {c : ℝ} (hc : 0 ≤ c) {ω : PathΩ sz} {k : ℕ} (hk : k ≤ K n)
    (hZ : ∀ ℓ ≤ L₀, ‖∑ j ∈ Finset.range k,
        DuhamelZst sz t1 t0 K n e I (2 ^ ℓ * lam0) (j + 1) ω‖
      ≤ c * Real.sqrt (k * (2 ^ ℓ * lam0))) :
    ‖∑ j ∈ Finset.range k, DuhamelZinc sz t1 t0 K n e I j ω‖
      ≤ c * Real.sqrt (k * lam0)
        + 8 * I.length * c * Real.sqrt (gridTime t1 t0 K n k - t1 n)
          * (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ)) : ℝ)⁻¹
              * (etaT e (gridTime t1 t0 K n j))⁻¹ ^ 2
              * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
                  (zt e (gridTime t1 t0 K n j)) (2 * I.length)))
        + 8 * I.length * c * Real.sqrt (2 * I.length * x ^ (2 * I.length + 4)
            * gridStep t1 t0 K n) := by
  classical
  obtain ⟨hΔ0, hKΔ, hη, hzd, hmono, htk⟩ :=
    Duhamel_grid_facts (K := K) (n := n) he ht1 hst ht0 hK heta
  set m : ℕ := I.length with hm
  set S : ℝ := (((sz.size n : ℕ)) : ℝ) with hS
  set Δ := gridStep t1 t0 K n with hΔ
  have hx0 : 0 < x := by linarith
  have hΔx : Δ ≤ x⁻¹ := by
    calc Δ = x⁻¹ * (x * Δ) := by field_simp
      _ ≤ x⁻¹ * 1 := mul_le_mul_of_nonneg_left hxΔ (by positivity)
      _ = x⁻¹ := mul_one _
  set a : ℕ → ℝ := fun j => Real.sqrt (S⁻¹ * (etaT e (gridTime t1 t0 K n j))⁻¹ ^ 2
    * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt e (gridTime t1 t0 K n j)) (2 * m)) with ha
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
  have hηj : ∀ j < k, x⁻¹ ≤ (zt e (gridTime t1 t0 K n j)).im ∧
      (zt e (gridTime t1 t0 K n (j + 1))).im ≥ x⁻¹ ∧
        (zt e (gridTime t1 t0 K n (j + 1))).im ≤ 1 :=
    fun j hj => ⟨(hη j (le_of_lt (hkK j hj))).1, (hη (j + 1) (hkK j hj)).1,
      (hη (j + 1) (hkK j hj)).2⟩
  have hinvx : ∀ {y : ℝ}, x⁻¹ ≤ y → y⁻¹ ≤ x := fun {y} hy => by
    have hy0 : 0 < y := lt_of_lt_of_le (inv_pos.2 hx0) hy
    rw [inv_le_comm₀ hy0 hx0]; exact hy
  -- `a j ≤ M_k` and `a j ≤ x^{m+1}`
  have haM : ∀ j < k, a j ≤ Mk := fun j hj =>
    le_ciSup (f := fun j : Fin k => a j) (Set.finite_range _).bddAbove ⟨j, hj⟩
  have hsqa : ∀ j < k, a j ^ 2 = S⁻¹ * (etaT e (gridTime t1 t0 K n j))⁻¹ ^ 2
      * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
          (zt e (gridTime t1 t0 K n j)) (2 * m) := by
    intro j hj
    rw [ha]; dsimp only
    rw [Real.sq_sqrt]
    have : 0 ≤ RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt e (gridTime t1 t0 K n j)) (2 * m) := RBM.Ind.loopMax_nonneg _
    positivity
  have haX : ∀ j < k, a j ≤ x ^ (m + 1) := by
    intro j hj
    have hpos : 0 < (zt e (gridTime t1 t0 K n j)).im :=
      lt_of_lt_of_le (inv_pos.2 hx0) (hηj j hj).1
    have hc' := Duhamel_qv_le_crude (sz := sz) (n := n) (gueH_isHermitian sz t1 t0 K n j ω) hpos
      (2 * m)
    rw [← DuhamelC_etaT_eq] at hc'
    have h1 : (etaT e (gridTime t1 t0 K n j))⁻¹ ≤ x := by
      rw [DuhamelC_etaT_eq]; exact hinvx (hηj j hj).1
    have h2 : (etaT e (gridTime t1 t0 K n j))⁻¹ ^ (2 * m + 2) ≤ x ^ (2 * m + 2) :=
      pow_le_pow_left₀ (by rw [DuhamelC_etaT_eq]; positivity) h1 _
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
  have hVQ : ∀ j < k, DuhamelVp sz t1 t0 K n e I j ω ≤ Q := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hηj j hj
    have hz'pos : 0 < (zt e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (inv_pos.2 hx0) h2
    have hz2 : (zt e (gridTime t1 t0 K n j)).im
        ≤ 2 * (zt e (gridTime t1 t0 K n (j + 1))).im := by
      have := (hmono j).2
      have hΔle : Δ ≤ (zt e (gridTime t1 t0 K n (j + 1))).im := le_trans hΔx h2
      linarith
    have hV := Duhamel_Vp_le (gueH_isHermitian sz t1 t0 K n j ω) hz'pos (hmono j).1 hz2 h3 hΔ0
      (le_of_eq (hzd j)) hwf
    have hVeq : DuhamelVp sz t1 t0 K n e I j ω
        = Δ / S * max (vGue sz n (gradMat (fun M' => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M')
            (zt e (gridTime t1 t0 K n (j + 1))) I) (gueH sz t1 t0 K n j ω)) : ℝ)
          (vGue sz n (-Complex.I • gradMat (fun M' => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M')
            (zt e (gridTime t1 t0 K n (j + 1))) I) (gueH sz t1 t0 K n j ω)) : ℝ) := rfl
    rw [hVeq]
    refine hV.trans ?_
    have hinv' : ((zt e (gridTime t1 t0 K n (j + 1))).im)⁻¹ ^ (2 * m + 4)
        ≤ x ^ (2 * m + 4) :=
      pow_le_pow_left₀ (by positivity) (hinvx h2) _
    have ha2 : S⁻¹ * ((zt e (gridTime t1 t0 K n j)).im)⁻¹ ^ 2
        * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
            (zt e (gridTime t1 t0 K n j)) (2 * m)
        ≤ Mk ^ 2 := by
      rw [← DuhamelC_etaT_eq, ← hsqa j hj]
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
  obtain ⟨ℓ, hℓN, hσ, hlam⟩ := Duhamel_exists_level (J := DuhamelVp sz t1 t0 K n e I)
    (K' := K n) (L₀ := L₀) (ω := ω) hlam0 hQ0 hQlt hk hVQ
  -- the stopped sum is the full sum
  have hfull : ∑ j ∈ Finset.range k, DuhamelZst sz t1 t0 K n e I (2 ^ ℓ * lam0) (j + 1) ω
      = ∑ j ∈ Finset.range k, DuhamelZinc sz t1 t0 K n e I j ω := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjs : j < firstHit (DuhamelVp sz t1 t0 K n e I) (2 ^ ℓ * lam0) (K n) ω :=
      lt_of_lt_of_le (Finset.mem_range.1 hj) hσ
    simp only [DuhamelZst]
    rw [Set.indicator_of_mem (show ω ∈ {ω | j < firstHit (DuhamelVp sz t1 t0 K n e I)
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

variable {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))}

/-- **The pathwise bound on the good event**, at the scale `x = N = sz.size n` and with `sz.size n`
dyadic levels. -/
private theorem DuhamelC_pathwise (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n) {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (heta : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaT e (t0 n))
    (hNΔ : ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1)
    (hQ : 32 * (I.length : ℝ) ^ 2 * gridStep t1 t0 K n
      * (((sz.size n : ℕ) : ℝ) ^ (2 * I.length + 2)
        + 2 * I.length * ((sz.size n : ℕ) : ℝ) ^ (2 * I.length + 4) * gridStep t1 t0 K n)
        < 2 ^ (sz.size n) * lam0)
    {c epsY : ℝ} (hc : 0 ≤ c) {ω : PathΩ sz}
    (htr : ∀ j < K n, ω (j + 1) ∈ DuhamelGood sz n)
    (hr : ∀ j < K n, ‖Duhamelr sz t1 t0 K n e I j ω‖
      ≤ envConst d (sz.L n) (sz.W n) e I.length (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2))
    {k : ℕ} (hk : k ≤ K n)
    (hZ : ∀ ℓ ≤ sz.size n, ‖∑ j ∈ Finset.range k,
        DuhamelZst sz t1 t0 K n e I (2 ^ ℓ * lam0) (j + 1) ω‖
      ≤ c * Real.sqrt (k * (2 ^ ℓ * lam0)))
    (hY : ‖∑ j ∈ Finset.range k, DuhamelYst sz t1 t0 K n e I (j + 1) ω‖ ≤ epsY) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
          (zt e (gridTime t1 t0 K n k)) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
            (zt e (gridTime t1 t0 K n 0)) I
        - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
            genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) I‖
      ≤ c * Real.sqrt (k * lam0)
        + 8 * I.length * c * Real.sqrt (gridTime t1 t0 K n k - t1 n)
          * (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ)) : ℝ)⁻¹
              * (etaT e (gridTime t1 t0 K n j))⁻¹ ^ 2
              * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
                  (zt e (gridTime t1 t0 K n j)) (2 * I.length)))
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
    Duhamel_grid_facts (K := K) (n := n) he ht1 hst ht0 hK heta
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  rw [DuhamelC_telescope he hwf ht1 hst ht0 htr hk]
  have hZb := DuhamelC_Z_bound (I := I) he hwf ht1 hst ht0 hK hlam0 hN1 heta hNΔ hQ hc hk hZ
  have hkK : (k : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hk
  have hinvN : ∀ j < K n, ((zt e (gridTime t1 t0 K n (j + 1))).im)⁻¹ ≤ N := by
    intro j hj
    have h := (hη (j + 1) hj).1
    have hpos : 0 < (zt e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (by positivity) h
    rw [inv_le_comm₀ hpos hN0]; exact h
  -- the bias sum
  set EBt : ℝ := 16 * Real.exp 2 * ((I.length : ℝ) * ((I.length : ℝ) + 1) * N * N ^ (I.length + 2))
      * (gridStep t1 t0 K n / N) * N ^ 4 * Real.exp (-N / 4) with hEBt
  have hv0 : 0 ≤ Duhamelv sz t1 t0 K n := div_nonneg hΔ0 (Nat.cast_nonneg _)
  have hB : ∀ j ∈ Finset.range k, ‖DuhamelB sz n (DuhamelPhi sz t1 t0 K n e I j)
      (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω)‖ ≤ EBt := by
    intro j hj
    have hjK : j < K n := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    obtain ⟨hz, hΦ, hC₂⟩ := Duhamel_bddC2C_Phi (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
      (e := e) (I := I) he hwf ht1 hst ht0 hjK
    refine (Duhamel_norm_B_le hΦ hC₂ hv0 (gueH_isHermitian sz t1 t0 K n j ω)).trans ?_
    rw [hEBt]
    have hpos : 0 < (zt e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (by positivity) (hη (j + 1) hjK).1
    have hinv : (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ≤ N := by
      rw [DuhamelC_etaT_eq]; exact hinvN j hjK
    have hetapos : 0 < etaT e (gridTime t1 t0 K n (j + 1)) := by
      rw [DuhamelC_etaT_eq]; exact hpos
    have hcast : ((I.length * (I.length + 1) : ℕ) : ℝ) = (I.length : ℝ) * ((I.length : ℝ) + 1) := by
      push_cast; ring
    have hC2 : ((I.length * (I.length + 1) : ℕ) : ℝ) * N
        * (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2)
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
  have hBsum : ‖∑ j ∈ Finset.range k, DuhamelB sz n (DuhamelPhi sz t1 t0 K n e I j)
      (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω)‖ ≤ (K n : ℝ) * EBt := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hB).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hkK hEBt0
  -- the D3 remainder sum
  set ERt : ℝ := 16 * ((I.length : ℝ) + 3) ^ 4 * N ^ 4 * (1 + N) ^ (I.length + 4)
      * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) with hERt
  have hr' : ∀ j ∈ Finset.range k, ‖Duhamelr sz t1 t0 K n e I j ω‖ ≤ ERt := by
    intro j hj
    have hjK : j < K n := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    refine (hr j hjK).trans ?_
    rw [hERt]
    have hpos : 0 < (zt e (gridTime t1 t0 K n (j + 1))).im :=
      lt_of_lt_of_le (by positivity) (hη (j + 1) hjK).1
    have hinv : (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ≤ N := by
      rw [DuhamelC_etaT_eq]; exact hinvN j hjK
    have hetapos : 0 < etaT e (gridTime t1 t0 K n (j + 1)) := by
      rw [DuhamelC_etaT_eq]; exact hpos
    have h1 : (1 + (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹) ^ (I.length + 4)
        ≤ (1 + N) ^ (I.length + 4) := by
      have : 0 ≤ 1 + (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ := by positivity
      gcongr
    have h2 : 0 ≤ gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ0 _
    have hmat : envConst d (sz.L n) (sz.W n) e I.length (gridTime t1 t0 K n (j + 1))
        = 16 * ((I.length : ℝ) + 3) ^ 4 * N ^ 4
          * (1 + (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹) ^ (I.length + 4) := rfl
    rw [hmat]
    have h3 : 0 ≤ 16 * ((I.length : ℝ) + 3) ^ 4 * N ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2
  have hERt0 : 0 ≤ ERt := by
    rw [hERt]
    have := Real.rpow_nonneg hΔ0 ((3 : ℝ) / 2)
    positivity
  have hrsum : ‖∑ j ∈ Finset.range k, Duhamelr sz t1 t0 K n e I j ω‖ ≤ (K n : ℝ) * ERt := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hr').trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hkK hERt0
  -- combine
  set SZ := ∑ j ∈ Finset.range k, DuhamelZinc sz t1 t0 K n e I j ω
  set SY := ∑ j ∈ Finset.range k, DuhamelYst sz t1 t0 K n e I (j + 1) ω
  set SB := ∑ j ∈ Finset.range k, DuhamelB sz n (DuhamelPhi sz t1 t0 K n e I j)
      (Duhamelv sz t1 t0 K n) (gueH sz t1 t0 K n j ω)
  set SR := ∑ j ∈ Finset.range k, Duhamelr sz t1 t0 K n e I j ω
  have htri : ‖SZ + SY - SB + SR‖ ≤ ‖SZ‖ + ‖SY‖ + ‖SB‖ + ‖SR‖ := by
    calc ‖SZ + SY - SB + SR‖ ≤ ‖SZ + SY - SB‖ + ‖SR‖ := norm_add_le _ _
      _ ≤ ‖SZ + SY‖ + ‖SB‖ + ‖SR‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖SZ‖ + ‖SY‖ + ‖SB‖ + ‖SR‖ := by gcongr; exact norm_add_le _ _
  refine htri.trans ?_
  linarith

end Pathwise3

/-! ### 2. Elementary eventual inequalities -/

section Eventually

/-- `C N^A e^{-c N^{τ₁}} ≤ 1` eventually in the real variable `N` (the Gaussian tail beats every
power). -/
private theorem DuhamelC_ev_exp_small_real (C A c : ℝ) {τ₁ : ℝ} (hc : 0 < c) (hτ₁ : 0 < τ₁) :
    ∀ᶠ N : ℝ in atTop, C * N ^ A * Real.exp (-(c * N ^ τ₁)) ≤ 1 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / τ₁) c hc
  have hg : Tendsto (fun N : ℝ => N ^ τ₁) atTop atTop := tendsto_rpow_atTop hτ₁
  have h2 := h.comp hg
  have hpos : (0 : ℝ) < (|C| + 1)⁻¹ := by positivity
  filter_upwards [h2.eventually (gt_mem_nhds hpos), eventually_gt_atTop (0 : ℝ)] with N hN hN0
  simp only [Function.comp_apply] at hN
  have e : (N ^ τ₁) ^ (A / τ₁) = N ^ A := by
    rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  rw [e] at hN
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have hx : 0 ≤ N ^ A * Real.exp (-(c * N ^ τ₁)) := by positivity
  have hN' : N ^ A * Real.exp (-c * N ^ τ₁) < (|C| + 1)⁻¹ := hN
  rw [neg_mul] at hN'
  calc C * N ^ A * Real.exp (-(c * N ^ τ₁))
      = C * (N ^ A * Real.exp (-(c * N ^ τ₁))) := by ring
    _ ≤ (|C| + 1) * (N ^ A * Real.exp (-(c * N ^ τ₁))) := mul_le_mul_of_nonneg_right hC hx
    _ ≤ (|C| + 1) * (|C| + 1)⁻¹ := mul_le_mul_of_nonneg_left hN'.le (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

private theorem DuhamelC_ev_exp_small (C A c : ℝ) {τ₁ : ℝ} (hc : 0 < c) (hτ₁ : 0 < τ₁) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ A * Real.exp (-(c * (N : ℝ) ^ τ₁)) ≤ 1 :=
  tendsto_natCast_atTop_atTop.eventually (DuhamelC_ev_exp_small_real C A c hc hτ₁)

/-- `C N^a ≤ N^b` eventually, `a < b`. -/
private theorem DuhamelC_ev_poly (C : ℝ) {a b : ℕ} (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  filter_upwards [eventually_ge_atTop (⌈|C|⌉₊ + 1)] with N hN
  have hC : C ≤ (N : ℝ) := by
    have h1 : (⌈|C|⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : |C| ≤ (⌈|C|⌉₊ : ℝ) := Nat.le_ceil _
    linarith [le_abs_self C]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (⌈|C|⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) ≤ ⌈|C|⌉₊ := Nat.cast_nonneg _
    linarith
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hC (by positivity)
    _ = (N : ℝ) ^ (a + 1) := by ring
    _ ≤ (N : ℝ) ^ b := pow_le_pow_right₀ hN1 hab

/-- `C N^a e^{-cN} ≤ 1` eventually. -/
private theorem DuhamelC_ev_exp (C : ℝ) (a : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a * Real.exp (-(c * (N : ℝ))) ≤ 1 := by
  have h := DuhamelC_ev_exp_small C (a : ℝ) c hc one_pos
  filter_upwards [h] with N hN
  simp only [Real.rpow_natCast, Real.rpow_one] at hN
  exact hN

/-- `N^a ≤ 2^N` eventually. -/
private theorem DuhamelC_ev_two_pow (a : ℕ) : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ 2 ^ N := by
  have h := DuhamelC_ev_exp 1 a (c := Real.log 2) (Real.log_pos one_lt_two)
  filter_upwards [h] with N hN
  have e : Real.exp (-(Real.log 2 * (N : ℝ))) = ((2 : ℝ) ^ N)⁻¹ := by
    rw [Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log two_pos]
  rw [e, one_mul] at hN
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rwa [mul_inv_le_iff₀ h2, one_mul] at hN

/-- `4 e^{-N^a} ≤ N^{-D}`. -/
private theorem DuhamelC_ev_exp_rpow {a : ℝ} (ha : 0 < a) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 * Real.exp (-(N : ℝ) ^ a) ≤ (N : ℝ) ^ (-D) := by
  have h := DuhamelC_ev_exp_small 4 D 1 (τ₁ := a) one_pos ha
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [one_mul] at hN
  have hD : (0 : ℝ) < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 D
  rw [Real.rpow_neg hN0.le, inv_eq_one_div, le_div_iff₀ hD]
  have e : 4 * Real.exp (-(N : ℝ) ^ a) * (N : ℝ) ^ D
      = 4 * (N : ℝ) ^ D * Real.exp (-(N : ℝ) ^ a) := by ring
  rw [e]
  simpa using hN

/-- `4 e^{-N} ≤ N^{-D}`. -/
private theorem DuhamelC_ev_exp_lin (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 * Real.exp (-(N : ℝ)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [DuhamelC_ev_exp_rpow one_pos D] with N hN
  simpa using hN

end Eventually

/-! ### 3. The exponent bookkeeping -/

section Numeric

/-- `c C x^p ≤ x^m` gives `C (x^m)⁻¹ ≤ (x^p)⁻¹ / c`. -/
private theorem DuhamelC_le_inv_div {x C c : ℝ} (hx : 0 < x) (hc : 0 < c) {m p : ℕ}
    (h : c * C * x ^ p ≤ x ^ m) : C * (x ^ m)⁻¹ ≤ (x ^ p)⁻¹ / c := by
  have hm : 0 < x ^ m := by positivity
  have hp : 0 < x ^ p := by positivity
  rw [show C * (x ^ m)⁻¹ = C / x ^ m by ring, show (x ^ p)⁻¹ / c = 1 / (c * x ^ p) by
    field_simp, div_le_div_iff₀ hm (by positivity)]
  linarith

/-- The step size: `Δ ≤ N^{-(32n₀+64)}` and `NΔ ≤ 1`. -/
private theorem DuhamelC_num_step (n0 : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ →
    ((N : ℝ) + 1) ^ (32 * n0 + 64) * Δ ≤ 1 →
      Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ ∧ (N : ℝ) * Δ ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with N hN Δ hΔ hKΔ
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxa : (N : ℝ) ^ (32 * n0 + 64) ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpos : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
  have h1 : Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by
    rw [← one_div, le_div_iff₀ hpos]; nlinarith
  refine ⟨h1, ?_⟩
  have h2 : (N : ℝ) ≤ (N : ℝ) ^ (32 * n0 + 64) := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hx (by omega)
  nlinarith

/-- The top dyadic level exceeds every proxy. -/
private theorem DuhamelC_num_Q {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ →
      32 * (n : ℝ) ^ 2 * Δ * ((N : ℝ) ^ (2 * n + 2) + 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
        < 2 ^ N * ((N : ℝ) ^ (40 * n0 + 80))⁻¹ := by
  filter_upwards [DuhamelC_ev_poly (32 * (n : ℝ) ^ 2 * (1 + 2 * n)) (a := 2 * n + 4)
      (b := 32 * n0 + 64) (by omega), DuhamelC_ev_two_pow (40 * n0 + 81),
      eventually_ge_atTop 2]
    with N h1 h2 hN Δ hΔ hΔa
  have hx : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : (1 : ℝ) ≤ N := by linarith
  have hpos : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
  have hΔ1 : Δ ≤ 1 := hΔa.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hx1))
  have hin : (N : ℝ) ^ (2 * n + 2) + 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ
      ≤ (1 + 2 * n) * (N : ℝ) ^ (2 * n + 4) := by
    have : (N : ℝ) ^ (2 * n + 2) ≤ (N : ℝ) ^ (2 * n + 4) := pow_le_pow_right₀ hx1 (by omega)
    have : 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ ≤ 2 * n * (N : ℝ) ^ (2 * n + 4) := by
      have h0 : 0 ≤ 2 * (n : ℝ) * (N : ℝ) ^ (2 * n + 4) := by positivity
      nlinarith
    linarith
  have hL : 32 * (n : ℝ) ^ 2 * Δ * ((N : ℝ) ^ (2 * n + 2) + 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
      ≤ 1 := by
    calc _ ≤ 32 * (n : ℝ) ^ 2 * Δ * ((1 + 2 * n) * (N : ℝ) ^ (2 * n + 4)) := by gcongr
      _ = Δ * (32 * (n : ℝ) ^ 2 * (1 + 2 * n) * (N : ℝ) ^ (2 * n + 4)) := by ring
      _ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ * (N : ℝ) ^ (32 * n0 + 64) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hR : 1 < 2 ^ N * ((N : ℝ) ^ (40 * n0 + 80))⁻¹ := by
    have hp : 0 < (N : ℝ) ^ (40 * n0 + 80) := by positivity
    rw [← div_eq_mul_inv, lt_div_iff₀ hp, one_mul]
    calc (N : ℝ) ^ (40 * n0 + 80) < (N : ℝ) ^ (40 * n0 + 81) :=
          pow_lt_pow_right₀ (by linarith) (by omega)
      _ ≤ 2 ^ N := h2
  linarith

/-- `x ^ (τ / 4) ≤ x` for `x ≥ 1`, `τ ≤ 1`. -/
private theorem DuhamelC_rpow_quarter_le {x τ : ℝ} (hx : 1 ≤ x) (hτ1 : τ ≤ 1) :
    x ^ (τ / 4) ≤ x := by
  calc x ^ (τ / 4) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = x := Real.rpow_one x

/-- `(x + 1) ^ a ≤ 2 ^ a * x ^ a` for `x ≥ 1`. -/
private theorem DuhamelC_one_add_pow_le {x : ℝ} (hx : 1 ≤ x) (a : ℕ) :
    (x + 1) ^ a ≤ 2 ^ a * x ^ a := by
  rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) a

/-- The dyadic floor. -/
private theorem DuhamelC_num_E1 {n0 n : ℕ} (hn : n ≤ 2 * n0) {τ : ℝ} (hτ1 : τ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (τ / 4)
      * Real.sqrt (((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) ^ (40 * n0 + 80))⁻¹)
        ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [DuhamelC_ev_poly ((2 : ℝ) ^ (32 * n0 + 64)) (a := 40 * n0 + 78)
      (b := 40 * n0 + 80) (by omega), DuhamelC_ev_poly 10 (a := n + 1) (b := 4 * n0 + 7)
      (by omega), eventually_ge_atTop 1] with N h1 h2 hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hq := DuhamelC_rpow_quarter_le hx hτ1
  have hsq : Real.sqrt (((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) ^ (40 * n0 + 80))⁻¹)
      ≤ ((N : ℝ) ^ (4 * n0 + 7))⁻¹ := by
    rw [Real.sqrt_le_left (by positivity)]
    have hb := DuhamelC_one_add_pow_le hx (32 * n0 + 64)
    have hp1 : 0 < (N : ℝ) ^ (40 * n0 + 80) := by positivity
    rw [inv_pow, ← pow_mul, ← div_eq_mul_inv, div_le_iff₀ hp1, ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    calc ((N : ℝ) + 1) ^ (32 * n0 + 64) * (N : ℝ) ^ ((4 * n0 + 7) * 2)
        ≤ 2 ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64) * (N : ℝ) ^ ((4 * n0 + 7) * 2) := by
          gcongr
      _ = 2 ^ (32 * n0 + 64) * (N : ℝ) ^ (40 * n0 + 78) := by
          rw [mul_assoc, ← pow_add]; ring_nf
      _ ≤ (N : ℝ) ^ (40 * n0 + 80) := h1
  have hstep : 2 * (N : ℝ) * ((N : ℝ) ^ (4 * n0 + 7))⁻¹ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
    refine DuhamelC_le_inv_div hx0 (by norm_num) ?_
    calc 5 * (2 * (N : ℝ)) * (N : ℝ) ^ n = 10 * (N : ℝ) ^ (n + 1) := by ring
      _ ≤ _ := h2
  calc 2 * (N : ℝ) ^ (τ / 4)
        * Real.sqrt (((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) ^ (40 * n0 + 80))⁻¹)
      ≤ 2 * (N : ℝ) * ((N : ℝ) ^ (4 * n0 + 7))⁻¹ := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 4) := Real.rpow_nonneg hx0.le _
        gcongr
    _ ≤ _ := hstep

/-- The shift term. -/
private theorem DuhamelC_num_E2 {n0 n : ℕ} (hn : n ≤ 2 * n0) {τ : ℝ} (hτ1 : τ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ →
      16 * n * (N : ℝ) ^ (τ / 4) * Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
        ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [DuhamelC_ev_poly (2 * (n : ℝ)) (a := 8 * n0 + 10) (b := 32 * n0 + 64)
      (by omega), DuhamelC_ev_poly (80 * (n : ℝ)) (a := n + 1) (b := 2 * n0 + 3) (by omega),
      eventually_ge_atTop 1] with N h1 h2 hN Δ hΔ hΔa
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hq := DuhamelC_rpow_quarter_le hx hτ1
  have hsq : Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ) ≤ ((N : ℝ) ^ (2 * n0 + 3))⁻¹ := by
    rw [Real.sqrt_le_left (by positivity)]
    have hpa : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
    have hpow : (N : ℝ) ^ (2 * n + 4) * (N : ℝ) ^ ((2 * n0 + 3) * 2)
        ≤ (N : ℝ) ^ (8 * n0 + 10) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hx (by omega)
    rw [inv_pow, ← pow_mul]
    calc 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ
        ≤ 2 * n * (N : ℝ) ^ (2 * n + 4) * ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by gcongr
      _ ≤ ((N : ℝ) ^ ((2 * n0 + 3) * 2))⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hpa, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
          calc 2 * n * (N : ℝ) ^ (2 * n + 4) * (N : ℝ) ^ ((2 * n0 + 3) * 2)
              = 2 * n * ((N : ℝ) ^ (2 * n + 4) * (N : ℝ) ^ ((2 * n0 + 3) * 2)) := by ring
            _ ≤ 2 * n * (N : ℝ) ^ (8 * n0 + 10) := by gcongr
            _ ≤ _ := h1
  have hstep : 16 * n * (N : ℝ) * ((N : ℝ) ^ (2 * n0 + 3))⁻¹ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
    refine DuhamelC_le_inv_div hx0 (by norm_num) ?_
    calc 5 * (16 * n * (N : ℝ)) * (N : ℝ) ^ n = 80 * n * (N : ℝ) ^ (n + 1) := by ring
      _ ≤ _ := h2
  calc 16 * n * (N : ℝ) ^ (τ / 4) * Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
      ≤ 16 * n * (N : ℝ) * ((N : ℝ) ^ (2 * n0 + 3))⁻¹ := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 4) := Real.rpow_nonneg hx0.le _
        gcongr
    _ ≤ _ := hstep

/-- The truncation level of `Ỹ`. -/
private theorem DuhamelC_num_E3 {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) ^ (2 * n0 + 2))⁻¹ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [DuhamelC_ev_poly 5 (a := n) (b := 2 * n0 + 2) (by omega),
    eventually_ge_atTop 1] with N h1 hN
  have hx0 : (0 : ℝ) < N := by exact_mod_cast hN
  have := DuhamelC_le_inv_div (C := 1) hx0 (by norm_num : (0 : ℝ) < 5) (m := 2 * n0 + 2)
    (p := n) (by linarith)
  simpa using this

/-- The truncation bias: `K ‖B‖ ≤ (KΔ) 16 e² n(n+1) N^{n+6} e^{-N/4}`, with
`C₂ = n (n+1) N η^{-(n+2)} ≤ n (n+1) N^{n+3}`, `v = Δ/N`. -/
private theorem DuhamelC_num_E4 {n : ℕ} :
    ∀ᶠ N : ℕ in atTop, ∀ Δ K : ℝ, 0 ≤ Δ → 0 ≤ K → K * Δ ≤ 1 →
      K * (16 * Real.exp 2 * (((n : ℝ) * ((n : ℝ) + 1)) * (N : ℝ) * (N : ℝ) ^ (n + 2))
        * (Δ / (N : ℝ)) * (N : ℝ) ^ 4 * Real.exp (-(N : ℝ) / 4)) ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [DuhamelC_ev_exp (80 * Real.exp 2 * ((n : ℝ) * ((n : ℝ) + 1))) (2 * n + 6)
      (c := 1 / 4) (by norm_num), eventually_ge_atTop 1] with N h1 hN Δ K hΔ hK hKΔ
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hE : Real.exp (-(N : ℝ) / 4) = Real.exp (-(1 / 4 * (N : ℝ))) := by ring_nf
  have heq : K * (16 * Real.exp 2 * (((n : ℝ) * ((n : ℝ) + 1)) * (N : ℝ) * (N : ℝ) ^ (n + 2))
        * (Δ / (N : ℝ)) * (N : ℝ) ^ 4 * Real.exp (-(N : ℝ) / 4))
      = (K * Δ) * (16 * Real.exp 2 * ((n : ℝ) * ((n : ℝ) + 1)) * (N : ℝ) ^ (n + 6)
        * Real.exp (-(N : ℝ) / 4)) := by
    field_simp
    ring
  rw [heq]
  have h0 : 0 ≤ 16 * Real.exp 2 * ((n : ℝ) * ((n : ℝ) + 1)) * (N : ℝ) ^ (n + 6)
      * Real.exp (-(N : ℝ) / 4) := by positivity
  calc (K * Δ) * (16 * Real.exp 2 * ((n : ℝ) * ((n : ℝ) + 1)) * (N : ℝ) ^ (n + 6)
        * Real.exp (-(N : ℝ) / 4))
      ≤ 1 * (16 * Real.exp 2 * ((n : ℝ) * ((n : ℝ) + 1)) * (N : ℝ) ^ (n + 6)
        * Real.exp (-(N : ℝ) / 4)) := by gcongr
    _ = (80 * Real.exp 2 * ((n : ℝ) * ((n : ℝ) + 1)) * (N : ℝ) ^ (2 * n + 6)
          * Real.exp (-(1 / 4 * (N : ℝ)))) * ((N : ℝ) ^ n)⁻¹ / 5 := by
        rw [hE]
        have hpn : (N : ℝ) ^ n ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ 1 * ((N : ℝ) ^ n)⁻¹ / 5 := by
        have : 0 ≤ ((N : ℝ) ^ n)⁻¹ := by positivity
        gcongr
    _ = _ := by ring

/-- The drift remainder: `K 16 (n+3)⁴ N⁴ (1+N)^{n+4} Δ^{3/2} ≤ N^{-n}/5`. -/
private theorem DuhamelC_num_E5 {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ K : ℝ, 0 ≤ Δ → 0 ≤ K → K * Δ ≤ 1 →
      Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ →
      K * (16 * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ 4 * (1 + (N : ℝ)) ^ (n + 4)
          * Δ ^ ((3 : ℝ) / 2)) ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [DuhamelC_ev_poly (80 * (2 : ℝ) ^ (n + 4) * ((n : ℝ) + 3) ^ 4) (a := 2 * n + 8)
      (b := 16 * n0 + 32) (by omega), eventually_ge_atTop 1] with N h1 hN Δ K hΔ hK hKΔ hΔa
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hsqrt : Δ ^ ((3 : ℝ) / 2) = Δ * Real.sqrt Δ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hΔ (by norm_num)]; norm_num
  have hsΔ : Real.sqrt Δ ≤ ((N : ℝ) ^ (16 * n0 + 32))⁻¹ := by
    rw [Real.sqrt_le_left (by positivity), inv_pow, ← pow_mul]
    exact hΔa.trans (le_of_eq (by ring_nf))
  have h1N : (1 + (N : ℝ)) ^ (n + 4) ≤ 2 ^ (n + 4) * (N : ℝ) ^ (n + 4) := by
    rw [add_comm]; exact DuhamelC_one_add_pow_le hx _
  rw [hsqrt]
  have heq : K * (16 * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ 4 * (1 + (N : ℝ)) ^ (n + 4)
        * (Δ * Real.sqrt Δ))
      = (K * Δ) * (16 * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ 4 * (1 + (N : ℝ)) ^ (n + 4)
        * Real.sqrt Δ) := by ring
  rw [heq]
  calc (K * Δ) * (16 * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ 4 * (1 + (N : ℝ)) ^ (n + 4)
        * Real.sqrt Δ)
      ≤ 1 * (16 * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ 4 * (2 ^ (n + 4) * (N : ℝ) ^ (n + 4))
          * ((N : ℝ) ^ (16 * n0 + 32))⁻¹) := by
        have : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
        gcongr
    _ = (16 * (2 : ℝ) ^ (n + 4) * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ (n + 8))
          * ((N : ℝ) ^ (16 * n0 + 32))⁻¹ := by
        rw [one_mul, show n + 8 = 4 + (n + 4) by ring, pow_add]
        ring
    _ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
        refine DuhamelC_le_inv_div hx0 (by norm_num) ?_
        calc 5 * (16 * (2 : ℝ) ^ (n + 4) * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ (n + 8)) * (N : ℝ) ^ n
            = 80 * (2 : ℝ) ^ (n + 4) * ((n : ℝ) + 3) ^ 4 * (N : ℝ) ^ (2 * n + 8) := by
              rw [show 2 * n + 8 = (n + 8) + n by ring, pow_add]; ring
          _ ≤ _ := h1

/-- The Hoeffding proxy of `Ỹ` is tiny against the level `N^{-2n₀-2}`.  Here `b = b_T + λ₀`,
`b_T = n(n+1)/2 · N^{n+6} Δ` (`C₂/2 · v · N⁴`,
`C₂ ≤ n(n+1) N^{n+3}`). -/
private theorem DuhamelC_num_Y {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ K : ℝ, 0 ≤ Δ → 0 ≤ K → K * Δ ≤ 1 →
      Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ → K ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) →
      16 * K * (((n * (n + 1) : ℕ) : ℝ) / 2 * (N : ℝ) ^ (n + 6) * Δ
          + ((N : ℝ) ^ (40 * n0 + 80))⁻¹) ^ 2
        ≤ (((N : ℝ) ^ (2 * n0 + 2))⁻¹) ^ 2 / N := by
  filter_upwards [DuhamelC_ev_poly (64 * (((n * (n + 1) : ℕ) : ℝ) / 2) ^ 2) (a := 2 * n + 4 * n0 + 17)
      (b := 32 * n0 + 64) (by omega),
      DuhamelC_ev_poly (64 * (2 : ℝ) ^ (32 * n0 + 64)) (a := 36 * n0 + 69) (b := 80 * n0 + 160)
        (by omega), eventually_ge_atTop 1] with N h1 h2 hN Δ K hΔ hK hKΔ hΔa hKa
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  set bT := ((n * (n + 1) : ℕ) : ℝ) / 2 * (N : ℝ) ^ (n + 6) * Δ with hbT
  set l0 := ((N : ℝ) ^ (40 * n0 + 80))⁻¹ with hl0
  have hbT0 : 0 ≤ bT := by positivity
  have hsq : (bT + l0) ^ 2 ≤ 2 * bT ^ 2 + 2 * l0 ^ 2 := by nlinarith [sq_nonneg (bT - l0)]
  have hpa : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
  -- the `bT` part
  have hA : 32 * K * bT ^ 2 ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
    have hc : (0 : ℝ) ≤ ((n * (n + 1) : ℕ) : ℝ) / 2 * (N : ℝ) ^ (n + 6) := by positivity
    have h1' : bT ^ 2 ≤ (((n * (n + 1) : ℕ) : ℝ) / 2 * (N : ℝ) ^ (n + 6)) ^ 2 * Δ * Δ := by
      rw [hbT]; apply le_of_eq; ring
    have hKΔΔ : K * (Δ * Δ) ≤ Δ := by nlinarith
    calc 32 * K * bT ^ 2
        ≤ 32 * K * ((((n * (n + 1) : ℕ) : ℝ) / 2 * (N : ℝ) ^ (n + 6)) ^ 2 * Δ * Δ) := by gcongr
      _ = 32 * (((n * (n + 1) : ℕ) : ℝ) / 2 * (N : ℝ) ^ (n + 6)) ^ 2 * (K * (Δ * Δ)) := by ring
      _ ≤ 32 * (((n * (n + 1) : ℕ) : ℝ) / 2 * (N : ℝ) ^ (n + 6)) ^ 2
          * ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by
          gcongr; exact hKΔΔ.trans hΔa
      _ = (32 * (((n * (n + 1) : ℕ) : ℝ) / 2) ^ 2 * (N : ℝ) ^ (2 * n + 12))
            * ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by
          rw [mul_pow, ← pow_mul, show (n + 6) * 2 = 2 * n + 12 by ring]
          ring
      _ ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
          refine DuhamelC_le_inv_div hx0 (by norm_num) ?_
          calc 2 * (32 * (((n * (n + 1) : ℕ) : ℝ) / 2) ^ 2 * (N : ℝ) ^ (2 * n + 12))
                * (N : ℝ) ^ (4 * n0 + 5)
              = 64 * (((n * (n + 1) : ℕ) : ℝ) / 2) ^ 2
                * ((N : ℝ) ^ (2 * n + 12) * (N : ℝ) ^ (4 * n0 + 5)) := by ring
            _ = 64 * (((n * (n + 1) : ℕ) : ℝ) / 2) ^ 2 * (N : ℝ) ^ (2 * n + 4 * n0 + 17) := by
                rw [← pow_add]; ring_nf
            _ ≤ _ := h1
  -- the floor part
  have hB2 : 32 * K * l0 ^ 2 ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
    have hKb := hKa.trans (DuhamelC_one_add_pow_le hx (32 * n0 + 64))
    have hl2 : l0 ^ 2 = ((N : ℝ) ^ (80 * n0 + 160))⁻¹ := by
      rw [hl0, inv_pow, ← pow_mul]; ring_nf
    rw [hl2]
    calc 32 * K * ((N : ℝ) ^ (80 * n0 + 160))⁻¹
        ≤ 32 * (2 ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64))
            * ((N : ℝ) ^ (80 * n0 + 160))⁻¹ := by gcongr
      _ ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
          refine DuhamelC_le_inv_div hx0 (by norm_num) ?_
          calc 2 * (32 * (2 ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64))) * (N : ℝ) ^ (4 * n0 + 5)
              = 64 * (2 : ℝ) ^ (32 * n0 + 64) * (N : ℝ) ^ (36 * n0 + 69) := by
                rw [show 36 * n0 + 69 = (32 * n0 + 64) + (4 * n0 + 5) by ring, pow_add]; ring
            _ ≤ _ := h2
  have hR : (((N : ℝ) ^ (2 * n0 + 2))⁻¹) ^ 2 / N = ((N : ℝ) ^ (4 * n0 + 5))⁻¹ := by
    rw [inv_pow, ← pow_mul, div_eq_mul_inv, ← mul_inv, ← pow_succ]; ring_nf
  rw [hR]
  calc 16 * K * (bT + l0) ^ 2 ≤ 16 * K * (2 * bT ^ 2 + 2 * l0 ^ 2) := by gcongr
    _ = 32 * K * bT ^ 2 + 32 * K * l0 ^ 2 := by ring
    _ ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 + ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := add_le_add hA hB2
    _ = _ := by ring

/-- The polynomial prefactor of the absorption. -/
private theorem DuhamelC_num_tau (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, 16 * (n : ℝ) * (N : ℝ) ^ (τ / 4) ≤ (N : ℝ) ^ τ := by
  filter_upwards [eventually_le_rpow (16 * (n : ℝ)) (show 0 < 3 * τ / 4 by linarith),
    eventually_ge_atTop 1] with N h1 hN
  have hx0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) ^ τ = (N : ℝ) ^ (3 * τ / 4) * (N : ℝ) ^ (τ / 4) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)

end Numeric

/-! ### 4. The good events hold with high probability -/

section Events

variable {d : ℕ} (sz : Sizes d)

/-- The dyadic floor `λ₀ = N^{-(40 n₀ + 80)}`. -/
private def DuhamelC_lam0 (n0 N : ℕ) : ℝ := ((N : ℝ) ^ (40 * n0 + 80))⁻¹

/-- The level `N^{-(2n₀+2)}` of the `Ỹ` martingale. -/
private def DuhamelC_epsY (n0 N : ℕ) : ℝ := ((N : ℝ) ^ (2 * n0 + 2))⁻¹

/-- `1 ≤ sz.size n = (W L)^d` (`3 ≤ L`, `1 ≤ W`; no hypothesis on `d`).  `2 ≤ sz.size n` needs
`1 ≤ d` and is used only eventually (`DuhamelC_card_le`; source `DC:926`, `9 ≤ (W L)²`). -/
private theorem DuhamelC_size_pos (n : ℕ) : 1 ≤ sz.size n := by
  unfold Sizes.size
  exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))

/-- `L^d ≤ sz.size n` (source `DC:935`, `L·L ≤ (W L)²`, by `ring`; here `pow_le_pow_left` from
`L ≤ W L`). -/
private theorem DuhamelC_L_pow_le (n : ℕ) : sz.L n ^ d ≤ sz.size n := by
  have hW : 1 ≤ sz.W n := sz.W_pos n
  have h : sz.L n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_left _ hW
  unfold Sizes.size
  exact Nat.pow_le_pow_left h d

/-- Counting the index set of the events: `(N+1)(K+1) 2^m (L^d)^m ≤ N^{2(32n₀+64)+2m+3}`
(`d`-line: `card (Zd d L) = L^d`, source `L·L`).  The grid length is a variable `K`
with `K n = (N+1)^{32n₀+64}` (`gueGridK sz n₀`), so that nothing unfolds the power.  `hN : 2 ≤ N`
replaces the source's `9 ≤ N` (`DuhamelC_size_ge`). -/
private theorem DuhamelC_card_le (n0 m n : ℕ) (K : ℕ → ℕ) (hN : 2 ≤ sz.size n)
    (hKn : K n = (sz.size n + 1) ^ (32 * n0 + 64)) :
    (Fintype.card (Fin (sz.size n + 1) × Fin (K n + 1)
        × ((Fin m → Bool) × (Fin m → Zd d (sz.L n)))) : ℝ)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (((2 * (32 * n0 + 64) + 2 * m + 3 : ℕ)) : ℝ) := by
  have hL := DuhamelC_L_pow_le sz n
  set N : ℕ := sz.size n with hNdef
  have hLD : Fintype.card ((Fin m → Bool) × (Fin m → Zd d (sz.L n)))
      = 2 ^ m * (sz.L n ^ d) ^ m := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool]
    simp only [Fintype.card_fin, Fintype.card_fun, ZMod.card]
  have hcard : Fintype.card (Fin (N + 1) × Fin (K n + 1)
        × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      = (N + 1) * (((N + 1) ^ (32 * n0 + 64) + 1) * (2 ^ m * (sz.L n ^ d) ^ m)) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hLD, hKn]
  have h1 : N + 1 ≤ N ^ 2 := by nlinarith
  have h2 : (N + 1) ^ (32 * n0 + 64) + 1 ≤ N ^ (2 * (32 * n0 + 64) + 1) := by
    have ha : (N + 1) ^ (32 * n0 + 64) ≤ N ^ (2 * (32 * n0 + 64)) := by
      calc (N + 1) ^ (32 * n0 + 64) ≤ (N ^ 2) ^ (32 * n0 + 64) := Nat.pow_le_pow_left h1 _
        _ = N ^ (2 * (32 * n0 + 64)) := by rw [← pow_mul]
    have hb : 1 ≤ N ^ (2 * (32 * n0 + 64)) := Nat.one_le_pow _ _ (by omega)
    have hc : N ^ (2 * (32 * n0 + 64) + 1) = N ^ (2 * (32 * n0 + 64)) * N := pow_succ _ _
    rw [hc]
    nlinarith
  have h3 : 2 ^ m * (sz.L n ^ d) ^ m ≤ N ^ (2 * m) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hN _) (Nat.pow_le_pow_left hL _)
  have hnat : Fintype.card (Fin (N + 1) × Fin (K n + 1)
        × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      ≤ N ^ (2 * (32 * n0 + 64) + 2 * m + 3) := by
    rw [hcard]
    calc (N + 1) * (((N + 1) ^ (32 * n0 + 64) + 1) * (2 ^ m * (sz.L n ^ d) ^ m))
        ≤ N ^ 2 * (N ^ (2 * (32 * n0 + 64) + 1) * N ^ (2 * m)) := by gcongr
      _ = N ^ (2 * (32 * n0 + 64) + 2 * m + 3) := by
          rw [← pow_add, ← pow_add]; congr 1; ring
  rw [Real.rpow_natCast]
  exact_mod_cast hnat

/-- The same count without the level factor. -/
private theorem DuhamelC_card_le' (n0 m n : ℕ) (K : ℕ → ℕ) (hN : 2 ≤ sz.size n)
    (hKn : K n = (sz.size n + 1) ^ (32 * n0 + 64)) :
    (Fintype.card (Fin (K n + 1) × ((Fin m → Bool) × (Fin m → Zd d (sz.L n)))) : ℝ)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (((2 * (32 * n0 + 64) + 2 * m + 3 : ℕ)) : ℝ) := by
  refine le_trans ?_ (DuhamelC_card_le sz n0 m n K hN hKn)
  have : Fintype.card (Fin (K n + 1) × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      ≤ Fintype.card (Fin (sz.size n + 1) × Fin (K n + 1)
        × ((Fin m → Bool) × (Fin m → Zd d (sz.L n)))) := by
    rw [Fintype.card_prod (Fin (sz.size n + 1))]
    exact Nat.le_mul_of_pos_left _ (by simp)
  exact_mod_cast this

/-- `0 < λ₀`. -/
private theorem DuhamelC_lam0_pos (n0 N : ℕ) (hN : 1 ≤ N) : 0 < DuhamelC_lam0 n0 N := by
  unfold DuhamelC_lam0
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- `K n = (N+1)^{32n₀+64}` as reals. -/
private theorem DuhamelC_K_cast (n0 n : ℕ) (K : ℕ → ℕ)
    (hKn : K n = (sz.size n + 1) ^ (32 * n0 + 64)) :
    (K n : ℝ) = (((sz.size n : ℕ) : ℝ) + 1) ^ (32 * n0 + 64) := by
  rw [hKn]; push_cast; ring

/-- **The dyadic Azuma events**: all the dyadic Azuma events hold simultaneously, w.h.p. -/
private theorem DuhamelC_highProb_Z {E t1 t0 : ℕ → ℝ}
    (hsize : Tendsto (fun n => sz.size n) atTop atTop) (ht10 : ∀ n, t1 n ≤ t0 n) (n0 m : ℕ)
    (K : ℕ → ℕ) (hKn : ∀ n, K n = (sz.size n + 1) ^ (32 * n0 + 64))
    {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (Pgue sz) sz.size (fun n =>
      ⋂ u : Fin (sz.size n + 1) × Fin (K n + 1)
          × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))),
      {ω | ‖∑ j ∈ Finset.range (u.2.1 : ℕ), DuhamelZst sz t1 t0 K n (E n)
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
  · have huniv : {ω | ‖∑ j ∈ Finset.range (k : ℕ), DuhamelZst sz t1 t0 K n (E n)
          (loopOf x.1 x.2) lam (j + 1) ω‖
        ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * Real.sqrt ((k : ℕ) * lam)} = Set.univ := by
      ext ω; simp [hk0]
    simp only [hlamdef] at huniv
    rw [huniv, Set.compl_univ, measure_empty]; exact zero_le
  · set ε := 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * Real.sqrt ((k : ℕ) * lam) with hεdef
    have hε0 : 0 ≤ ε := by positivity
    have hsub : {ω | ‖∑ j ∈ Finset.range (k : ℕ), DuhamelZst sz t1 t0 K n (E n)
          (loopOf x.1 x.2) lam (j + 1) ω‖ ≤ ε}ᶜ
        ⊆ {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ), DuhamelZst sz t1 t0 K n (E n)
          (loopOf x.1 x.2) lam (j + 1) ω‖} := fun ω hω => le_of_lt (not_le.1 (by simpa using hω))
    have haz := Duhamel_azuma_Z (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
      (e := E n) (I := loopOf x.1 x.2) hlam hv (k : ℕ) hε0
    have hkl : (0 : ℝ) < (k : ℕ) * lam := mul_pos (by exact_mod_cast hkpos) hlam
    have hexp : -ε ^ 2 / (4 * ((k : ℕ) * lam)) = -((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      have hq : (((sz.size n : ℕ) : ℝ) ^ (τ / 4)) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
      rw [hεdef, mul_pow, mul_pow, hq, Real.sq_sqrt hkl.le]
      field_simp
      ring
    rw [hexp] at haz
    calc (Pgue sz) {ω | ‖∑ j ∈ Finset.range (k : ℕ), DuhamelZst sz t1 t0 K n (E n)
          (loopOf x.1 x.2) lam (j + 1) ω‖ ≤ ε}ᶜ
        ≤ (Pgue sz) {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ), DuhamelZst sz t1 t0 K n
          (E n) (loopOf x.1 x.2) lam (j + 1) ω‖} := measure_mono hsub
      _ = ENNReal.ofReal ((Pgue sz).real {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          DuhamelZst sz t1 t0 K n (E n) (loopOf x.1 x.2) lam (j + 1) ω‖}) :=
          (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (4 * Real.exp (-((sz.size n : ℕ) : ℝ) ^ (τ / 2))) :=
          ENNReal.ofReal_le_ofReal haz
      _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hN

end Events

section Events2

variable {d : ℕ} (sz : Sizes d)

private theorem DuhamelC_loopOf_wf {L m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d L) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem DuhamelC_loopOf_length {L m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d L) :
    (loopOf σ a).length = m := by
  simp [loopOf, LoopIdx.length]

/-- **The uniform truncation bound** of `T` along the grid: `‖T‖ ≤ n(n+1)/2 · N^{n+6} Δ` at
Hermitian base points, `x = N = sz.size n`. -/
private theorem DuhamelC_T_le_uniform {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ}
    {I : LoopIdx (Zd d (sz.L n))} (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 n)
    (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK : 0 < K n)
    (heta : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaT e (t0 n)) {j : ℕ} (hj : j < K n)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian)
    (y : Sizes.SeqΩ sz) :
    ‖DuhamelT sz n (DuhamelPhi sz t1 t0 K n e I j) (Duhamelv sz t1 t0 K n) M y‖
      ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) / 2 * ((sz.size n : ℕ) : ℝ) ^ (I.length + 6)
          * gridStep t1 t0 K n := by
  obtain ⟨hΔ0, _, hη, _, _, _⟩ := Duhamel_grid_facts (K := K) (n := n) he ht1 hst ht0 hK heta
  obtain ⟨hz, hΦ, hC₂⟩ := Duhamel_bddC2C_Phi (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
    (e := e) (I := I) he hwf ht1 hst ht0 hj
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast DuhamelC_size_pos sz n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hv : 0 ≤ Duhamelv sz t1 t0 K n := div_nonneg hΔ0 (Nat.cast_nonneg _)
  refine (Duhamel_norm_T_le hΦ hC₂ hv hM y).trans ?_
  have hpos : 0 < (zt e (gridTime t1 t0 K n (j + 1))).im :=
    lt_of_lt_of_le (by positivity) (hη (j + 1) hj).1
  have hetapos : 0 < etaT e (gridTime t1 t0 K n (j + 1)) := by
    rw [DuhamelC_etaT_eq]; exact hpos
  have hinv : (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ≤ N := by
    rw [DuhamelC_etaT_eq, inv_le_comm₀ hpos hN0]; exact (hη (j + 1) hj).1
  have hpow : (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2) ≤ N ^ (I.length + 2) :=
    pow_le_pow_left₀ (inv_nonneg.2 hetapos.le) hinv _
  have hvN : Duhamelv sz t1 t0 K n = gridStep t1 t0 K n / N := rfl
  have hc0 : (0 : ℝ) ≤ ((I.length * (I.length + 1) : ℕ) : ℝ) * N := by positivity
  calc ((I.length * (I.length + 1) : ℕ) : ℝ) * N
          * (etaT e (gridTime t1 t0 K n (j + 1)))⁻¹ ^ (I.length + 2) / 2
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
private theorem DuhamelC_highProb_Y {κ : ℝ} (hκ : 0 < κ)
    (hsize : Tendsto (fun n => sz.size n) atTop atTop) (n0 m : ℕ) (hm : m ≤ 2 * n0)
    (K : ℕ → ℕ) (hKn : ∀ n, K n = (sz.size n + 1) ^ (32 * n0 + 64)) (hKpos : ∀ n, 0 < K n)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (heta : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaT (E n) (t0 n)) :
    HighProbAt (Pgue sz) sz.size (fun n =>
      ⋂ u : Fin (K n + 1) × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))),
      {ω | ‖∑ j ∈ Finset.range (u.1 : ℕ), DuhamelYst sz t1 t0 K n (E n)
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
  have he : |E n| < 2 := by linarith [hE n]
  have hwf : (loopOf x.1 x.2).WF := DuhamelC_loopOf_wf x.1 x.2
  have hlen : (loopOf x.1 x.2).length = m := DuhamelC_loopOf_length x.1 x.2
  have hK : 0 < K n := hKpos n
  obtain ⟨hΔ0, hKΔ, _, _, _, _⟩ := Duhamel_grid_facts (K := K) (n := n) he (ht1 n)
    (ht10 n) (ht0 n) hK hηN
  set S : ℝ := ((sz.size n : ℕ) : ℝ) with hSdef
  set Δ := gridStep t1 t0 K n with hΔdef
  have hKcast := DuhamelC_K_cast sz n0 n K (hKn n)
  have hTu := fun j (hj : j < K n) (M : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian) (y : Sizes.SeqΩ sz) =>
    DuhamelC_T_le_uniform sz (I := loopOf x.1 x.2) he hwf (ht1 n) (ht10 n) (ht0 n) hK hηN hj hM y
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
      M.IsHermitian → ∀ y, ‖DuhamelT sz n (DuhamelPhi sz t1 t0 K n (E n)
        (loopOf x.1 x.2) j) (Duhamelv sz t1 t0 K n) M y‖ ≤ b := by
    intro j hj M hM y
    refine (hTu j hj M hM y).trans ?_
    rw [hbdef]; linarith
  have hεY : 0 ≤ DuhamelC_epsY n0 (sz.size n) := by unfold DuhamelC_epsY; positivity
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
  · have huniv : {ω | ‖∑ j ∈ Finset.range (k : ℕ), DuhamelYst sz t1 t0 K n (E n)
          (loopOf x.1 x.2) (j + 1) ω‖ ≤ DuhamelC_epsY n0 (sz.size n)} = Set.univ := by
      ext ω; simp [hk0, hεY]
    rw [huniv, Set.compl_univ, measure_empty]; exact zero_le
  · have hkK : (k : ℕ) ≤ K n := Nat.lt_succ_iff.1 k.2
    have haz := Duhamel_azuma_Y (sz := sz) (t1 := t1) (t0 := t0) (K := K) (n := n)
      (e := E n) (I := loopOf x.1 x.2) hb0.le hb hkK hεY
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
    have hsub : {ω | ‖∑ j ∈ Finset.range (k : ℕ), DuhamelYst sz t1 t0 K n (E n)
          (loopOf x.1 x.2) (j + 1) ω‖ ≤ DuhamelC_epsY n0 (sz.size n)}ᶜ
        ⊆ {ω | DuhamelC_epsY n0 (sz.size n) ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          DuhamelYst sz t1 t0 K n (E n) (loopOf x.1 x.2) (j + 1) ω‖} :=
      fun ω hω => le_of_lt (not_le.1 (by simpa using hω))
    calc (Pgue sz) {ω | ‖∑ j ∈ Finset.range (k : ℕ), DuhamelYst sz t1 t0 K n (E n)
          (loopOf x.1 x.2) (j + 1) ω‖ ≤ DuhamelC_epsY n0 (sz.size n)}ᶜ
        ≤ (Pgue sz) {ω | DuhamelC_epsY n0 (sz.size n) ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          DuhamelYst sz t1 t0 K n (E n) (loopOf x.1 x.2) (j + 1) ω‖} :=
          measure_mono hsub
      _ = ENNReal.ofReal ((Pgue sz).real {ω | DuhamelC_epsY n0 (sz.size n) ≤ ‖∑ j ∈
          Finset.range (k : ℕ), DuhamelYst sz t1 t0 K n (E n) (loopOf x.1 x.2)
          (j + 1) ω‖}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(DuhamelC_epsY n0 (sz.size n)) ^ 2
          / (4 * (((k : ℕ) : ℝ) * (4 * b ^ 2))))) := ENNReal.ofReal_le_ofReal haz
      _ ≤ ENNReal.ofReal (4 * Real.exp (-S)) := by
          apply ENNReal.ofReal_le_ofReal
          have := Real.exp_le_exp.2 hexp
          linarith
      _ ≤ ENNReal.ofReal (S ^ (-D)) := ENNReal.ofReal_le_ofReal hexpN

/-- **The drift remainder bounds** hold almost surely, hence w.h.p. -/
private theorem DuhamelC_highProb_AE {κ : ℝ} (hκ : 0 < κ) (m : ℕ) (K : ℕ → ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) :
    HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ j < K n,
      ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖Duhamelr sz t1 t0 K n (E n) (loopOf x.1 x.2) j ω‖
        ≤ envConst d (sz.L n) (sz.W n) (E n) (loopOf x.1 x.2).length
            (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)}) := by
  intro D _
  refine Eventually.of_forall fun n => ?_
  have he : |E n| < 2 := by linarith [hE n]
  have hae : ∀ᵐ ω ∂(Pgue sz), ∀ j : Fin (K n), ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖Duhamelr sz t1 t0 K n (E n) (loopOf x.1 x.2) j ω‖
        ≤ envConst d (sz.L n) (sz.W n) (E n) (loopOf x.1 x.2).length
            (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro x
    exact Duhamel_drift_remainder_ae sz t1 t0 K n j (E n) he
      (DuhamelC_loopOf_wf x.1 x.2) (ht1 n) (ht10 n) (ht0 n) j.2
  have hnull : (Pgue sz) {ω | ∀ j < K n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖Duhamelr sz t1 t0 K n (E n) (loopOf x.1 x.2) j ω‖
        ≤ envConst d (sz.L n) (sz.W n) (E n) (loopOf x.1 x.2).length
            (gridTime t1 t0 K n (j + 1))
          * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)}ᶜ = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun ω hω => ?_) hae
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hω ⊢
    intro hall
    exact hω fun j hj x => hall ⟨j, hj⟩ x
  rw [hnull]; exact zero_le

end Events2

/-! ### 5. The main theorem -/

section Main

variable {d : ℕ} (sz : Sizes d)

/-- **The discrete Duhamel remainder of the GUE-phase loops**, the proof of for a grid length `K`
with `K n = (N+1)^{32n₀+64}`
(`K = gueGridK sz n₀`; a variable so that nothing unfolds the power). -/
private theorem DuhamelC_main {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (K : ℕ → ℕ)
    (hKn : ∀ n, K n = (sz.size n + 1) ^ (32 * n0 + 64)) {E t1 t0 : ℕ → ℝ}
    (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (m : ℕ) (hm : m ≤ 2 * n0) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (K n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n p.1 ω))
            (zt (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
            (zt (E n) (gridTime t1 t0 K n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j)
                (gueH sz t1 t0 K n j ω) (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => Real.sqrt (gridTime t1 t0 K n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            gueLmax sz E t1 t0 K n (2 * m) j ω))
        + (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ m) := by
  have hEb : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hKpos : ∀ n, 0 < K n := fun n => by rw [hKn n]; positivity
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by
    exact_mod_cast DuhamelC_size_pos sz n
  -- `η_{t₀} ≥ N⁻¹`
  have heta : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ)⁻¹ ≤ etaT (E n) (t0 n) := by
    filter_upwards [hscale] with n hs
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith [hN1 n]
    have hη0 : 0 < etaT (E n) (t0 n) := etaT_pos (hEb n) (ht0 n)
    have hpow : ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) * etaT (E n) (t0 n) := by
      have hpos : 0 < ((sz.size n : ℕ) : ℝ) * etaT (E n) (t0 n) := mul_pos hN0 hη0
      have := hs.trans hpow
      unfold gueScale at this
      rwa [inv_le_one_iff₀, or_iff_right (not_le.2 hpos)] at this
    rw [inv_le_iff_one_le_mul₀ hN0]
    nlinarith
  -- `ζ ≥ 0`
  have hζ0 : ∀ n (p : Fin (K n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (ω : PathΩ sz),
      0 ≤ Real.sqrt (gridTime t1 t0 K n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            gueLmax sz E t1 t0 K n (2 * m) j ω))
        + (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ m := by
    intro n p ω
    have h1 : 0 ≤ ⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            gueLmax sz E t1 t0 K n (2 * m) j ω) :=
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
    have hη : 0 < etaT (E n) (gridTime t1 t0 K n p.1) :=
      etaT_pos (hEb n) (lt_of_le_of_lt hle (ht0 n))
    have h2 : 0 ≤ (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ m := by
      unfold gueScale
      have : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith [hN1 n]
      positivity
    have h3 := Real.sqrt_nonneg (gridTime t1 t0 K n p.1 - t1 n)
    positivity
  -- reduction to `τ ≤ 1`
  suffices hmain : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → HighProbAt (Pgue sz) sz.size (fun n => {ω | ∀ p :
      Fin (K n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n p.1 ω))
            (zt (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
            (zt (E n) (gridTime t1 t0 K n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j)
                (gueH sz t1 t0 K n j ω) (loopOf p.2.1 p.2.2)‖
        ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (Real.sqrt (gridTime t1 t0 K n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            gueLmax sz E t1 t0 K n (2 * m) j ω))
        + (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ m)}) by
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
  have hAE := DuhamelC_highProb_AE sz hκ m K hE ht1 ht10 ht0
  have hZ := DuhamelC_highProb_Z (E := E) sz hsize ht10 n0 m K hKn hτ
  have hY := DuhamelC_highProb_Y sz hκ hsize n0 m hm K hKn hKpos hE ht1 ht10 ht0 heta
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
  have he := hEb n
  have hwf := DuhamelC_loopOf_wf x.1 x.2
  have hIlen : (loopOf x.1 x.2).length = m := DuhamelC_loopOf_length x.1 x.2
  obtain ⟨hΔ0, hKΔ, hη, _, _, _⟩ := Duhamel_grid_facts (K := K) (n := n) he (ht1 n)
    (ht10 n) (ht0 n) (hKpos n) hηN
  have hKcast := DuhamelC_K_cast sz n0 n K (hKn n)
  obtain ⟨hΔa, hNΔ⟩ := hstep _ hΔ0 (by rw [← hKcast]; exact hKΔ)
  have hkK : (k : ℕ) ≤ K n := Nat.lt_succ_iff.1 k.2
  have htr : ∀ j < K n, ω (j + 1) ∈ DuhamelGood sz n :=
    fun j hj i l => hωT (j + 1) (by omega) (by omega) i l
  have hr := fun j (hj : j < K n) => hωAE j hj x
  have hZω : ∀ ℓ ≤ sz.size n, ‖∑ j ∈ Finset.range (k : ℕ), DuhamelZst sz t1 t0 K n (E n)
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
  have hpath := DuhamelC_pathwise (I := loopOf x.1 x.2) he hwf (ht1 n) (ht10 n) (ht0 n)
    (hKpos n) (DuhamelC_lam0_pos n0 _ (DuhamelC_size_pos sz n)) (hN1 n) hηN hNΔ
    hQ' hc htr hr hkK hZω hYω
  rw [hIlen] at hpath
  unfold gueLmax
  refine hpath.trans ?_
  -- the scalar bookkeeping
  set Δ := gridStep t1 t0 K n with hΔdef
  set sq := Real.sqrt (gridTime t1 t0 K n (k : ℕ) - t1 n) with hsqdef
  set M := ⨆ j : Fin (k : ℕ), Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
      (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
      RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt (E n) (gridTime t1 t0 K n j)) (2 * m)) with hMdef
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
  -- the prefactor and the control
  have hT6 : 8 * (m : ℝ) * (2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) * sq * M
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (sq * M) := by
    have h := mul_le_mul_of_nonneg_right htau (mul_nonneg hsq0 hM0)
    calc 8 * (m : ℝ) * (2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) * sq * M
        = 16 * m * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * (sq * M) := by ring
      _ ≤ _ := h
  have hT7 : (((sz.size n : ℕ) : ℝ) ^ m)⁻¹
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n (gridTime t1 t0 K n (k : ℕ)))⁻¹ ^ m := by
    have hηk := hη (k : ℕ) hkK
    have hSc : 0 < gueScale sz E n (gridTime t1 t0 K n (k : ℕ)) := by
      unfold gueScale
      rw [DuhamelC_etaT_eq]
      exact mul_pos hN0 (lt_of_lt_of_le (by positivity) hηk.1)
    have hScN : gueScale sz E n (gridTime t1 t0 K n (k : ℕ)) ≤ ((sz.size n : ℕ) : ℝ) := by
      unfold gueScale
      rw [DuhamelC_etaT_eq]
      calc ((sz.size n : ℕ) : ℝ) * (zt (E n) (gridTime t1 t0 K n (k : ℕ))).im
          ≤ ((sz.size n : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hηk.2 hN0.le
        _ = ((sz.size n : ℕ) : ℝ) := mul_one _
    have hinv : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ (gueScale sz E n (gridTime t1 t0 K n (k : ℕ)))⁻¹ :=
      inv_anti₀ hSc hScN
    have hpow : (((sz.size n : ℕ) : ℝ) ^ m)⁻¹
        ≤ (gueScale sz E n (gridTime t1 t0 K n (k : ℕ)))⁻¹ ^ m := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hinv m
    have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow (hN1 n) hτ.le
    have h0 : 0 ≤ (gueScale sz E n (gridTime t1 t0 K n (k : ℕ)))⁻¹ ^ m :=
      pow_nonneg (inv_nonneg.2 hSc.le) m
    exact hpow.trans (le_mul_of_one_le_left h0 hNτ)
  rw [mul_add]
  linarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7]

end Main

section Public

/-- **The discrete Duhamel remainder of the GUE-phase loops**: for loops of length `1 ≤ m ≤ 2 n₀`,
uniformly in the grid step `k ≤ K = gueGridK sz n₀ n` and the loop `(σ, a)`,
`‖L_k − L_0 − Δ Σ_{j<k} 𝓖_GUE(u_j, H_j)‖ ≺
  √(u_k − t₁) · max_{j<k} √(N⁻¹ η_{u_j}^{-2} L^{(2m)}_j) + (N η_{u_k})^{-m}`, `N = sz.size n = (W L)^d`.
Unstopped (no stopping time of D6d/D6e enters); on the size scale (`StochDomAt`, thresholds and
failure rates in `sz.size n`); `1 ≤ m` is not used (the drift remainder of
`Duhamel_drift_remainder_ae`
needs no length hypothesis). -/
theorem gueGrid_loop_duhamel {d : ℕ} (sz : Sizes d) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (m : ℕ) (_hm1 : 1 ≤ m) (hm : m ≤ 2 * n0) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω))
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n 0 ω))
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 (gueGridK sz n0) n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
                (gueH sz t1 t0 (gueGridK sz n0) n j ω) (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => Real.sqrt (gridTime t1 t0 (gueGridK sz n0) n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
            gueLmax sz E t1 t0 (gueGridK sz n0) n (2 * m) j ω))
        + (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹ ^ m) :=
  DuhamelC_main sz hκ hτU n0 (gueGridK sz n0) (fun _ => rfl) hsize hE ht1 ht10 ht0 hscale m hm

end Public

end RBM.Univ.GUEPhase

/-! ### 6. Compiled nonempty instance of `gueGrid_loop_duhamel`

Namespace `RBM.Univ.GUEPhase.DuhamelCInst`.  Data: the merged `SizesInst.sz0` (`d = 3`,
`L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`, `N_n = 2^21 (n+1)^18`, `N_0 = 2097152`), `E_n = 0`
(`|E_n| ≤ 2 - κ` with `κ = 1`, `mE 0 = I`), `τU = 1/2`, `n₀ = 1`, the `Grid.lean` §`GridCheck`
times `t₀ = 9/10`, `t₁ = (1 - ζ(1/20)) t₀ = e^{-1/20} t₀`, loops of length `m = 2 ≤ 2 n₀`
(`1 ≤ m`), the grid `K = gueGridK sz0 1`.  `hsize` is the merged `sz0_size_tendsto_nat`; `hscale`
is discharged (`η_{t₀} = 1/10`, `(N/10)⁻¹ ≤ N^{-1/2}` iff `N ≥ 100`, eventually).  Every hypothesis
of the target is discharged; there is no external hypothesis. -/

namespace RBM.Univ.GUEPhase.DuhamelCInst

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
  RBM.Gauss.SizesInst RBM.Univ.GUEPhase RBM.Loop
open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev DuhamelCInst_t1 : ℕ → ℝ := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)
private abbrev DuhamelCInst_t0 : ℕ → ℝ := fun _ => 9 / 10

private theorem DuhamelCInst_t1_le_t0 : ∀ n, DuhamelCInst_t1 n ≤ DuhamelCInst_t0 n := by
  intro n
  unfold DuhamelCInst_t1 DuhamelCInst_t0 ouZeta
  have : Real.exp (-(1 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  nlinarith

private theorem DuhamelCInst_mE_im : (mE 0).im = 1 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [mE, h4]

private theorem DuhamelCInst_eta : RBM.Gauss.etaT 0 (9 / 10) = 1 / 10 := by
  unfold RBM.Gauss.etaT
  rw [DuhamelCInst_mE_im]
  norm_num

/-- `hscale` at `sz0`: `(N η_{t₀})⁻¹ = 10 / N ≤ N^{-1/2}` as soon as `N ≥ 100`. -/
theorem hscale_check :
    ∀ᶠ n in atTop, (gueScale sz0 (fun _ => (0 : ℝ)) n (DuhamelCInst_t0 n))⁻¹
      ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [MarkovInst.sz0_size_tendsto_nat.eventually (eventually_ge_atTop 100)] with n hN
  have hN' : (100 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast hN
  set N : ℝ := ((sz0.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hs : 10 ≤ Real.sqrt N := by
    have h10 : Real.sqrt 100 = 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h10]
    exact Real.sqrt_le_sqrt hN'
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  unfold gueScale DuhamelCInst_t0
  rw [DuhamelCInst_eta, Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow]
  refine inv_anti₀ hspos ?_
  nlinarith

/-- **`gueGrid_loop_duhamel` at `sz0`** (`d = 3`), `κ = 1`, `τU = 1/2`, `n₀ = 1`, `E = 0`,
the `GridCheck` times, loops of length `m = 2`: every hypothesis is discharged. -/
theorem gueGrid_loop_duhamel_check :
    StochDomAt (Pgue sz0) sz0.size
      (fun n (p : Fin (gueGridK sz0 1 n + 1) × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))) ω =>
        ‖loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
              (gueH sz0 DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1 ω))
            (zt 0 (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1))
            (loopOf p.2.1 p.2.2)
          - loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n)
              (gueH sz0 DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n 0 ω))
            (zt 0 (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n 0))
            (loopOf p.2.1 p.2.2)
          - (gridStep DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n : ℂ) *
            ∑ j ∈ Finset.range p.1,
              genMatGUE 3 (sz0.L n) (sz0.W n) 0
                (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n j)
                (gueH sz0 DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n j ω)
                (loopOf p.2.1 p.2.2)‖)
      (fun n p ω =>
        Real.sqrt (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1
            - DuhamelCInst_t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz0.size n : ℕ) : ℝ))⁻¹ *
            (RBM.Gauss.etaT 0 (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n j))⁻¹
              ^ 2 *
            gueLmax sz0 (fun _ => (0 : ℝ)) DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n
              (2 * 2) j ω))
        + (gueScale sz0 (fun _ => (0 : ℝ)) n
            (gridTime DuhamelCInst_t1 DuhamelCInst_t0 (gueGridK sz0 1) n p.1))⁻¹ ^ 2) :=
  gueGrid_loop_duhamel sz0 (κ := 1) (τU := 1 / 2) one_pos (by norm_num) 1
    (E := fun _ => (0 : ℝ)) (t1 := DuhamelCInst_t1) (t0 := DuhamelCInst_t0)
    MarkovInst.sz0_size_tendsto_nat (fun n => by norm_num) (fun _ => GridCheck.t1_pos)
    DuhamelCInst_t1_le_t0 (fun _ => by norm_num) hscale_check 2 (by norm_num) (by norm_num)

end RBM.Univ.GUEPhase.DuhamelCInst

end
