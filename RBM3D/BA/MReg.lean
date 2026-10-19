/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.ImmLower
import RBM3D.BA.Boundary
import RBM3D.BA.UNPins
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Regularity of the block Anderson Stieltjes transform on a bulk window

Proves `RBM.Univ.UNDensBARow'` (`BA/UNPins`) unconditionally, for every `d`, with constants depending on
`κ` only (uniform in `L`, `λ`, `d`, `n`).  Paper: the density `ρ_N = π⁻¹ Im m(E + i0)` of `μ_N` (text before (2.32) `self_m`),
`(self_m)` (2.32), and the regularity input of Definition 2.1 of Landon-Sosoe-Yau (arXiv:1609.09011v4) used in the proof of Theorem 2.4 (`Thm: B_Univ`).

The proof is finite algebra plus one compactness step.  With `κ₁ = πκ` and "solution at `z`" = `BASelf d L g z m`:

* (a) every solution at `Im z ≥ 0` has `‖m‖ ≤ 1` (`BAm_norm_le_one`); `BAbulk κ E` is a real-axis solution
  `m_E` with `κ₁ ≤ Im m_E` (`BAbulk_iff_exists`), and then `BAm E = m_E` (`BAm_real_eq_of_self`);
* (b) `BAm_sub_le_of_im`: `(Im m² + Im m'²) ‖m - m'‖ ≤ 2 ‖z - z'‖` (`BASelf_sub_le`) with
  `Im m, Im m' ≥ c` gives `‖m - m'‖ ≤ ‖z - z'‖ / c²`;
* (c) `BAbulk_window`: for `0 < η ≤ κ₁³/8` the value `m(x + iη)` stays within `κ₁/2` of `m_E`
  (`BASelf_sub_le`); a subsequence `η_k ↓ 0` converges (Bolzano-Weierstrass) to a solution at `x`
  (`BASelf_of_tendsto`) with `Im ≥ κ₁/2`;
* (d) `BArho_rate_of_bulk`:
  `|π⁻¹ Im m(E + iη) - ρ(E)| ≤ 2η / (π³κ²)`; (e) `BAm_im_lower_window`: `Im m(x + iη) ≥ κ₁⁵/2048` on
  the window `|x - E| ≤ κ₁³/8`, `0 < η ≤ 10` (`BAm_im_lower_of_bulk` for `η ≤ 1`, `BAm_im_ge_mul` for `1 < η ≤ 10`);
* (f) `RBM.Univ.unDens'_ba`: `UNDens'` of the datum `m n = m(·, λ_n)`, `ρ n = ρ_{N_n}(E)` with
  `c = κ₁⁵/2048`, `C = K = 1`, `Lp = 1/c²`, all fixed before `∀ᶠ n`; (g) `unDensBARow'_holds`:
  `δ₀ = (πκ)³/8`.

The hypotheses of `UNDensBARow'` that the proof does not use are `3 ≤ d` and `sz.Admissible 𝔠 𝔡` (so `𝔠`, `𝔡`); `3 ≤ L` is used only through
the instance `Sizes.neZeroL`.  Sections 1-5 assume no sign of `g = λ_n`.  The constants are not optimized.
Not here: the coupling shift `|m(z, λ e^{t/2}) - m(z, λ)| ≤ C t` and `BAPropM`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open Filter Topology

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The two-point estimate in the form used below -/

/-- Two solutions with `Im ≥ c ≥ 0`: `c² ‖m - m'‖ ≤ ‖z - z'‖`. -/
private theorem MReg_two (d L : ℕ) [NeZero L] (g c : ℝ) (z z' m m' : ℂ) (hz : 0 ≤ z.im) (hz' : 0 ≤ z'.im)
    (h : BASelf d L g z m) (h' : BASelf d L g z' m') (hc : 0 ≤ c) (h1 : c ≤ m.im) (h2 : c ≤ m'.im) :
    c ^ 2 * ‖m - m'‖ ≤ ‖z - z'‖ := by
  have h0 := BASelf_sub_le d L g z z' m m' hz hz' h h'
  have hs : 2 * c ^ 2 ≤ m.im ^ 2 + m'.im ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right hs (norm_nonneg (m - m'))
  nlinarith

/-- `‖(E : ℂ) - (x + η I)‖ ≤ |x - E| + η` for `η > 0`. -/
private theorem MReg_norm_sub_le (E x η : ℝ) (hη : 0 < η) :
    ‖(E : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤ |x - E| + η := by
  have h1 : (E : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I) =
      ((E - x : ℝ) : ℂ) + (-(η : ℂ) * Complex.I) := by push_cast; ring
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_of_pos hη, abs_sub_comm]

/-! ## 2. The modulus of `m` off the real axis -/

/-- The modulus of `m(·, g)` off the real axis, uniform in `d`, `L`, `g`: two points of the upper
half plane where `Im m ≥ c > 0` give `‖m(z) - m(z')‖ ≤ ‖z - z'‖ / c²`.  Paper: the proof of Lemma 8.3 (`lem:propM`), through `BASelf_sub_le`. -/
theorem BAm_sub_le_of_im (d L : ℕ) [NeZero L] (g c : ℝ) (z z' : ℂ) (hc : 0 < c) (hz : 0 < z.im) (hz' : 0 < z'.im)
    (h1 : c ≤ (BAm d L g z).im) (h2 : c ≤ (BAm d L g z').im) :
    ‖BAm d L g z - BAm d L g z'‖ ≤ ‖z - z'‖ / c ^ 2 := by
  have h := MReg_two d L g c z z' _ _ hz.le hz'.le (BAm_self d L g z hz) (BAm_self d L g z' hz') hc.le h1 h2
  rw [le_div_iff₀ (by positivity)]
  linarith

/-! ## 3. The bulk window -/

/-- The estimate of (c): for `0 < η ≤ κ₁³/8` and `|x - E| ≤ κ₁³/8`, `Im m(x + iη) ≥ κ₁/2`, given a real-axis
solution `m_E` at `E` with `κ₁ ≤ Im m_E`. -/
private theorem MReg_key (d L : ℕ) [NeZero L] (g κ E x : ℝ) (hκ : 0 < κ) (mE : ℂ)
    (hmE : BASelf d L g (E : ℂ) mE) (hmEκ : Real.pi * κ ≤ mE.im) (hx : |x - E| ≤ (Real.pi * κ) ^ 3 / 8)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ (Real.pi * κ) ^ 3 / 8) :
    Real.pi * κ / 2 ≤ (BAm d L g ((x : ℂ) + (η : ℂ) * Complex.I)).im := by
  have hz' : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
  have hs' := BAm_self d L g _ hz'
  have h1 := BASelf_sub_le d L g (E : ℂ) _ mE _ (by simp) hz'.le hmE hs'
  have h2 := MReg_norm_sub_le E x η hη
  set m' := BAm d L g ((x : ℂ) + (η : ℂ) * Complex.I) with hm'
  set k := Real.pi * κ with hk
  have hk0 : 0 < k := by positivity
  have h3 : k ^ 2 * ‖mE - m'‖ ≤ k ^ 3 / 2 := by
    have h4 : k ^ 2 ≤ mE.im ^ 2 + m'.im ^ 2 := by nlinarith [sq_nonneg m'.im]
    have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg (mE - m'))
    nlinarith
  have h4 : ‖mE - m'‖ ≤ k / 2 := by
    by_contra hc
    have hc := not_le.mp hc
    have h5 : k ^ 2 * (k / 2) < k ^ 2 * ‖mE - m'‖ := mul_lt_mul_of_pos_left hc (by positivity)
    nlinarith
  have h5 : (mE - m').im ≤ ‖mE - m'‖ := Complex.im_le_norm _
  rw [Complex.sub_im] at h5
  linarith

/-- The bulk set is open, quantitatively: `ρ_N(E) ≥ κ` and `|x - E| ≤ (πκ)³/8` give
`ρ_N(x) ≥ κ/2`.  A real-axis solution at `x` is built as a subsequential limit of `m(x + iη_k)`, `η_k ↓ 0`
(Bolzano-Weierstrass, `BASelf_of_tendsto`); no `3 ≤ L`, no `0 < g`. -/
theorem BAbulk_window (d L : ℕ) [NeZero L] (g κ E x : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (hx : |x - E| ≤ (Real.pi * κ) ^ 3 / 8) : BAbulk d L g (κ / 2) x := by
  obtain ⟨mE, hmE, hmEκ⟩ := (BAbulk_iff_exists d L g κ E hκ).mp hb
  have hk0 : 0 < Real.pi * κ := by positivity
  have key := MReg_key d L g κ E x hκ mE hmE hmEκ hx
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun k : ℕ => (Real.pi * κ) ^ 3 / 8 * (1 / ((k : ℝ) + 1)) := by
    exact ⟨_, rfl⟩
  have hηpos : ∀ k, 0 < η k := fun k => by rw [hηdef]; positivity
  have hηle : ∀ k, η k ≤ (Real.pi * κ) ^ 3 / 8 := fun k => by
    rw [hηdef]
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h2 : 0 ≤ (Real.pi * κ) ^ 3 / 8 := by positivity
    simpa using mul_le_mul_of_nonneg_left h1 h2
  have hη0 : Tendsto η atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((Real.pi * κ) ^ 3 / 8)
    rw [hηdef]
    simpa using this
  obtain ⟨zs, hzsdef⟩ : ∃ zs : ℕ → ℂ, zs = fun k : ℕ => (x : ℂ) + (η k : ℂ) * Complex.I := by
    exact ⟨_, rfl⟩
  have hzim : ∀ k, 0 < (zs k).im := fun k => by rw [hzsdef]; simp [hηpos k]
  have hself : ∀ k, BASelf d L g (zs k) (BAm d L g (zs k)) := fun k => BAm_self d L g _ (hzim k)
  have hbd : ∀ k, BAm d L g (zs k) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro k
    rw [mem_closedBall_zero_iff]
    exact BAm_norm_le_one d L g _ _ (hzim k).le (hself k)
  obtain ⟨m, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hbd
  have hmim : Real.pi * κ / 2 ≤ m.im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto m).comp hlim)
      (Eventually.of_forall fun k => by
        have := key (η (φ k)) (hηpos _) (hηle _)
        simpa [hzsdef] using this)
  have hzs : Tendsto (fun k => zs (φ k)) atTop (𝓝 (x : ℂ)) := by
    have h1 : Continuous (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have := (h1.tendsto 0).comp (hη0.comp hφ.tendsto_atTop)
    simpa [hzsdef, Function.comp_def] using this
  have hs : BASelf d L g (x : ℂ) m :=
    BASelf_of_tendsto d L g (x : ℂ) m _ _ hzs hlim (fun k => (hzim _).le) (fun k => hself _)
      (by linarith)
  refine (BAbulk_iff_exists d L g (κ / 2) x (by positivity)).mpr ⟨m, hs, ?_⟩
  linarith

/-! ## 4. The boundary value with a rate -/

/-- The boundary value with a rate, in the `κ`-bulk, no `3 ≤ L`, no `0 < g`:
`|π⁻¹ Im m(E + iη) - ρ_N(E)| ≤ 2η / (π³κ²)` for every `η > 0`. -/
theorem BArho_rate_of_bulk (d L : ℕ) [NeZero L] (g κ E : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (η : ℝ) (hη : 0 < η) :
    |(BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi - BArho d L g E| ≤
      2 * η / (Real.pi ^ 3 * κ ^ 2) := by
  obtain ⟨mE, hmE, hmEκ⟩ := (BAbulk_iff_exists d L g κ E hκ).mp hb
  have e1 := BAm_real_eq_of_self d L g E mE hmE
  have hz' : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
  have hs' := BAm_self d L g _ hz'
  set m' := BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I) with hm'
  have hm'1 : ‖m'‖ ≤ 1 := BAm_norm_le_one d L g _ _ hz'.le hs'
  have h := BASelf_sub_le d L g (E : ℂ) _ mE _ (by simp) hz'.le hmE hs'
  have h2 : ‖(E : ℂ) - ((E : ℂ) + (η : ℂ) * Complex.I)‖ = η := by
    rw [sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hη]
  rw [h2] at h
  have hk0 : 0 < Real.pi * κ := by positivity
  have h1 : |m'.im - mE.im| ≤ ‖mE - m'‖ := by
    have := Complex.abs_im_le_norm (mE - m')
    rwa [Complex.sub_im, abs_sub_comm] at this
  have h3 : (Real.pi * κ) ^ 2 * ‖mE - m'‖ ≤ 2 * η := by
    have h4 : (Real.pi * κ) ^ 2 ≤ mE.im ^ 2 + m'.im ^ 2 := by nlinarith [sq_nonneg m'.im]
    have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg (mE - m'))
    nlinarith
  have h6 : |m'.im - mE.im| * (Real.pi * κ) ^ 2 ≤ 2 * η := by
    have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ (Real.pi * κ) ^ 2)
    nlinarith
  unfold BArho
  rw [e1, ← sub_div, abs_div, abs_of_pos Real.pi_pos, div_le_div_iff₀ Real.pi_pos (by positivity)]
  have := mul_le_mul_of_nonneg_right h6 Real.pi_pos.le
  nlinarith

/-! ## 5. The lower bound on the window -/

/-- On the window `|x - E| ≤ (πκ)³/8`, `0 < η ≤ 10`: `Im m(x + iη) ≥ (πκ)⁵/2048`.
Window form of the lower bound `BAm_im_lower_of_bulk`, `BAm_im_ge_mul`. -/
theorem BAm_im_lower_window (d L : ℕ) [NeZero L] (g κ E x η : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (hx : |x - E| ≤ (Real.pi * κ) ^ 3 / 8) (hη : 0 < η) (hη10 : η ≤ 10) :
    (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g ((x : ℂ) + (η : ℂ) * Complex.I)).im := by
  have hw := BAbulk_window d L g κ E x hκ hb hx
  have hκ2 : 0 < κ / 2 := by positivity
  obtain ⟨mE, hmE, hmEκ⟩ := (BAbulk_iff_exists d L g κ E hκ).mp hb
  have hk0 : 0 < Real.pi * κ := by positivity
  have hk1 : Real.pi * κ ≤ 1 :=
    hmEκ.trans ((Complex.im_le_norm _).trans (BAm_norm_le_one d L g (E : ℂ) mE (by simp) hmE))
  by_cases h1 : η ≤ 1
  · have h := BAm_im_lower_of_bulk d L g (κ / 2) x hκ2 hw η hη h1
    have e : (Real.pi * (κ / 2)) ^ 5 / 64 = (Real.pi * κ) ^ 5 / 2048 := by ring
    rwa [e] at h
  · have h1 := not_le.mp h1
    obtain ⟨m, hm, hmκ⟩ := (BAbulk_iff_exists d L g (κ / 2) x hκ2).mp hw
    have h := BAm_im_ge_mul d L g (Real.pi * (κ / 2)) x m (by positivity) ⟨hm, hmκ⟩ η hη
    refine le_trans ?_ h
    have hk5 : (Real.pi * κ) ^ 5 ≤ (Real.pi * κ) ^ 2 :=
      pow_le_pow_of_le_one hk0.le hk1 (by norm_num)
    have e : (Real.pi * (κ / 2)) ^ 2 = (Real.pi * κ) ^ 2 / 4 := by ring
    rw [e, le_div_iff₀ (by positivity)]
    have hk2 : 0 < (Real.pi * κ) ^ 2 := by positivity
    nlinarith [mul_pos hk2 hη, mul_le_mul_of_nonneg_left (show (η + 3) ^ 2 ≤ 169 * η by nlinarith) hk2.le]

end RBM.BA

/-! ## 6. `UNDens'` of the block Anderson datum and `UNDensBARow'` -/

namespace RBM.Univ

open RBM RBM.Gauss RBM.BA

/-- `⟨x, η⟩ = x + η I` as complex numbers. -/
private theorem MReg_mk (x η : ℝ) : (⟨x, η⟩ : ℂ) = (x : ℂ) + (η : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- `‖⟨x, η⟩ - ⟨y, η⟩‖ = |x - y|`. -/
private theorem MReg_norm_horiz (x y η : ℝ) : ‖(⟨x, η⟩ : ℂ) - ⟨y, η⟩‖ = |x - y| := by
  have : (⟨x, η⟩ : ℂ) - ⟨y, η⟩ = ((x - y : ℝ) : ℂ) := by apply Complex.ext <;> simp
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-- The pointwise facts at a fixed model `(d, L, g)` with `ρ_N(E) ≥ κ`, on the box `|Re z - E| ≤ δ`,
`0 < Im z ≤ 10`: lower bound, `Im m ≤ 1`, `‖m‖ ≤ 1`, and the Lipschitz bound with `Lp = 1/c²`, `c = (πκ)⁵/2048`. -/
private theorem MReg_pt (d L : ℕ) [NeZero L] (g κ E δ : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (hδ : δ ≤ (Real.pi * κ) ^ 3 / 8) :
    (∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 10 →
      (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g z).im ∧ (BAm d L g z).im ≤ 1 ∧ ‖BAm d L g z‖ ≤ 1) ∧
    (∀ z z' : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 10 → |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 10 →
      ‖BAm d L g z - BAm d L g z'‖ ≤ 1 / ((Real.pi * κ) ^ 5 / 2048) ^ 2 * ‖z - z'‖) := by
  have hk0 : 0 < Real.pi * κ := by positivity
  have hlow : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 10 →
      (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g z).im := by
    intro z hz h0 h10
    have := BAm_im_lower_window d L g κ E z.re z.im hκ hb (hz.trans hδ) h0 h10
    rwa [Complex.re_add_im] at this
  refine ⟨fun z hz h0 h10 => ?_, fun z z' hz h0 h10 hz' h0' h10' => ?_⟩
  · have hn : ‖BAm d L g z‖ ≤ 1 := BAm_norm_le_one d L g z _ h0.le (BAm_self d L g z h0)
    exact ⟨hlow z hz h0 h10, (Complex.im_le_norm _).trans hn, hn⟩
  · have h := BAm_sub_le_of_im d L g ((Real.pi * κ) ^ 5 / 2048) z z' (by positivity) h0 h0'
      (hlow z hz h0 h10) (hlow z' hz' h0' h10')
    calc ‖BAm d L g z - BAm d L g z'‖ ≤ ‖z - z'‖ / ((Real.pi * κ) ^ 5 / 2048) ^ 2 := h
      _ = 1 / ((Real.pi * κ) ^ 5 / 2048) ^ 2 * ‖z - z'‖ := by ring

/-- `UNDens'` of the block Anderson datum `m n = m(·, λ_n)`, `ρ n = ρ_{N_n}(E)`, on every window
`0 < δ ≤ (πκ)³/8`, from the eventual bulk at `E` alone (no admissibility, no sign of `λ_n`).  Constants (before
`∀ᶠ n`): `c = (πκ)⁵/2048`, `C = K = 1`, `Lp = 1/c²`. -/
theorem unDens'_ba (d : ℕ) (sz : Sizes d) (κ E : ℝ) (hκ : 0 < κ)
    (hb : ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) (δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ ≤ (Real.pi * κ) ^ 3 / 8) :
    UNDens' (fun n => BAm d (sz.L n) (sz.lam n)) E (fun n => BArho d (sz.L n) (sz.lam n) E) δ := by
  have hk0 : 0 < Real.pi * κ := by positivity
  have hcpos : 0 < (Real.pi * κ) ^ 5 / 2048 := by positivity
  have hLp : 0 < 1 / ((Real.pi * κ) ^ 5 / 2048) ^ 2 := by positivity
  refine ⟨⟨hδ, (Real.pi * κ) ^ 5 / 2048, 1, 1 / ((Real.pi * κ) ^ 5 / 2048) ^ 2, hcpos, one_pos, hLp, ?_⟩,
    (Real.pi * κ) ^ 5 / 2048, 1, 1 / ((Real.pi * κ) ^ 5 / 2048) ^ 2, hcpos, one_pos, hLp, ?_⟩
  · filter_upwards [hb] with n hn
    obtain ⟨hpt, hlip⟩ := MReg_pt d (sz.L n) (sz.lam n) κ E δ hκ hn hδ'
    refine ⟨fun x η hx h0 h10 => ?_, fun x y η hx hy h0 h10 => ?_, ?_⟩
    · obtain ⟨h1, h2, -⟩ := hpt ⟨x, η⟩ hx h0 h10
      exact ⟨h1, h2⟩
    · have h := hlip ⟨x, η⟩ ⟨y, η⟩ hx h0 h10 hy h0 h10
      rw [MReg_norm_horiz] at h
      refine le_trans ?_ h
      have := Complex.abs_im_le_norm (BAm d (sz.L n) (sz.lam n) ⟨x, η⟩ - BAm d (sz.L n) (sz.lam n) ⟨y, η⟩)
      rwa [Complex.sub_im] at this
    · have hg : Tendsto (fun η : ℝ => 2 * η / (Real.pi ^ 3 * κ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h1 : Tendsto (fun η : ℝ => 2 * η / (Real.pi ^ 3 * κ ^ 2)) (𝓝 (0 : ℝ))
            (𝓝 (2 * 0 / (Real.pi ^ 3 * κ ^ 2))) :=
          ((continuous_const.mul continuous_id).div_const _).tendsto 0
        simpa using h1.mono_left nhdsWithin_le_nhds
      refine tendsto_iff_dist_tendsto_zero.mpr
        (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hg)
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [Real.dist_eq]
      have := BArho_rate_of_bulk d (sz.L n) (sz.lam n) κ E hκ hn η hη
      rw [MReg_mk]
      exact this
  · filter_upwards [hb] with n hn
    obtain ⟨hpt, hlip⟩ := MReg_pt d (sz.L n) (sz.lam n) κ E δ hκ hn hδ'
    refine ⟨fun z hz h0 h1 => ?_, fun z z' hz h0 h1 hz' h0' h1' => ?_⟩
    · obtain ⟨h2, -, h4⟩ := hpt z hz h0 (h1.trans (by norm_num))
      exact ⟨h2, h4⟩
    · exact hlip z z' hz h0 (h1.trans (by norm_num)) hz' h0' (h1'.trans (by norm_num))

/-- `UNDensBARow'` (`BA/UNPins`), unconditionally, with
`δ₀ = (πκ)³/8`.  The hypotheses `3 ≤ d` and `sz.Admissible 𝔠 𝔡` are not used. -/
theorem unDensBARow'_holds : UNDensBARow' := by
  intro d _ 𝔠 𝔡 sz _ κ hκ E hb
  refine ⟨(Real.pi * κ) ^ 3 / 8, by positivity, fun δ hδ hδ0 => ⟨unDens'_ba d sz κ E hκ hb δ hδ hδ0, fun x hx => ?_⟩⟩
  filter_upwards [hb] with n hn
  exact BAbulk_window d (sz.L n) (sz.lam n) κ E x hκ hn (hx.trans hδ0)

end RBM.Univ

