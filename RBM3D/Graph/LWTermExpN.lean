/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWPins

/-!
# LW-16: `lem: EWGn2_N` in the regime `1 - t ≤ ĝ²/L²` from `lem:LWterm` (T2342)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:20` ("an immediate consequence of `lem:LWterm`,
with `ℓ_t = L`") and `paper/tex/3_5_Loop_Hierarchy.tex:385-415`.

`lwtermExpN_of_LWterm : ∀ d, LWterm d → LWtermExpN d`: `lem:LWterm` is applied to the merged B class
`Φ = LWPhiB sz d K t` (`c₀ = d`, `K n = ⌊ℓ n⌋ ∧ L n`), at the window `ε₁ = min(ε₀, d c/2)` and the given
control parameter `Ψ`.

* Section 1: `≺` with an eventual pointwise constant (`lwN_prec_mono`), `η_t ≥ 0`.
* Section 2: deterministic facts on `B`, `𝒯`, `wT`: the comparison with the B class on `r ≤ L`
  (`lwN_tailW_le`, all regimes) and in the regime `1 - t ≤ g²/L²` (`lwN_B_le_tail`).
* Section 3: the size data (`W^{-d} B_{t,0} ≤ N^{-c}` for `t ≤ lemT z`, copied from the merged
  `ST_Bdata_holds`, `Induction/Step2Iterate.lean:1049`, which is not in the import closure of `LWPins`),
  and `W^{-1/𝔠} ≤ L^{-d}`.
* Section 4: the target.
* Section 5: the compiled nonempty instance at `d = 3`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.flexible false

noncomputable section

open MeasureTheory Filter

/-! ## 1. `≺` with an eventual constant, `η_t ≥ 0` -/

namespace RBM

/-- If `ζ ≤ c ζ'` pointwise eventually (with `ζ' ≥ 0`) and `ξ ≺ ζ`, then `ξ ≺ ζ'`. -/
theorem lwN_prec_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*} {size : ℕ → ℕ}
    {ξ ζ ζ' : ∀ l, U l → Ω → ℝ} (hsize : Tendsto size atTop atTop) {c : ℝ}
    (hle : ∀ᶠ l in atTop, ∀ u ω, 0 ≤ ζ' l u ω ∧ ζ l u ω ≤ c * ζ' l u ω)
    (h : StochDomAt P size ξ ζ) : StochDomAt P size ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, hsize.eventually (eventually_le_rpow c (half_pos hτ))] with l hl hcN
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  obtain ⟨hnn, hz⟩ := hl u ω
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmul : (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2)) = (size l : ℝ) ^ τ := by
    rw [← Real.rpow_add' (Nat.cast_nonneg _) (by linarith)]; congr 1; ring
  have h1 : (size l : ℝ) ^ (τ / 2) * ζ l u ω ≤ (size l : ℝ) ^ τ * ζ' l u ω := by
    calc (size l : ℝ) ^ (τ / 2) * ζ l u ω ≤ (size l : ℝ) ^ (τ / 2) * (c * ζ' l u ω) :=
          mul_le_mul_of_nonneg_left hz hpos
      _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ' l u ω) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcN hnn) hpos
      _ = (size l : ℝ) ^ τ * ζ' l u ω := by rw [← mul_assoc, hmul]
  exact lt_of_le_of_lt h1 hu

end RBM

namespace RBM.Gauss

/-- `η_t ≥ 0` for `t ≤ 1` (`(mE E).im = √(4-E²)/2 ≥ 0`). -/
theorem lwN_etaT_nonneg (E t : ℝ) (ht : t ≤ 1) : 0 ≤ etaT E t := by
  unfold etaT
  rw [mE_im]
  have : 0 ≤ Real.sqrt (4 - E ^ 2) / 2 := by positivity
  exact mul_nonneg (by linarith) this

end RBM.Gauss

/-! ## 2. Deterministic facts on `B`, `𝒯`, `wT` -/

namespace RBM

variable {d L : ℕ} {g t : ℝ}

/-- `⌊min(r, ℓ)⌋ = min(r, ⌊ℓ⌋)` for `r ∈ ℕ`. -/
private theorem lwN_floor_min (r : ℕ) (ℓ : ℝ) :
    ⌊min (r : ℝ) ℓ⌋₊ = min r ⌊ℓ⌋₊ := by
  rw [Monotone.map_min (Nat.floor_mono : Monotone (Nat.floor : ℝ → ℕ)), Nat.floor_natCast]

/-- `B_{t,⌊s⌋} ≤ 2^{d-2} B_{t,s}` (real argument `s ≥ 0`, `d ≥ 2`). -/
theorem lwN_BparamR_floor_le {s : ℝ} (hs : 0 ≤ s) :
    BparamR d L g t (⌊s⌋₊ : ℕ) ≤ 2 ^ (d - 2) * BparamR d L g t s := by
  unfold BparamR
  set k := d - 2 with hk
  have hm : (0 : ℝ) ≤ (⌊s⌋₊ : ℝ) := Nat.cast_nonneg _
  have hlt : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
  have h1 : (s + 1) ^ k ≤ (2 * ((⌊s⌋₊ : ℝ) + 1)) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  have h2 : ((2 * ((⌊s⌋₊ : ℝ) + 1)) ^ k)⁻¹ ≤ ((s + 1) ^ k)⁻¹ :=
    inv_anti₀ (pow_pos (by linarith) _) h1
  have h3 : (((⌊s⌋₊ : ℝ) + 1) ^ k)⁻¹ = 2 ^ k * ((2 * ((⌊s⌋₊ : ℝ) + 1)) ^ k)⁻¹ := by
    rw [mul_pow]; field_simp
  have hA : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  have hZ : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have e1 : (g ^ 2 + |1 - t|)⁻¹ * ((((⌊s⌋₊ : ℕ) : ℝ) + 1) ^ k)⁻¹ ≤
      2 ^ k * ((g ^ 2 + |1 - t|)⁻¹ * ((s + 1) ^ k)⁻¹) := by
    rw [h3]
    calc (g ^ 2 + |1 - t|)⁻¹ * (2 ^ k * ((2 * ((⌊s⌋₊ : ℝ) + 1)) ^ k)⁻¹)
        = 2 ^ k * ((g ^ 2 + |1 - t|)⁻¹ * ((2 * ((⌊s⌋₊ : ℝ) + 1)) ^ k)⁻¹) := by ring
      _ ≤ 2 ^ k * ((g ^ 2 + |1 - t|)⁻¹ * ((s + 1) ^ k)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hA) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right h2k hZ]

/-- `𝒯 ≤ B` (the exponential factor is `≤ 1`; no regime). -/
theorem lwN_tailT_le {r : ℝ} (hr : 0 ≤ r) : tailT d L g t r ≤ BparamR d L g t r := by
  unfold tailT
  have hB := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) hr
  have hle : Real.exp (-Real.sqrt (r / ellT L g t)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hle hB]

/-- **The comparison `wT ≤ B_{t, r∧K}`** (the premise `LWLoop2` of `lem:LWterm` for the B class from
`(LW_assm_exp)`): `r ∈ ℕ`, `r ≤ L`, `K = ⌊ℓ⌋ ∧ L`, `0 ≤ t < 1`, `W^{-D} ≤ L^{-d}`.  No regime. -/
theorem lwN_tailW_le {W ℓ D : ℝ} {K : ℕ} (r : ℕ) (hrL : r ≤ L) (hL : 0 < L) (hK : K = min ⌊ℓ⌋₊ L) (hℓ : 0 ≤ ℓ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hW : W ^ (-D) ≤ (((L : ℝ) ^ d))⁻¹) :
    tailW d L g t ℓ W D r ≤ Bparam d L g t (min r K) := by
  have hs0 : 0 ≤ min (r : ℝ) ℓ := le_min (Nat.cast_nonneg _) hℓ
  have hmin : min r K = ⌊min (r : ℝ) ℓ⌋₊ := by
    rw [lwN_floor_min, hK, ← min_assoc, min_eq_left ((min_le_left _ _).trans hrL)]
  unfold tailW
  refine max_le ?_ ?_
  · calc tailT d L g t (min (r : ℝ) ℓ) ≤ BparamR d L g t (min (r : ℝ) ℓ) := lwN_tailT_le hs0
      _ ≤ BparamR d L g t (⌊min (r : ℝ) ℓ⌋₊ : ℕ) :=
          BparamR_antitone (Nat.cast_nonneg _) (Nat.floor_le hs0)
      _ = Bparam d L g t (min r K) := by rw [BparamR_natCast, hmin]
  · have hu0 : 0 < |1 - t| := abs_pos.2 (by linarith)
    have hu1 : |1 - t| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
    have hLd : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (by exact_mod_cast hL) d
    have hinv : (((L : ℝ) ^ d))⁻¹ ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ :=
      inv_anti₀ (mul_pos hLd hu0) (mul_le_of_le_one_right hLd.le hu1)
    have hA : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ * ((((min r K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
      mul_nonneg (inv_nonneg.mpr (by positivity)) (inv_nonneg.mpr (pow_nonneg (by positivity) _))
    unfold Bparam
    linarith

/-- **The comparison `B_{t, r∧K} ≤ e 2^{d-2} wT`** in the regime `1 - t ≤ g²/L²` (`ℓ_t = L`, `7_8:20`):
`r ∈ ℕ`, `r ≤ L`, `K = ⌊ℓ⌋ ∧ L`, `g ≥ 0`, `0 ≤ t < 1`, `L ≥ 1`.  Constant `e · 2^{d-2}`. -/
theorem lwN_B_le_tail {W ℓ D : ℝ} {K : ℕ} (r : ℕ) (hrL : r ≤ L) (hK : K = min ⌊ℓ⌋₊ L) (hℓ : 0 ≤ ℓ)
    (hg : 0 ≤ g) (ht1 : t < 1) (hL : 1 ≤ (L : ℝ)) (hreg : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) :
    Bparam d L g t (min r K) ≤ (Real.exp 1 * 2 ^ (d - 2)) * tailW d L g t ℓ W D r := by
  have hs0 : 0 ≤ min (r : ℝ) ℓ := le_min (Nat.cast_nonneg _) hℓ
  have hsL : min (r : ℝ) ℓ ≤ L := (min_le_left _ _).trans (by exact_mod_cast hrL)
  have hmin : min r K = ⌊min (r : ℝ) ℓ⌋₊ := by
    rw [lwN_floor_min, hK, ← min_assoc, min_eq_left ((min_le_left _ _).trans hrL)]
  obtain ⟨h1, -⟩ := tailT_regime2_bounds (d := d) (L := L) hg ht1 hL hreg hs0 hsL
  have h2 : tailT d L g t (min (r : ℝ) ℓ) ≤ tailW d L g t ℓ W D r := le_max_left _ _
  have h3 := lwN_BparamR_floor_le (d := d) (L := L) (g := g) (t := t) hs0
  have hB : Bparam d L g t (min r K) ≤ 2 ^ (d - 2) * BparamR d L g t (min (r : ℝ) ℓ) := by
    rw [hmin, ← BparamR_natCast]; exact h3
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  have h4 : BparamR d L g t (min (r : ℝ) ℓ) ≤ Real.exp 1 * tailW d L g t ℓ W D r := by
    have h5 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos 1).le
    rw [← mul_assoc, he, one_mul] at h5
    exact h5
  calc Bparam d L g t (min r K) ≤ 2 ^ (d - 2) * BparamR d L g t (min (r : ℝ) ℓ) := hB
    _ ≤ 2 ^ (d - 2) * (Real.exp 1 * tailW d L g t ℓ W D r) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (Real.exp 1 * 2 ^ (d - 2)) * tailW d L g t ℓ W D r := by ring

end RBM

/-! ## 3. The size data and `W^{-1/𝔠} ≤ L^{-d}`

Copied from the merged `Induction/Step2Iterate.lean:1014-1175` (`ST_one_sub_lemT`, the upper half of
`ST_Bdata_holds`; commit of `main` at the branch point), with `ST_flow_im_pos`, `ST_size_pow_big` inlined:
these modules are not in the import closure of `LWPins`, and importing them would make a later import of
`LWtermExp` by `Step2Events`/`Step2Iterate` cyclic. -/

namespace RBM.Gauss.Sizes

open RBM

variable {d : ℕ} (sz : Sizes d)

private theorem lwN_flow_im_pos {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im := by
  have h := (hflow.2 n).2.1
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h

private theorem lwN_one_sub_lemT {z : ℂ} (hz : 0 < z.im) : z.im / (1 + ‖z‖) ≤ 1 - lemT z := by
  set m := msc z with hm
  have hr : 0 < ‖m‖ := norm_msc_pos hz
  have hI : 0 < m.im := msc_im_pos hz
  have hlt : ‖m‖ < 1 := norm_msc_lt_one hz
  have hN : Complex.normSq m = ‖m‖ ^ 2 := by rw [Complex.sq_norm]
  have him : m.im + z.im = m.im / ‖m‖ ^ 2 := by
    have := congrArg Complex.im (msc_add_eq_neg_inv hz)
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im] at this
    have h' : m.im + z.im = m.im / Complex.normSq m := by rw [← hm] at this; rw [this]; ring
    rwa [hN] at h'
  have hkey : z.im * ‖m‖ ^ 2 = m.im * (1 - ‖m‖ ^ 2) := by
    have h1 : (m.im + z.im) * ‖m‖ ^ 2 = m.im := by
      rw [him]; field_simp
    nlinarith [h1]
  have hIle : m.im ≤ ‖m‖ := Complex.im_le_norm m
  have h1 : z.im * ‖m‖ ^ 2 ≤ ‖m‖ * (1 - ‖m‖ ^ 2) := by
    rw [hkey]
    exact mul_le_mul_of_nonneg_right hIle (by nlinarith)
  have h2 : z.im * ‖m‖ ≤ 1 - ‖m‖ ^ 2 := by
    have : ‖m‖ * (z.im * ‖m‖) ≤ ‖m‖ * (1 - ‖m‖ ^ 2) := by nlinarith [h1]
    exact le_of_mul_le_mul_left this hr
  have h3 : (1 + ‖z‖)⁻¹ ≤ ‖m‖ := by
    have hg := lemT_ge hz
    rw [lemT, ← inv_pow] at hg
    exact (pow_le_pow_iff_left₀ (by positivity) hr.le two_ne_zero).1 hg
  calc z.im / (1 + ‖z‖) = z.im * (1 + ‖z‖)⁻¹ := div_eq_mul_inv _ _
    _ ≤ z.im * ‖m‖ := mul_le_mul_of_nonneg_left h3 hz.le
    _ ≤ 1 - ‖m‖ ^ 2 := h2
    _ = 1 - lemT z := by rw [lemT]

set_option maxHeartbeats 800000 in

-- The copied proof of `ST_Bdata_holds` (`Step2Iterate.lean:1048`) carries the same heartbeat limit.
set_option maxHeartbeats 800000 in
/-- **Size data, upper half of `STBdata`**: `W^{-d} B_{u,0} ≤ N^{-c}` for `0 ≤ u ≤ t_n ≤ lemT z_n`,
`c = min(2𝔡𝔠, ε)/2`, eventually. -/
theorem lwN_Bctl_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (htT : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-(min (2 * 𝔡 * 𝔠) ε / 2)) := by
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hc1 : 2 * c ≤ 2 * 𝔡 * 𝔠 := by rw [hcdef]; have := min_le_left (2 * 𝔡 * 𝔠) ε; linarith
  have hc2 : 2 * c ≤ ε := by rw [hcdef]; have := min_le_right (2 * 𝔡 * 𝔠) ε; linarith
  rw [← hcdef]
  have hbig : ∀ᶠ n in atTop, (5 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ c :=
    ((tendsto_rpow_atTop hc).comp (tendsto_natCast_atTop_iff.2 hsize)).eventually (eventually_ge_atTop 5)
  filter_upwards [hWO, hband, hbig,
    hsize.eventually (eventually_ge_atTop 1)] with n hwo hbn hN5 hN1 u hu0 hut
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have him := lwN_flow_im_pos sz hflow n
  have hlt1 : u < 1 := lt_of_le_of_lt (hut.trans (htT n)) (lemT_lt_one him)
  have hlam : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hwo.1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hz0 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  have hBp : Bparam d (sz.L n) (sz.lam n) u 0 =
      (sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    unfold Bparam
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - u)]
    simp
  have hBc : sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0 := rfl
  have hz3 : ‖z n‖ ≤ 3 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (z n)
    have h2 := (hflow.2 n).1
    have h3 := (hflow.2 n).2.2
    rw [abs_of_pos him] at h1
    linarith
  have hone := lwN_one_sub_lemT him
  have hu1 : (z n).im / 4 ≤ 1 - u := by
    have : (z n).im / 4 ≤ (z n).im / (1 + ‖z n‖) :=
      div_le_div_of_nonneg_left him.le (by positivity) (by linarith)
    have h2 : 1 - lemT (z n) ≤ 1 - u := by linarith [hut.trans (htT n)]
    linarith
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have hsz2 : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  -- `(N(1-u))⁻¹ ≤ 4 N^{-ε}`
  have hA : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
      4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ =
        (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
      rw [hsz2]; field_simp
    rw [h1]
    have hNε : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos hN0 _
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4 ≤ 1 - u := by linarith
    have h3 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) ≤
        ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_left h2 hN0.le
    have h4 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) =
        ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by
      have : ((sz.size n : ℕ) : ℝ) ^ ε = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
        conv_lhs => rw [show ε = 1 + (-1 + ε) by ring]
        rw [Real.rpow_add hN0, Real.rpow_one]
      rw [this]; ring
    rw [h4] at h3
    have h5 : 0 < ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by positivity
    calc (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ ε / 4)⁻¹ :=
          inv_anti₀ h5 h3
      _ = 4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
          rw [Real.rpow_neg hN0.le]; field_simp
  -- `(W^d lam²)⁻¹ ≤ W^{-2𝔡} ≤ N^{-2𝔡𝔠}`
  have hB : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
    have h1 := Sizes.lam_sq_mul_pow_ge sz n hwo.1
    have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ =
        (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_comm, mul_inv]
    rw [h2]
    have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    calc (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos hW _) h1
      _ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := (Real.rpow_neg hW.le _).symm
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(2 * 𝔡)) :=
          Real.rpow_le_rpow_of_nonpos hNc hbn (by linarith)
      _ = ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
  rw [hBc, hBp, mul_add]
  have hfirst : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith))
      (inv_nonneg.mpr hWd.le)
  have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
      4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by rw [mul_comm]; exact hA
  have hN2c : ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hNe : ((sz.size n : ℕ) : ℝ) ^ (-ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hsum : 5 * ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    have e : ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) =
        ((sz.size n : ℕ) : ℝ) ^ (-c) * ((sz.size n : ℕ) : ℝ) ^ (-c) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h5 : 5 * ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ 1 := by
      have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ c := Real.rpow_pos_of_pos hN0 _
      rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one hNc]
      linarith
    have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := Real.rpow_nonneg hN0.le _
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right h5 hp]
  linarith


/-- `N^{-c} ≤ W^{-(d c)}` (`N ≥ W^d`), copied from `ST_size_rpow_neg_le` (`Step2Events.lean:242`). -/
theorem lwN_size_rpow_neg_le (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h1 : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hL) d
    exact_mod_cast h
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have h2 := Real.rpow_le_rpow_of_nonpos hWd h1 (show -c ≤ 0 by linarith)
  calc ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ (-c) := h2
    _ = ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; congr 1; ring

/-- `W^{-1/𝔠} ≤ L^{-d}` eventually, from `(Main_DEL_COND)` `N^𝔠 ≤ W` and `N = (WL)^d ≥ L^d`. -/
theorem lwN_Wneg_le {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(1 / 𝔠)) ≤ ((((sz.L n : ℕ) : ℝ)) ^ d)⁻¹ := by
  filter_upwards [hband] with n hb
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (0 : ℝ) < (((sz.L n : ℕ) : ℝ)) ^ d :=
    pow_pos (by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)) d
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 := sz.size_rpow_le_W_rpow h𝔠 n hb (τ := 1) zero_le_one
  rw [Real.rpow_one] at h1
  have hsz2 : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hLN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hsz2]; nlinarith
  calc ((sz.W n : ℕ) : ℝ) ^ (-(1 / 𝔠)) = (((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠))⁻¹ := Real.rpow_neg hW.le _
    _ ≤ ((sz.size n : ℕ) : ℝ)⁻¹ := inv_anti₀ hN0 h1
    _ ≤ ((((sz.L n : ℕ) : ℝ)) ^ d)⁻¹ := inv_anti₀ hLd hLN

end RBM.Gauss.Sizes

/-! ## 4. The target -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- `W^{-d}` as the rpow of `LWPhiB` equals the natural-power inverse of `Bctl`. -/
private theorem lwN_wneg (W : ℝ) (hW : 0 ≤ W) (d : ℕ) : W ^ (-(d : ℝ)) = (W ^ d)⁻¹ := by
  rw [Real.rpow_neg hW, Real.rpow_natCast]

/-- `Φ_n(0) = Bctl^{1/2}` and `Φ_n(r)² = W^{-d} B_{t, r∧K}` for the B class with `c₀ = d`, `r ∈ ℕ`. -/
private theorem lwN_phi_zero {d : ℕ} (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) :
    LWPhiB sz (d : ℝ) K t n 0 = (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
  unfold LWPhiB Sizes.Bctl
  rw [lwN_wneg _ (Nat.cast_nonneg _)]
  simp

private theorem lwN_phi_sq {d : ℕ} (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n r : ℕ) :
    LWPhiB sz (d : ℝ) K t n (r : ℝ) ^ 2 =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) (min r (K n)) := by
  unfold LWPhiB
  rw [lwN_wneg _ (Nat.cast_nonneg _), Nat.floor_natCast, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt]
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
  unfold Bparam
  positivity

private theorem lwN_zdistInf_le {d : ℕ} (L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L x ≤ L := by
  refine Finset.sup_le fun i _ => ?_
  unfold zdist
  exact (min_le_left _ _).trans (ZMod.val_lt _).le

/-- **`lem: EWGn2_N`, second regime (`1 - t ≤ ĝ²/L²`), from `lem:LWterm`** (`7_8:20`, `3_5:385-415`):
`lem:LWterm` is applied to the B class `Φ = LWPhiB sz d K t`, `K n = ⌊ℓ_n⌋ ∧ L_n`, `c₀ = d`, at the window
`ε₁ = min(ε₀, d c/2)`, `c = min(2𝔡𝔠, ε)/2`, and the given `Ψ`; `LWLoop2` for `Φ` is `(LW_assm_exp)` at
`D' = 1/𝔠` (`wT ≤ B_{r∧K}`, `W^{-D'} ≤ L^{-d}`); the conclusion is compared with `tailW` on the regime
with the constant `e · 2^{d-2}` (`ℓ_t = L`).  Not the `tailW` class `Ψ² = W^{-d} 𝒯̃` of `7_8:20`
(paper-delta candidate `T2342a`). -/
theorem lwtermExpN_of_LWterm (d : ℕ) (hLW : LWterm d) : LWtermExpN d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  obtain ⟨hε₀, hwin, hinit, hℓ0, hℓt, hloop⟩ := hA
  have hd2 : 2 ≤ d := by omega
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  have him : ∀ n, 0 < (z n).im := lwN_flow_im_pos sz hflow
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (lemT_lt_one (him n))
  -- the constants
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min ε₀ ((d : ℝ) * c / 2) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]; exact lt_min hε₀ (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := by rw [hε₁def]; exact min_le_left _ _
  have hε₁b : 2 * ε₁ ≤ (d : ℝ) * c := by
    have : ε₁ ≤ (d : ℝ) * c / 2 := by rw [hε₁def]; exact min_le_right _ _
    linarith
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  have hL1 : ∀ n, (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := fun n =>
    Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
  -- data conditions of `LWClass_B`
  have hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (hWpos n) _) hn.1, hn.2⟩
  have ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1 :=
    Eventually.of_forall fun n => ⟨ht0 n, (ht1 n).le⟩
  have hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := by
    filter_upwards [lwN_Bctl_le sz hκ hε h𝔡 hflow htT] with n hn
    have h1 := hn (t n) (ht0 n) le_rfl
    rw [← hcdef] at h1
    have h2 := lwN_size_rpow_neg_le sz n hc.le
    have h3 : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) :=
      Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
    rw [lwN_wneg _ (Nat.cast_nonneg _)]
    exact (h1.trans h2).trans h3
  set K : ℕ → ℕ := fun n => min ⌊ℓ n⌋₊ (sz.L n) with hKdef
  obtain ⟨-, hcls, hrel⟩ := LWPhiB_psiAll sz hd2 (ε₀ := ε₁) (c₀ := (d : ℝ)) K t hε₁pos le_rfl hg ht hup
  -- the window and `(initialGT2)` at `ε₁ ≤ ε₀`
  have hwin' : LWWindow sz ε₁ Ψ := by
    filter_upwards [hwin] with n hn
    exact ⟨hn.1, hn.2.trans (Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith))⟩
  have hinit' : LWInit sz (STflowE z) t ε₁ Ψ := by
    refine ⟨?_, hinit.2⟩
    refine lwN_prec_mono hsize (c := 1) ?_ hinit.1
    exact Eventually.of_forall fun n u ω => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
      by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)⟩
  -- `LWLoop2` for the B class from `(LW_assm_exp)` at `D' = 1/𝔠`
  have hD' : 0 < 1 / 𝔠 := by positivity
  have hL2 : LWLoop2 sz (STflowE z) t (LWPhiB sz (d : ℝ) K t) := by
    refine lwN_prec_mono hsize (c := 1) ?_ (hloop (1 / 𝔠) hD')
    filter_upwards [lwN_Wneg_le sz h𝔠 hband] with n hn
    rintro ⟨σ, a, b⟩ ω
    simp only
    have hLn : (zdistInf d (sz.L n) (a - b) : ℕ) ≤ sz.L n := lwN_zdistInf_le _ _
    rw [lwN_phi_sq, one_mul]
    refine ⟨mul_nonneg (inv_nonneg.mpr (by positivity)) ?_, ?_⟩
    · unfold Bparam; positivity
    · refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
      exact lwN_tailW_le (L := sz.L n) _ hLn (by have := sz.three_le_L n; omega) rfl (hℓ0 n)
        (ht0 n) (ht1 n) hn
  have hmain := hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₁ _ _ _ _ Ψ (LWPhiB sz (d : ℝ) K t)
    ⟨hε₁pos, hwin', hinit', hcls, hrel, hL2⟩
  -- restrict to the regime subtype and compare
  have h1 := StochDomAt.precomp_param hmain
    (fun n (v : {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
      1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2} ) => v.1)
  refine lwN_prec_mono hsize (c := Real.exp 1 * 2 ^ (d - 2)) ?_ h1
  filter_upwards [hg] with n hgn
  rintro ⟨⟨σ, a⟩, hreg⟩ ω
  simp only
  have hLn : (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) ≤ sz.L n := lwN_zdistInf_le _ _
  have hη : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := inv_nonneg.mpr (lwN_etaT_nonneg _ _ (ht1 n).le)
  have hS : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by
    unfold Sizes.Bctl Bparam; positivity) _
  have hTW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
      ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (tailW_pos (hWpos n) _).le
  refine ⟨mul_nonneg (mul_nonneg hη hS) hTW, ?_⟩
  rw [lwN_phi_zero, lwN_phi_sq]
  have hB := lwN_B_le_tail (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
    (zdistInf d (sz.L n) (a 0 - a 1)) hLn rfl (hℓ0 n) hgn.1.le (ht1 n) (hL1 n) hreg
  calc (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n)
          (min (zdistInf d (sz.L n) (a 0 - a 1)) (K n)))
      ≤ (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((Real.exp 1 * 2 ^ (d - 2)) *
          tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D
            ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr (by positivity)))
          (mul_nonneg hη hS)
    _ = (Real.exp 1 * 2 ^ (d - 2)) * ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
          ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))) := by ring

end RBM.Gauss.Sizes

/-! ## 5. Compiled nonempty instance at `d = 3`

The merged `RBM.Gauss.LWInst.inst_LWtermExpN` (`Graph/LWPins.lean:783`; merged `sz0`: `L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `z_n = 1/2 + i N_n^{-4/5}`,
`t = tEnd = lemT z_n`, `ε₀ = 1/20`, `ℓ = ℓ_{t₀}`), with its hypothesis `LWtermExpN 3` replaced by
`LWterm 3` through `lwtermExpN_of_LWterm`.  The hypotheses `LWterm 3` (LW-01), `LWInit` and `LWLoopExp`
(`(initialGT2)`, `(LW_assm_exp)`) are other gates' pins and stay hypotheses; every deterministic
hypothesis (the flow, `0 ≤ t ≤ lemT z`, `LWWindow`, `ℓ ≥ 0`, `ℓ ≤ (log W)^{10} ℓ_t`, `D > 0`) is
discharged at the data.  The regime `1 - t ≤ ĝ²/L²` is the one that holds at `t₀` (`T2040-prove.md`
b.7: `n = 0, 5, 500`), so the index set is nonempty. -/

namespace RBM.Gauss.LWTermExpNInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.LWInst

/-- **`lem: EWGn2_N`, second regime, from `lem:LWterm`, instantiated** (`d = 3`, merged data). -/
theorem inst_lwtermExpN_of_LWterm (h : LWterm 3)
    (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        1 - tEnd n ≤ sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2})
      (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tEnd n) p.1.1 p.1.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tEnd n))⁻¹ * (sz0.Bctl n (tEnd n)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tEnd n) (ℓT tEnd n)
          ((sz0.W n : ℕ) : ℝ) D ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) :=
  inst_LWtermExpN (lwtermExpN_of_LWterm 3 h) hI hL D hD

end RBM.Gauss.LWTermExpNInst
