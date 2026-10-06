/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.FixedZ
import RBM3D.Induction.ContinuityNet

/-!
# MA-04: the `z`-net `[net]` (Theorems 2.2, 2.5, assembly)

Ticket T2230 (MA-04 of the T2192 assembly split).  The header docstring and the two pins `MANetLoc`,
`MANetQD` are copied verbatim from the compiled probe `RBM3D/Probe/T2192Pins.lean` at `97d958e`
(branch `t/T2192`, never merged, lines `2031-2046`); the probe namespace `RBM.Probe.T2192` becomes
`RBM.Endpoints`.  Both pins are proved here (`netLoc : MANetLoc`, `netQD : MANetQD`); the
intermediate statements are new mathematics, uncompiled in the probe.

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`): Theorem 2.2
(`1_2:386-395`), Theorem 2.5 (`1_2:488-511`), and the net, "a standard net argument" after the
fixed-`z` estimates (`1_2:1226-1228`).

* **The net is deterministic** (`zNet_exists`): the product of two 1D grids of mesh `N^{-7}` on
  `[-(2-κ), 2-κ]` and `[N^{-1+ε}, 1]` (the points `lo + k h`, `k ≤ ⌊(hi - lo)/h⌋`; no port from
  RBM1D/RBM2D), at most `(4N^7 + 1)(N^7 + 1) ≤ 25 N^{14}` points, all inside `𝐃_{κ,ε}`; empty
  when `𝐃_{κ,ε}` is.
* **No random control** (`Gn_entry_le`, `Gn_entry_lip`, `profPM_lip`, `profPP_lip`): for every `ω`
  (`seqXmat` is Hermitian) the entries of the resolvent are `η⁻¹`-bounded and `η⁻²`-Lipschitz in
  `z` on `Im z ≥ η` (`cont_green_diff` at `H = H'`), `msc` is `η⁻²`-Lipschitz (`msc_lip`:
  `m(z) - m(z') = (z - z')/((m+z)(m'+z') - 1)`), the profiles `profPM`, `profPP` are
  `12 η⁻⁴`-Lipschitz on `η ≤ Im z ≤ 1` (`‖Θ_ξ‖ ≤ (1-|ξ|)⁻¹ ≤ 2/η` by `norm_Theta_le` and
  `one_sub_lemT_ge`: `1 - |m|² ≥ Im z/(1 + Im z)`; `Theta_sub_Theta`, `norm_SB`); the block
  average does not increase a uniform entrywise bound (`avg2_lip`).
* **The cover lemmas** (`locBad1_net`, `locBad2_net`, `qd1Bad_net`, `qd2Bad_net`): for `32 ≤ N`,
  `5 ≤ W^{τ/2}`, `ε > 0` and any `S` with the two properties of `zNet_exists`, every `ω` in the bad
  event at `τ` lies in the per-point bad event at `τ/2` of some `w ∈ S`: `η_z, η_w ≥ N^{-1+ε} ≥
  N^{-1}`, `‖z - w‖ ≤ 2 N^{-7}`, entry error `≤ 4 N^{-5}`, profile error `≤ 4 N^{-4} + 24 N^{-3} ≤
  N^{-2}`, `4s + 1 ≤ s²` for `s = W^{τ/2} ≥ 5`.
* **`netLoc`, `netQD`**: `locSCFixed` resp. `QDiffFixed` at `(κ, ε, τ/2, D + 15)` for the
  probability halves, the union bound `net_union_le`, the count `net_count` (`25 N^{14} N^{-(D+15)}
  ≤ N^{-D}` for `N ≥ 25`); the expectation half of `QDiff` is the one of `QDiffFixed` at
  `(κ, ε, τ, D)` (already pointwise in `z`, no lift).
* **§64 (4) statement (the net is a grid lift)**: lifted are only the three right sides
  `W^τ 𝓑_{η,distB}` (`(G_bound)`), `W^τ 𝓑_{η,0}` (`(G_bound_ave)`), `qdBound τ η a b`
  (`(eq:diffu1,2)`): **deterministic** functions of `(n, Im z, a, b)`, relatively continuous in `η`
  (`calB_shift_le`: factor `≤ 2`, resp. `≤ 4` for `qdBound`, under `|η' - η| ≤ η/2`) with
  polynomial **floors** `𝓑 ≥ (Nη)⁻¹ ≥ N⁻¹` (`inv_size_mul_le_calB`) and
  `min(𝓑_0^{1/5} 𝓑_K, 𝓑_0²) ≥ N⁻²`.  The random left sides (`G_xy - M_xy`, the block averages)
  move under `z → w` by a **deterministic** amount for every `ω`.  No per-time clause with a
  floorless random right side is lifted; the expectation half of `QDiff` is not lifted at all.
* Consumers: MA-06 (`band_endpoints_of_pins`: `hNL : MANetLoc`, `hNQ : MANetQD`, with
  `fixed_of_ML`); through `locSC`: `decol_of_locSC` (MA-03), `locSC_to_UNLocAvgBand`
  (`Endpoints.lean`), hence `UNLocAvgBand` (UN); through `QDiff`: MA-05.
* Registry (DECISIONS §16, §20): `locSC`, `QDiff` stay owed (MA-04 proves `locSCFixed → locSC`,
  `QDiffFixed → QDiff`, not `locSC`, `QDiff`); the event predicates `locBad2`, `qd1Bad`, `qd2Bad`,
  hypotheses of the deterministic cover lemmas, are structural (`RBM3D/Test/Axioms.lean`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints

/-! ### (c′) The `z`-net `[net]` (`1_2:1228`): the pins `MANetLoc`, `MANetQD` (owed by MA-04)

The net needs no probability in the direct parametrization (preflight row 6): for Hermitian `H` and
`η, η' ≥ η_min`, `‖G(z) - G(z')‖ ≤ |z - z'| η_min⁻²` (merged `cont_green_diff`, `Induction/ContinuityNet.lean:448`, at
`H = H'`), `|m(z) - m(z')| ≤ |z - z'| η⁻¹ η'⁻¹` (`msc_eq_integral`), `‖Θ_ξ‖ ≤ (1-|ξ|)⁻¹ ≤ 2/η` (`|ξ| = t₀`, `zRange`),
`𝓑_{η',K} ∈ [1/2, 2] 𝓑_{η,K}` for `|η - η'| ≤ η/2`, and the floor `𝓑 ≥ (Nη)⁻¹ ≥ N⁻¹` (`inv_size_mul_le_calB`).  With mesh `N^{-7}`
the net error is `≤ N^{-3} ≤ N^{-2}/2`, the cardinality `≤ 25 N^{14}`; the per-point probability is the one of
`locSCFixed` at `D + 15`, `τ/2`.  RBM2D's `RegionUnif` (`RBM2D/Main/RegionUnif.lean`, 950 lines) survives only as the abstract
core `regionUnif_core` (`:111`, union bound over a finite net: the merged `stochDomAt_of_perTimeDomAt`); the Gaussian
good event `contGood` (`H_t = √t X` is unbounded) and the `(E, t)`-net are not needed. -/

/-- **Pin `MANetLoc`**: `locSC` from its fixed-`z` form. -/
def MANetLoc : Prop := locSCFixed → locSC

/-- **Pin `MANetQD`**: `QDiff` from its fixed-`z` form (the expectation half is already pointwise). -/
def MANetQD : Prop := QDiffFixed → QDiff

/-! ### The union bound over a finite net and the count -/

/-- **The union bound over a finite net** (any measure, no measurability): `P A ≤ #S · p` when `A ⊆ ⋃_{i ∈ S} B_i`
and `P (B_i) ≤ p` for `i ∈ S`. -/
theorem net_union_le {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Finset ι) (A : Set Ω)
    (B : ι → Set Ω) (p : ℝ≥0∞) (hA : A ⊆ ⋃ i ∈ S, B i) (hB : ∀ i ∈ S, P (B i) ≤ p) :
    P A ≤ (S.card : ℝ≥0∞) * p := by
  calc P A ≤ P (⋃ i ∈ S, B i) := measure_mono hA
    _ ≤ ∑ i ∈ S, P (B i) := measure_biUnion_finset_le S B
    _ ≤ ∑ _i ∈ S, p := Finset.sum_le_sum hB
    _ = (S.card : ℝ≥0∞) * p := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The count**: at most `25 N^{14}` net points of probability `N^{-(D+15)}` each have total mass `≤ N^{-D}`
for `N ≥ 25`. -/
theorem net_count {N D : ℝ} (c : ℕ) (hN : 25 ≤ N) (hc : (c : ℝ) ≤ 25 * N ^ (14 : ℕ)) :
    (c : ℝ≥0∞) * ENNReal.ofReal (N ^ (-(D + 15))) ≤ ENNReal.ofReal (N ^ (-D)) := by
  have hN0 : 0 < N := by linarith
  have hexp : N ^ (14 : ℕ) * N ^ (-(D + 15)) = N ^ (-D) * N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0,
      show ((14 : ℕ) : ℝ) + -(D + 15) = -D + (-1) by push_cast; ring, Real.rpow_add hN0, Real.rpow_neg_one]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : (c : ℝ) * N ^ (-(D + 15)) ≤ 25 * N ^ (14 : ℕ) * N ^ (-(D + 15)) :=
    mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN0.le _)
  have h2 : 25 * N ^ (14 : ℕ) * N ^ (-(D + 15)) = 25 * (N ^ (-D) * N⁻¹) := by rw [mul_assoc, hexp]
  have h3 : 25 * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  have h4 : 0 ≤ N ^ (-D) := Real.rpow_nonneg hN0.le _
  nlinarith

/-! ### Scalar facts -/

private theorem znet_W_pos {d : ℕ} (sz : Sizes d) (n : ℕ) : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

/-- **Relative continuity of `𝓑_{η,K}` in `η`**: `𝓑_{η',K} ≤ 2 𝓑_{η,K}` for `|η' - η| ≤ η/2`, `K ≥ 0`. -/
theorem calB_shift_le {d : ℕ} (sz : Sizes d) (n : ℕ) {η η' K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    (h : |η' - η| ≤ η / 2) : calB sz n η' K ≤ 2 * calB sz n η K := by
  have hη' : η / 2 ≤ η' := by have := (abs_le.mp h).1; linarith
  have hη'0 : 0 < η' := by linarith
  have hW := znet_W_pos sz n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast one_le_size sz n
  have hlam : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have hA : 0 < ((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) := by
    have : 0 < K + ((sz.W n : ℕ) : ℝ) := by linarith
    positivity
  have h1 : (sz.lam n ^ 2 + η')⁻¹ ≤ 2 * (sz.lam n ^ 2 + η)⁻¹ := by
    have : ((sz.lam n ^ 2 + η) / 2)⁻¹ = 2 * (sz.lam n ^ 2 + η)⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [← this]
    exact inv_anti₀ (by positivity) (by linarith)
  have h2 : (((sz.size n : ℕ) : ℝ) * η')⁻¹ ≤ 2 * (((sz.size n : ℕ) : ℝ) * η)⁻¹ := by
    have : (((sz.size n : ℕ) : ℝ) * η / 2)⁻¹ = 2 * (((sz.size n : ℕ) : ℝ) * η)⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [← this]
    exact inv_anti₀ (by positivity) (by nlinarith)
  unfold calB
  have h3 : (sz.lam n ^ 2 + η')⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) ≤
      2 * ((sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2))) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h1 hA.le
  linarith

/-- `1 - |m|² ≥ Im z/(1 + Im z)` for `Im z > 0`: from `|m|² (Im m + Im z) = Im m` (`msc_mul`) and `Im m < 1`. -/
theorem one_sub_lemT_ge {z : ℂ} (hz : 0 < z.im) : z.im / (1 + z.im) ≤ 1 - lemT z := by
  have hm := msc_mul z
  have him := msc_im_pos hz
  have hlt := norm_msc_lt_one hz
  have hT : lemT z = Complex.normSq (msc z) := by unfold lemT; rw [Complex.sq_norm]
  rw [hT]
  set m := msc z with hm_def
  have hm0 : m ≠ 0 := by
    intro h; rw [h, Complex.zero_im] at him; exact lt_irrefl _ him
  have hinv : m + z = -m⁻¹ := by
    field_simp
    linear_combination hm
  have hN : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm0
  have key : (m.im + z.im) * Complex.normSq m = m.im := by
    have := congrArg Complex.im hinv
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at this
    rw [this]
    field_simp
  have himlt : m.im < 1 := lt_of_le_of_lt (Complex.im_le_norm m) hlt
  have hN1 : Complex.normSq m < 1 := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hN1.le) (sub_nonneg.2 himlt.le)]

private theorem znet_norm_mul_sub_one_ge {q q' : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : a ≤ q.im) (hq' : b ≤ q'.im) : a * b ≤ ‖q * q' - 1‖ := by
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hq; simp at hq; linarith
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hqa : a ≤ ‖q‖ := le_trans hq (Complex.im_le_norm q)
  have hw : ‖q‖ ^ 2 * b ≤ ‖(q * q' - 1) * (starRingEnd ℂ) q‖ := by
    have him : ((q * q' - 1) * (starRingEnd ℂ) q).im = Complex.normSq q * q'.im + q.im := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.one_re,
        Complex.one_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
      ring
    calc ‖q‖ ^ 2 * b ≤ Complex.normSq q * q'.im + q.im := by
          rw [Complex.sq_norm]
          nlinarith [Complex.normSq_nonneg q]
      _ = ((q * q' - 1) * (starRingEnd ℂ) q).im := him.symm
      _ ≤ ‖(q * q' - 1) * (starRingEnd ℂ) q‖ := Complex.im_le_norm _
  rw [norm_mul, Complex.norm_conj] at hw
  have h2 : ‖q‖ * b ≤ ‖q * q' - 1‖ := by
    have : ‖q‖ * b * ‖q‖ ≤ ‖q * q' - 1‖ * ‖q‖ := by nlinarith
    exact le_of_mul_le_mul_right this hqn
  nlinarith

/-- **`m` is `η⁻²`-Lipschitz on `Im z, Im z' ≥ η`**: `z - z' = (m - m') ((m + z)(m' + z') - 1)` (`msc_mul`) and
`|q q' - 1| ≥ Im q Im q'` for `Im q, Im q' > 0`, `q = m + z`, `q' = m' + z'`, `Im q ≥ Im z`. -/
theorem msc_lip {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz' : η ≤ z'.im) :
    ‖msc z - msc z'‖ ≤ η⁻¹ * η⁻¹ * ‖z - z'‖ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη hz
  have hz0' : 0 < z'.im := lt_of_lt_of_le hη hz'
  have h1 := msc_mul z
  have h2 := msc_mul z'
  have himm := msc_im_pos hz0
  have himm' := msc_im_pos hz0'
  set m := msc z with hm_def
  set m' := msc z' with hm'_def
  have hid : (m - m') * ((m + z) * (m' + z') - 1) = z - z' := by
    linear_combination (m' + z') * h1 - (m + z) * h2
  have hq : η ≤ (m + z).im := by rw [Complex.add_im]; linarith
  have hq' : η ≤ (m' + z').im := by rw [Complex.add_im]; linarith
  have hge := znet_norm_mul_sub_one_ge hη hη hq hq'
  have hnorm : ‖z - z'‖ = ‖m - m'‖ * ‖(m + z) * (m' + z') - 1‖ := by rw [← hid, norm_mul]
  have hη2 : 0 < η * η := mul_pos hη hη
  have : ‖m - m'‖ * (η * η) ≤ ‖z - z'‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hge (norm_nonneg _)
  rw [← mul_inv, ← div_eq_inv_mul, le_div_iff₀ hη2]
  exact this


/-! ### The 2D grid of mesh `N^{-7}` inside `𝐃_{κ,ε}` -/

private theorem znet_grid1 (lo hi h : ℝ) (hh : 0 < h) (hlo : lo ≤ hi) :
    ∃ T : Finset ℝ, (T.card : ℝ) ≤ (hi - lo) / h + 1 ∧ (∀ p ∈ T, lo ≤ p ∧ p ≤ hi) ∧
      ∀ x : ℝ, lo ≤ x → x ≤ hi → ∃ p ∈ T, |x - p| ≤ h := by
  set K : ℕ := ⌊(hi - lo) / h⌋₊ with hK
  have hK0 : 0 ≤ (hi - lo) / h := div_nonneg (by linarith) hh.le
  have hKle : (K : ℝ) ≤ (hi - lo) / h := Nat.floor_le hK0
  refine ⟨(Finset.range (K + 1)).image (fun k : ℕ => lo + (k : ℝ) * h), ?_, ?_, ?_⟩
  · calc (((Finset.range (K + 1)).image (fun k : ℕ => lo + (k : ℝ) * h)).card : ℝ)
        ≤ ((Finset.range (K + 1)).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (K : ℝ) + 1 := by simp
      _ ≤ (hi - lo) / h + 1 := by linarith
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    have hk' : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have : (k : ℝ) * h ≤ hi - lo := by
      have := mul_le_mul_of_nonneg_right (hk'.trans hKle) hh.le
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    refine ⟨by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], by linarith⟩
  · intro x hx1 hx2
    set k : ℕ := ⌊(x - lo) / h⌋₊ with hk
    have hx0 : 0 ≤ (x - lo) / h := div_nonneg (by linarith) hh.le
    have hkle : (k : ℝ) ≤ (x - lo) / h := Nat.floor_le hx0
    have hklt : (x - lo) / h < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkK : k ≤ K := Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
    refine ⟨lo + (k : ℝ) * h, Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hkK), rfl⟩, ?_⟩
    have h1 : (k : ℝ) * h ≤ x - lo := by
      have := mul_le_mul_of_nonneg_right hkle hh.le
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    have h2 : x - lo < ((k : ℝ) + 1) * h := by
      have := mul_lt_mul_of_pos_right hklt hh
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    rw [abs_of_nonneg (by linarith)]
    nlinarith

private theorem znet_rpow_neg7 {N : ℝ} (hN : 0 < N) : (N ^ (-7 : ℝ))⁻¹ = N ^ (7 : ℕ) := by
  rw [Real.rpow_neg hN.le, inv_inv]
  exact_mod_cast Real.rpow_natCast N 7

/-- **The deterministic net**: for `κ > 0` a finite set `S` of at most `25 N^{14}` points of `𝐃_{κ,ε}` (`N = (W L)^d`)
such that every `z ∈ 𝐃_{κ,ε}` has a point of `S` within `N^{-7}` in the real and in the imaginary part (empty when
`𝐃_{κ,ε}` is). -/
theorem zNet_exists {d : ℕ} (sz : Sizes d) {κ ε : ℝ} (hκ : 0 < κ) (n : ℕ) : ∃ S : Finset ℂ,
    (S.card : ℝ) ≤ 25 * Nsz sz n ^ (14 : ℕ) ∧ (∀ w ∈ S, sz.locDomain κ ε n w) ∧
    ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ) := by
  have hN0 : 0 < Nsz sz n := Nsz_pos sz n
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast one_le_size sz n
  have hh0 : 0 < Nsz sz n ^ (-7 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hhinv : (Nsz sz n ^ (-7 : ℝ))⁻¹ = Nsz sz n ^ (7 : ℕ) := znet_rpow_neg7 hN0
  have hN7 : (1 : ℝ) ≤ Nsz sz n ^ (7 : ℕ) := one_le_pow₀ hN1
  by_cases hne : 0 ≤ 2 - κ ∧ Nsz sz n ^ (-1 + ε) ≤ 1
  · obtain ⟨T₁, hc₁, hT₁, hcov₁⟩ := znet_grid1 (-(2 - κ)) (2 - κ) (Nsz sz n ^ (-7 : ℝ)) hh0 (by linarith [hne.1])
    obtain ⟨T₂, hc₂, hT₂, hcov₂⟩ := znet_grid1 (Nsz sz n ^ (-1 + ε)) 1 (Nsz sz n ^ (-7 : ℝ)) hh0 hne.2
    refine ⟨(T₁ ×ˢ T₂).image (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)), ?_, ?_, ?_⟩
    · have hcard : (((T₁ ×ˢ T₂).image (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))).card : ℝ) ≤
          (T₁.card : ℝ) * (T₂.card : ℝ) := by
        have : ((T₁ ×ˢ T₂).image (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))).card ≤ T₁.card * T₂.card :=
          Finset.card_image_le.trans (by rw [Finset.card_product])
        exact_mod_cast this
      have e1 : (T₁.card : ℝ) ≤ 4 * Nsz sz n ^ (7 : ℕ) + 1 := by
        refine hc₁.trans ?_
        rw [div_eq_mul_inv, hhinv]
        nlinarith [mul_pos hκ (by linarith : 0 < Nsz sz n ^ (7 : ℕ))]
      have e2 : (T₂.card : ℝ) ≤ Nsz sz n ^ (7 : ℕ) + 1 := by
        refine hc₂.trans ?_
        rw [div_eq_mul_inv, hhinv]
        have : 0 ≤ Nsz sz n ^ (-1 + ε) := Real.rpow_nonneg hN0.le _
        nlinarith [mul_nonneg this (by linarith : 0 ≤ Nsz sz n ^ (7 : ℕ))]
      calc _ ≤ (T₁.card : ℝ) * T₂.card := hcard
        _ ≤ (4 * Nsz sz n ^ (7 : ℕ) + 1) * (Nsz sz n ^ (7 : ℕ) + 1) :=
            mul_le_mul e1 e2 (Nat.cast_nonneg _) (by positivity)
        _ ≤ 25 * Nsz sz n ^ (14 : ℕ) := by
            have : Nsz sz n ^ (14 : ℕ) = Nsz sz n ^ (7 : ℕ) * Nsz sz n ^ (7 : ℕ) := by rw [← pow_add]
            rw [this]; nlinarith
    · intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨a1, a2⟩ := hT₁ _ hp1
      obtain ⟨b1, b2⟩ := hT₂ _ hp2
      exact ⟨abs_le.2 ⟨by simpa using a1, by simpa using a2⟩, b1, b2⟩
    · intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      obtain ⟨p₁, hp₁, hd₁⟩ := hcov₁ z.re (by linarith [(abs_le.1 hz1).1]) (by linarith [(abs_le.1 hz1).2])
      obtain ⟨p₂, hp₂, hd₂⟩ := hcov₂ z.im hz2 hz3
      exact ⟨⟨p₁, p₂⟩, Finset.mem_image.2 ⟨(p₁, p₂), Finset.mem_product.2 ⟨hp₁, hp₂⟩, rfl⟩, hd₁, hd₂⟩
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro z hz
    exfalso
    apply hne
    refine ⟨by linarith [(abs_le.1 hz.1).1, (abs_le.1 hz.1).2], le_trans hz.2.1 hz.2.2⟩

/-! ### The resolvent entries and the block average, for every `ω` -/

section Resolvent

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **`|G_{xy}(z)| ≤ η⁻¹`** on `Im z ≥ η`, for every `ω` (`seqXmat` is Hermitian). -/
theorem Gn_entry_le (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖sz.Gn n z ω x y‖ ≤ η⁻¹ := by
  have hH := Sizes.seqXmat_isHermitian sz n ω
  have h1 := RBM.Ind.ContinuityNet.cont_norm_green_le hH hη (le_trans hz (le_abs_self _))
  have h2 := norm_matrix_entry_le_opNorm (green (sz.seqXmat n ω) z) x y
  have hG : sz.Gn n z ω = green (sz.seqXmat n ω) z := RBM.Ind.ContinuityNet.cont_Gres_true_eq_green _ _
  rw [hG]
  exact h2.trans h1

/-- **`|G_{xy}(z) - G_{xy}(z')| ≤ η⁻² |z - z'|`** on `Im z, Im z' ≥ η`, for every `ω` (`cont_green_diff` at `H = H'`). -/
theorem Gn_entry_lip (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im)
    (hz' : η ≤ z'.im) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖sz.Gn n z ω x y - sz.Gn n z' ω x y‖ ≤ η⁻¹ * η⁻¹ * ‖z - z'‖ := by
  have hH := Sizes.seqXmat_isHermitian sz n ω
  have h1 := RBM.Ind.ContinuityNet.cont_green_diff hH hH hη (le_trans hz (le_abs_self _))
    (le_trans hz' (le_abs_self _))
  rw [sub_self, norm_zero, zero_add] at h1
  have h2 := norm_matrix_entry_le_opNorm (green (sz.seqXmat n ω) z - green (sz.seqXmat n ω) z') x y
  rw [Matrix.sub_apply] at h2
  have hG : ∀ w, sz.Gn n w ω = green (sz.seqXmat n ω) w := fun w =>
    RBM.Ind.ContinuityNet.cont_Gres_true_eq_green _ _
  rw [hG z, hG z']
  exact h2.trans h1

end Resolvent

/-- The block average does not increase a uniform entrywise bound. -/
theorem avg2_lip {d : ℕ} (sz : Sizes d) (n : ℕ)
    (F F' : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) {c : ℝ}
    (h : ∀ x y, ‖F x y - F' x y‖ ≤ c) (a b : Zd d (sz.L n)) :
    ‖avg2 sz n F a b - avg2 sz n F' a b‖ ≤ c := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (znet_W_pos sz n) d
  have hcard1 : ((Iblk d (sz.L n) (sz.W n) a).card : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [card_Iblk]; push_cast; rfl
  have hcard2 : ((Iblk d (sz.L n) (sz.W n) b).card : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [card_Iblk]; push_cast; rfl
  have hsum : ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, (F x y - F' x y)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * c) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => h x y)).trans (le_of_eq ?_)
    simp only [Finset.sum_const, nsmul_eq_mul, hcard1, hcard2]
  have hk : ‖((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹‖ = ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, norm_pow, Complex.norm_natCast]
  unfold avg2
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [norm_mul, hk]
  calc ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2)⁻¹ * ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, (F x y - F' x y)‖
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * c)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = c := by field_simp

/-! ### Lipschitz bounds of the deterministic profiles -/

section Profile

open scoped Matrix.Norms.Operator

variable {d : ℕ}

private theorem znet_entry_le_linfty {L : ℕ} [NeZero L] (A : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) :
    ‖A a b‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A a b‖₊ ≤ ∑ j, ‖A a j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖A a j‖₊) (fun _ _ => zero_le) (Finset.mem_univ b)
  have h2 : ∑ j, ‖A a j‖₊ ≤ Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ a)
  exact_mod_cast h1.trans h2

private theorem znet_prof_core {L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {ξ ξ' : ℂ} (hξ : ‖ξ‖ < 1)
    (hξ' : ‖ξ'‖ < 1) {B : ℝ} (hB : ‖Theta d L g ξ‖ ≤ B) (hB' : ‖Theta d L g ξ'‖ ≤ B) (a b : Zd d L) :
    ‖ξ * Theta d L g ξ a b - ξ' * Theta d L g ξ' a b‖ ≤ ‖ξ - ξ'‖ * (B + B * B) := by
  have hS := norm_SB d L g hL
  have hdiff := Theta_sub_Theta d L g hS hξ' hξ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
  have hentry : ξ * Theta d L g ξ a b - ξ' * Theta d L g ξ' a b =
      (ξ - ξ') * Theta d L g ξ a b +
        ξ' * ((ξ - ξ') * (Theta d L g ξ * SB d L g * Theta d L g ξ') a b) := by
    have h := congrFun (congrFun hdiff a) b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    linear_combination ξ' * h
  have hP : ‖(Theta d L g ξ * SB d L g * Theta d L g ξ') a b‖ ≤ B * B := by
    refine (znet_entry_le_linfty _ a b).trans ?_
    calc ‖Theta d L g ξ * SB d L g * Theta d L g ξ'‖
        ≤ ‖Theta d L g ξ * SB d L g‖ * ‖Theta d L g ξ'‖ := norm_mul_le _ _
      _ ≤ (‖Theta d L g ξ‖ * ‖SB d L g‖) * ‖Theta d L g ξ'‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖Theta d L g ξ‖ * ‖Theta d L g ξ'‖ := by rw [hS, mul_one]
      _ ≤ B * B := mul_le_mul hB hB' (norm_nonneg _) hB0
  have hT : ‖Theta d L g ξ a b‖ ≤ B := (znet_entry_le_linfty _ a b).trans hB
  rw [hentry]
  calc ‖(ξ - ξ') * Theta d L g ξ a b +
        ξ' * ((ξ - ξ') * (Theta d L g ξ * SB d L g * Theta d L g ξ') a b)‖
      ≤ ‖(ξ - ξ') * Theta d L g ξ a b‖ +
        ‖ξ' * ((ξ - ξ') * (Theta d L g ξ * SB d L g * Theta d L g ξ') a b)‖ := norm_add_le _ _
    _ = ‖ξ - ξ'‖ * ‖Theta d L g ξ a b‖ +
        ‖ξ'‖ * (‖ξ - ξ'‖ * ‖(Theta d L g ξ * SB d L g * Theta d L g ξ') a b‖) := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ ‖ξ - ξ'‖ * B + 1 * (‖ξ - ξ'‖ * (B * B)) := by
        gcongr
    _ = ‖ξ - ξ'‖ * (B + B * B) := by ring

private theorem znet_div_Wd (sz : Sizes d) (n : ℕ) (A A' : ℂ) :
    ‖A / ((sz.W n : ℕ) : ℂ) ^ d - A' / ((sz.W n : ℕ) : ℂ) ^ d‖ ≤ ‖A - A'‖ := by
  rw [← sub_div, norm_div, norm_pow, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  exact div_le_self (norm_nonneg _) h1

private theorem znet_one_sub_ge {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz1 : z.im ≤ 1) :
    η / 2 ≤ 1 - ‖msc z‖ ^ 2 := by
  have h1 := one_sub_lemT_ge (lt_of_lt_of_le hη hz)
  have h2 : z.im / 2 ≤ z.im / (1 + z.im) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  unfold lemT at h1
  linarith

private theorem znet_inv_le {t η : ℝ} (hη : 0 < η) (h : η / 2 ≤ 1 - t) : (1 - t)⁻¹ ≤ 2 * η⁻¹ := by
  have : (η / 2)⁻¹ = 2 * η⁻¹ := by rw [inv_div, div_eq_mul_inv]
  rw [← this]
  exact inv_anti₀ (by positivity) h

private theorem znet_theta_PM (sz : Sizes d) (n : ℕ) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im)
    (hz1 : z.im ≤ 1) : ‖ThetaPM sz n z‖ ≤ 2 * η⁻¹ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη hz
  have h1 := znet_one_sub_ge hη hz hz1
  have ht1 : ‖msc z‖ ^ 2 < 1 := by linarith
  have ht0 : (0 : ℝ) ≤ ‖msc z‖ ^ 2 := by positivity
  have := norm_Theta_le (d := d) (L := sz.L n) (g := sz.lam n) (sz.three_le_L n) ht0 ht1
    (m := 1) (by simp)
  rw [mul_one] at this
  exact this.trans (znet_inv_le hη h1)

private theorem znet_theta_PP (sz : Sizes d) (n : ℕ) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im)
    (hz1 : z.im ≤ 1) : ‖ThetaPP sz n z‖ ≤ 2 * η⁻¹ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη hz
  have h1 := znet_one_sub_ge hη hz hz1
  have ht1 : ‖msc z‖ ^ 2 < 1 := by linarith
  have ht0 : (0 : ℝ) ≤ ‖msc z‖ ^ 2 := by positivity
  have hm : ‖mE (lemE z) ^ 2‖ = 1 := by
    rw [norm_pow, norm_mE (abs_lemE_lt_two hz0).le]; norm_num
  have hsq : msc z ^ 2 = ((‖msc z‖ ^ 2 : ℝ) : ℂ) * mE (lemE z) ^ 2 := by
    have h := msc_eq_sqrt_mul_mE hz0
    have hT : lemT z = ‖msc z‖ ^ 2 := rfl
    conv_lhs => rw [h]
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (lemT_pos hz0).le, hT]
  have := norm_Theta_le (d := d) (L := sz.L n) (g := sz.lam n) (sz.three_le_L n) ht0 ht1 hm
  rw [← hsq] at this
  unfold ThetaPP
  exact this.trans (znet_inv_le hη h1)

private theorem znet_const_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    2 * η⁻¹ ^ 2 * (2 * η⁻¹ + (2 * η⁻¹) * (2 * η⁻¹)) ≤ 12 * η⁻¹ ^ 4 := by
  have hv : 1 ≤ η⁻¹ := (one_le_inv₀ hη).2 hη1
  nlinarith [pow_le_pow_right₀ hv (by norm_num : 3 ≤ 4), pow_pos (inv_pos.2 hη) 3]

/-- **`profPM` is `12 η⁻⁴`-Lipschitz** on `η ≤ Im z, Im z' ≤ 1` (`‖Θ‖ ≤ (1 - t)⁻¹ ≤ 2/η`, `Theta_sub_Theta`, `norm_SB`). -/
theorem profPM_lip (sz : Sizes d) (n : ℕ) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz1 : z.im ≤ 1)
    (hz' : η ≤ z'.im) (hz1' : z'.im ≤ 1) (a b : Zd d (sz.L n)) :
    ‖profPM sz n z a b - profPM sz n z' a b‖ ≤ 12 * η⁻¹ ^ 4 * ‖z - z'‖ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη hz
  have hz0' : 0 < z'.im := lt_of_lt_of_le hη hz'
  have hn1 : ‖msc z‖ < 1 := norm_msc_lt_one hz0
  have hn1' : ‖msc z'‖ < 1 := norm_msc_lt_one hz0'
  have hlip := msc_lip hη hz hz'
  have hξ : ‖(((‖msc z‖ ^ 2 : ℝ)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; nlinarith [norm_nonneg (msc z)]
  have hξ' : ‖(((‖msc z'‖ ^ 2 : ℝ)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; nlinarith [norm_nonneg (msc z')]
  have hcore := znet_prof_core (d := d) (L := sz.L n) (sz.lam n) (sz.three_le_L n) hξ hξ'
    (znet_theta_PM sz n hη hz hz1) (znet_theta_PM sz n hη hz' hz1') a b
  have hdiff : ‖(((‖msc z‖ ^ 2 : ℝ)) : ℂ) - (((‖msc z'‖ ^ 2 : ℝ)) : ℂ)‖ ≤ 2 * (η⁻¹ * η⁻¹ * ‖z - z'‖) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖msc z‖ ^ 2 - ‖msc z'‖ ^ 2 = (‖msc z‖ - ‖msc z'‖) * (‖msc z‖ + ‖msc z'‖) := by ring
    rw [h1, abs_mul]
    have h2 : |‖msc z‖ - ‖msc z'‖| ≤ η⁻¹ * η⁻¹ * ‖z - z'‖ := (abs_norm_sub_norm_le _ _).trans hlip
    have h3 : |‖msc z‖ + ‖msc z'‖| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]; linarith
    calc |‖msc z‖ - ‖msc z'‖| * |‖msc z‖ + ‖msc z'‖| ≤ (η⁻¹ * η⁻¹ * ‖z - z'‖) * 2 :=
          mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
      _ = 2 * (η⁻¹ * η⁻¹ * ‖z - z'‖) := by ring
  have hB : 0 ≤ 2 * η⁻¹ := by positivity
  calc ‖profPM sz n z a b - profPM sz n z' a b‖
      ≤ ‖(((‖msc z‖ ^ 2 : ℝ)) : ℂ) * Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b -
        (((‖msc z'‖ ^ 2 : ℝ)) : ℂ) * Theta d (sz.L n) (sz.lam n) (((‖msc z'‖ ^ 2 : ℝ)) : ℂ) a b‖ :=
        znet_div_Wd sz n _ _
    _ ≤ ‖(((‖msc z‖ ^ 2 : ℝ)) : ℂ) - (((‖msc z'‖ ^ 2 : ℝ)) : ℂ)‖ * (2 * η⁻¹ + (2 * η⁻¹) * (2 * η⁻¹)) := hcore
    _ ≤ (2 * (η⁻¹ * η⁻¹ * ‖z - z'‖)) * (2 * η⁻¹ + (2 * η⁻¹) * (2 * η⁻¹)) :=
        mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ = (2 * η⁻¹ ^ 2 * (2 * η⁻¹ + (2 * η⁻¹) * (2 * η⁻¹))) * ‖z - z'‖ := by ring
    _ ≤ (12 * η⁻¹ ^ 4) * ‖z - z'‖ :=
        mul_le_mul_of_nonneg_right (znet_const_le hη (le_trans hz hz1)) (norm_nonneg _)

/-- **`profPP` is `12 η⁻⁴`-Lipschitz** on `η ≤ Im z, Im z' ≤ 1` (`m² = t (m^{(E)})²`, `‖m^{(E)}‖ = 1`). -/
theorem profPP_lip (sz : Sizes d) (n : ℕ) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ z.im) (hz1 : z.im ≤ 1)
    (hz' : η ≤ z'.im) (hz1' : z'.im ≤ 1) (a b : Zd d (sz.L n)) :
    ‖profPP sz n z a b - profPP sz n z' a b‖ ≤ 12 * η⁻¹ ^ 4 * ‖z - z'‖ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη hz
  have hz0' : 0 < z'.im := lt_of_lt_of_le hη hz'
  have hn1 : ‖msc z‖ < 1 := norm_msc_lt_one hz0
  have hn1' : ‖msc z'‖ < 1 := norm_msc_lt_one hz0'
  have hlip := msc_lip hη hz hz'
  have hξ : ‖msc z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg (msc z)]
  have hξ' : ‖msc z' ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg (msc z')]
  have hcore := znet_prof_core (d := d) (L := sz.L n) (sz.lam n) (sz.three_le_L n) hξ hξ'
    (znet_theta_PP sz n hη hz hz1) (znet_theta_PP sz n hη hz' hz1') a b
  have hdiff : ‖msc z ^ 2 - msc z' ^ 2‖ ≤ 2 * (η⁻¹ * η⁻¹ * ‖z - z'‖) := by
    have h1 : msc z ^ 2 - msc z' ^ 2 = (msc z - msc z') * (msc z + msc z') := by ring
    rw [h1, norm_mul]
    have h3 : ‖msc z + msc z'‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    calc ‖msc z - msc z'‖ * ‖msc z + msc z'‖ ≤ (η⁻¹ * η⁻¹ * ‖z - z'‖) * 2 :=
          mul_le_mul hlip h3 (norm_nonneg _) (by positivity)
      _ = 2 * (η⁻¹ * η⁻¹ * ‖z - z'‖) := by ring
  calc ‖profPP sz n z a b - profPP sz n z' a b‖
      ≤ ‖msc z ^ 2 * Theta d (sz.L n) (sz.lam n) (msc z ^ 2) a b -
        msc z' ^ 2 * Theta d (sz.L n) (sz.lam n) (msc z' ^ 2) a b‖ := znet_div_Wd sz n _ _
    _ ≤ ‖msc z ^ 2 - msc z' ^ 2‖ * (2 * η⁻¹ + (2 * η⁻¹) * (2 * η⁻¹)) := hcore
    _ ≤ (2 * (η⁻¹ * η⁻¹ * ‖z - z'‖)) * (2 * η⁻¹ + (2 * η⁻¹) * (2 * η⁻¹)) :=
        mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ = (2 * η⁻¹ ^ 2 * (2 * η⁻¹ + (2 * η⁻¹) * (2 * η⁻¹))) * ‖z - z'‖ := by ring
    _ ≤ (12 * η⁻¹ ^ 4) * ‖z - z'‖ :=
        mul_le_mul_of_nonneg_right (znet_const_le hη (le_trans hz hz1)) (norm_nonneg _)

end Profile

/-! ### The cover lemmas: the bad event at `(τ)` is covered by the per-point bad events at `(τ/2)` -/

section Cover

variable {d : ℕ}

private theorem znet_rpow_sq {W : ℝ} (hW : 0 < W) (τ : ℝ) : (W ^ (τ / 2)) ^ 2 = W ^ τ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
  congr 1; push_cast; ring

/-- The geometry of a point `z` of the domain and a net point `w` within `N^{-7}` of it:
`N^{-1} ≤ Im z, Im w`, `|Im w - Im z| ≤ Im z / 2`, `‖z - w‖ ≤ 2 N^{-7}`. -/
private theorem znet_geom (sz : Sizes d) (n : ℕ) {κ ε : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n)
    {z w : ℂ} (hz : sz.locDomain κ ε n z) (hw : sz.locDomain κ ε n w)
    (hre : |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ)) (him : |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) :
    (Nsz sz n)⁻¹ ≤ z.im ∧ (Nsz sz n)⁻¹ ≤ w.im ∧ |w.im - z.im| ≤ z.im / 2 ∧
      ‖z - w‖ ≤ 2 * ((Nsz sz n)⁻¹) ^ 7 := by
  have hN0 : 0 < Nsz sz n := by linarith
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 hN0
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hmono : (Nsz sz n)⁻¹ ≤ Nsz sz n ^ (-1 + ε) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hδ : Nsz sz n ^ (-7 : ℝ) = ((Nsz sz n)⁻¹) ^ 7 := by
    rw [inv_pow, ← znet_rpow_neg7 hN0, inv_inv]
  have h7 : ((Nsz sz n)⁻¹) ^ 7 ≤ (Nsz sz n)⁻¹ / 2 := by
    have h6 : ((Nsz sz n)⁻¹) ^ 6 ≤ (1 / 32) ^ 6 := pow_le_pow_left₀ hu0.le hu32 6
    have h6' : ((Nsz sz n)⁻¹) ^ 6 ≤ 1 / 2 := h6.trans (by norm_num)
    calc ((Nsz sz n)⁻¹) ^ 7 = ((Nsz sz n)⁻¹) ^ 6 * (Nsz sz n)⁻¹ := by ring
      _ ≤ 1 / 2 * (Nsz sz n)⁻¹ := mul_le_mul_of_nonneg_right h6' hu0.le
      _ = (Nsz sz n)⁻¹ / 2 := by ring
  rw [hδ] at hre him
  have hzu : (Nsz sz n)⁻¹ ≤ z.im := hmono.trans hz.2.1
  refine ⟨hzu, hmono.trans hw.2.1, ?_, ?_⟩
  · rw [abs_sub_comm]
    linarith
  · calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 * ((Nsz sz n)⁻¹) ^ 7 := by
        rw [Complex.sub_re, Complex.sub_im]
        linarith

/-- The floor `N^{-1} ≤ 𝓑_{η,K}` for `0 < η ≤ 1`, `K ≥ 0` (`(Nη)⁻¹ ≤ 𝓑_{η,K}`, `η ≤ 1`). -/
private theorem znet_floor (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {η K : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hK : 0 ≤ K) : (Nsz sz n)⁻¹ ≤ calB sz n η K := by
  refine le_trans ?_ (inv_size_mul_le_calB sz n hd hη hK)
  exact inv_anti₀ (mul_pos (Nsz_pos sz n) hη) (mul_le_of_le_one_right (Nsz_pos sz n).le hη1)

/-- The resolvent entries move by at most `2 u⁵` (`u = N⁻¹`) from `z` to a net point, for every `ω`. -/
private theorem znet_G_diff (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {z w : ℂ} {u : ℝ} (hu : 0 < u)
    (hzu : u ≤ z.im) (hwu : u ≤ w.im) (hζ : ‖z - w‖ ≤ 2 * u ^ 7) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖sz.Gn n z ω x y - sz.Gn n w ω x y‖ ≤ 2 * u ^ 5 := by
  refine (Gn_entry_lip sz n ω hu hzu hwu x y).trans ?_
  calc u⁻¹ * u⁻¹ * ‖z - w‖ ≤ u⁻¹ * u⁻¹ * (2 * u ^ 7) := mul_le_mul_of_nonneg_left hζ (by positivity)
    _ = 2 * u ^ 5 := by field_simp

private theorem znet_m_diff {z w : ℂ} {u : ℝ} (hu : 0 < u) (hzu : u ≤ z.im) (hwu : u ≤ w.im)
    (hζ : ‖z - w‖ ≤ 2 * u ^ 7) : ‖msc z - msc w‖ ≤ 2 * u ^ 5 := by
  refine (msc_lip hu hzu hwu).trans ?_
  calc u⁻¹ * u⁻¹ * ‖z - w‖ ≤ u⁻¹ * u⁻¹ * (2 * u ^ 7) := mul_le_mul_of_nonneg_left hζ (by positivity)
    _ = 2 * u ^ 5 := by field_simp

private theorem znet_avg1 (sz : Sizes d) (n : ℕ) (a : Zd d (sz.L n)) (F F' : Idx d (sz.L n) (sz.W n) → ℂ)
    {c : ℝ} (h : ∀ x, ‖F x - F' x‖ ≤ c) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, F x -
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, F' x‖ ≤ c := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (znet_W_pos sz n) d
  have hcard : ((Iblk d (sz.L n) (sz.W n) a).card : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [card_Iblk]; push_cast; rfl
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hsum : ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a, (F x - F' x)‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * c := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => h x).trans (le_of_eq ?_))
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a, (F x - F' x)‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * c) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = c := by field_simp

private theorem znet_sq_diff {a b : ℂ} {B c : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hab : ‖a - b‖ ≤ c) :
    ‖((‖a‖ ^ 2 : ℝ) : ℂ) - ((‖b‖ ^ 2 : ℝ) : ℂ)‖ ≤ c * (2 * B) := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
  rw [h1, abs_mul]
  have h2 : |‖a‖ - ‖b‖| ≤ c := (abs_norm_sub_norm_le _ _).trans hab
  have h3 : |‖a‖ + ‖b‖| ≤ 2 * B := by
    rw [abs_of_nonneg (by positivity)]; linarith
  exact mul_le_mul h2 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h2)

private theorem znet_prod_diff {a b a' b' : ℂ} {B c : ℝ} (ha' : ‖a'‖ ≤ B) (hb : ‖b‖ ≤ B)
    (h1 : ‖a - a'‖ ≤ c) (h2 : ‖b - b'‖ ≤ c) : ‖a * b - a' * b'‖ ≤ c * (2 * B) := by
  have hc : 0 ≤ c := le_trans (norm_nonneg _) h1
  have hB : 0 ≤ B := le_trans (norm_nonneg _) hb
  have hid : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [hid]
  calc ‖(a - a') * b + a' * (b - b')‖ ≤ ‖(a - a') * b‖ + ‖a' * (b - b')‖ := norm_add_le _ _
    _ = ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := by rw [norm_mul, norm_mul]
    _ ≤ c * B + B * c := add_le_add (mul_le_mul h1 hb (norm_nonneg _) hc)
        (mul_le_mul ha' h2 (norm_nonneg _) hB)
    _ = c * (2 * B) := by ring

/-- Numerics of the entries: `e ≤ 4 u⁵`, `u ≤ 1/32` give `e ≤ u` and `2 e² ≤ u`. -/
private theorem znet_num1 {u e : ℝ} (hu : 0 < u) (hu32 : u ≤ 1 / 32) (he : e ≤ 4 * u ^ 5) (he0 : 0 ≤ e) :
    e ≤ u ∧ 2 * e ^ 2 ≤ u := by
  have h4 : u ^ 4 ≤ (1 / 32) ^ 4 := pow_le_pow_left₀ hu.le hu32 4
  have h9 : u ^ 9 ≤ (1 / 32) ^ 9 := pow_le_pow_left₀ hu.le hu32 9
  have h4' : 4 * u ^ 4 ≤ 1 := by norm_num at h4; linarith
  have h9' : 32 * u ^ 9 ≤ 1 := by norm_num at h9; linarith
  have e1 : e ≤ u := by
    calc e ≤ 4 * u ^ 5 := he
      _ = (4 * u ^ 4) * u := by ring
      _ ≤ 1 * u := mul_le_mul_of_nonneg_right h4' hu.le
      _ = u := one_mul u
  refine ⟨e1, ?_⟩
  have e2 : e ^ 2 ≤ (4 * u ^ 5) ^ 2 := pow_le_pow_left₀ he0 he 2
  calc 2 * e ^ 2 ≤ 2 * (4 * u ^ 5) ^ 2 := by linarith
    _ = (32 * u ^ 9) * u := by ring
    _ ≤ 1 * u := mul_le_mul_of_nonneg_right h9' hu.le
    _ = u := one_mul u

/-- Numerics of the profiles: `4 u⁴ + 24 u³ ≤ u²` for `0 < u ≤ 1/32`. -/
private theorem znet_num2 {u : ℝ} (hu : 0 < u) (hu32 : u ≤ 1 / 32) : 4 * u ^ 4 + 24 * u ^ 3 ≤ u ^ 2 := by
  have h1 : 4 * u ^ 2 + 24 * u ≤ 1 := by nlinarith
  calc 4 * u ^ 4 + 24 * u ^ 3 = u ^ 2 * (4 * u ^ 2 + 24 * u) := by ring
    _ ≤ u ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg u)
    _ = u ^ 2 := mul_one _

/-- The core of `(G_bound)`: from the net point's bound `Y² ≤ s 𝓑_w` and `X ≤ Y + e` to `X² ≤ s² 𝓑_z`. -/
private theorem znet_loc1_core {s Bz Bw u X Y e : ℝ} (hs : 5 ≤ s) (hBw : Bw ≤ 2 * Bz) (hu : u ≤ Bz)
    (hu0 : 0 < u) (hu32 : u ≤ 1 / 32) (he0 : 0 ≤ e) (he : e ≤ 4 * u ^ 5) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hY : Y ^ 2 ≤ s * Bw) (hX : X ≤ Y + e) : X ^ 2 ≤ s ^ 2 * Bz := by
  obtain ⟨he1, he2⟩ := znet_num1 hu0 hu32 he he0
  have hBz : 0 ≤ Bz := le_trans hu0.le hu
  have h1 : X ^ 2 ≤ (Y + e) ^ 2 := pow_le_pow_left₀ hX0 hX 2
  have h2 : (Y + e) ^ 2 ≤ 2 * Y ^ 2 + 2 * e ^ 2 := by nlinarith [sq_nonneg (Y - e)]
  have h3 : 2 * Y ^ 2 ≤ 4 * s * Bz := by nlinarith
  have h4 : (4 * s + 1) * Bz ≤ s ^ 2 * Bz := mul_le_mul_of_nonneg_right (by nlinarith) hBz
  nlinarith

/-- The core of `(G_bound_ave)`. -/
private theorem znet_loc2_core {s Bz Bw u X Y e : ℝ} (hs : 5 ≤ s) (hBw : Bw ≤ 2 * Bz) (hu : u ≤ Bz)
    (hu0 : 0 < u) (hu32 : u ≤ 1 / 32) (he0 : 0 ≤ e) (he : e ≤ 4 * u ^ 5) (hY : Y ≤ s * Bw)
    (hX : X ≤ Y + e) : X ≤ s ^ 2 * Bz := by
  obtain ⟨he1, he2⟩ := znet_num1 hu0 hu32 he he0
  have hBz : 0 ≤ Bz := le_trans hu0.le hu
  have h4 : (2 * s + 1) * Bz ≤ s ^ 2 * Bz := mul_le_mul_of_nonneg_right (by nlinarith) hBz
  nlinarith

/-- `min(𝓑_{η',0}^{1/5} 𝓑_{η',K}, 𝓑_{η',0}²) ≤ 4 min(𝓑_{η,0}^{1/5} 𝓑_{η,K}, 𝓑_{η,0}²)` for `|η' - η| ≤ η/2`. -/
private theorem znet_min_shift (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {η η' : ℝ} (hη : 0 < η)
    (h : |η' - η| ≤ η / 2) (a b : Zd d (sz.L n)) :
    min (calB sz n η' 0 ^ ((1 : ℝ) / 5) * calB sz n η' (distB sz n a b)) (calB sz n η' 0 ^ 2) ≤
      4 * min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b)) (calB sz n η 0 ^ 2) := by
  have hη' : 0 < η' := by have := (abs_le.mp h).1; linarith
  have hK : 0 ≤ distB sz n a b := by unfold distB; positivity
  have h0 := calB_shift_le sz n hη (le_refl (0 : ℝ)) h
  have hK' := calB_shift_le sz n hη hK h
  have hB0 : 0 ≤ calB sz n η 0 := calB_nonneg sz n hη le_rfl
  have hBK : 0 ≤ calB sz n η (distB sz n a b) := calB_nonneg sz n hη hK
  have hB0' : 0 ≤ calB sz n η' 0 := calB_nonneg sz n hη' le_rfl
  have hBK' : 0 ≤ calB sz n η' (distB sz n a b) := calB_nonneg sz n hη' hK
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hpow : calB sz n η' 0 ^ ((1 : ℝ) / 5) ≤ 2 * calB sz n η 0 ^ ((1 : ℝ) / 5) := by
    calc calB sz n η' 0 ^ ((1 : ℝ) / 5) ≤ (2 * calB sz n η 0) ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow hB0' h0 (by norm_num)
      _ = 2 ^ ((1 : ℝ) / 5) * calB sz n η 0 ^ ((1 : ℝ) / 5) := Real.mul_rpow (by norm_num) hB0
      _ ≤ 2 * calB sz n η 0 ^ ((1 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hB0 _)
  have e1 : calB sz n η' 0 ^ ((1 : ℝ) / 5) * calB sz n η' (distB sz n a b) ≤
      4 * (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b)) := by
    calc _ ≤ (2 * calB sz n η 0 ^ ((1 : ℝ) / 5)) * (2 * calB sz n η (distB sz n a b)) :=
          mul_le_mul hpow hK' hBK' (by positivity)
      _ = 4 * (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b)) := by ring
  have e2 : calB sz n η' 0 ^ 2 ≤ 4 * calB sz n η 0 ^ 2 := by
    calc calB sz n η' 0 ^ 2 ≤ (2 * calB sz n η 0) ^ 2 := pow_le_pow_left₀ hB0' h0 2
      _ = 4 * calB sz n η 0 ^ 2 := by ring
  calc _ ≤ min (4 * (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b)))
        (4 * calB sz n η 0 ^ 2) := min_le_min e1 e2
    _ = 4 * min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b)) (calB sz n η 0 ^ 2) :=
        (mul_min_of_nonneg _ _ (by norm_num)).symm

/-- The floor `N⁻² ≤ min(𝓑_{η,0}^{1/5} 𝓑_{η,K}, 𝓑_{η,0}²)` for `0 < η ≤ 1`. -/
private theorem znet_min_floor (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : 1 ≤ Nsz sz n) (a b : Zd d (sz.L n)) :
    ((Nsz sz n)⁻¹) ^ 2 ≤
      min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b)) (calB sz n η 0 ^ 2) := by
  have hK : 0 ≤ distB sz n a b := by unfold distB; positivity
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (lt_of_lt_of_le one_pos hN)
  have hu1 : (Nsz sz n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have f0 := znet_floor sz n hd hη hη1 (le_refl (0 : ℝ))
  have fK := znet_floor sz n hd hη hη1 hK
  have h5 : (Nsz sz n)⁻¹ ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) := by
    calc (Nsz sz n)⁻¹ = (Nsz sz n)⁻¹ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Nsz sz n)⁻¹ ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by norm_num)
      _ ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow hu0.le f0 (by norm_num)
  refine le_min ?_ ?_
  · calc ((Nsz sz n)⁻¹) ^ 2 = (Nsz sz n)⁻¹ * (Nsz sz n)⁻¹ := sq _
      _ ≤ calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b) :=
          mul_le_mul h5 fK hu0.le (le_trans hu0.le h5)
  · exact pow_le_pow_left₀ hu0.le f0 2

/-- The core of `(eq:diffu1,2)`: `X ≤ Y + E`, `Y ≤ qdBound_{τ/2}(w)`, `E ≤ u²` give `X ≤ qdBound_τ(z)`. -/
private theorem znet_qd_core (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {τ : ℝ} {z w : ℂ}
    (hz1 : z.im ≤ 1) (hzu : (Nsz sz n)⁻¹ ≤ z.im) (hN : 1 ≤ Nsz sz n)
    (hshift : |w.im - z.im| ≤ z.im / 2) (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (a b : Zd d (sz.L n))
    {X Y E : ℝ} (hY : Y ≤ qdBound sz n (τ / 2) w.im a b) (hE : E ≤ ((Nsz sz n)⁻¹) ^ 2) (hX : X ≤ Y + E) :
    X ≤ qdBound sz n τ z.im a b := by
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (lt_of_lt_of_le one_pos hN)
  have hz0 : 0 < z.im := lt_of_lt_of_le hu0 hzu
  have hW := znet_W_pos sz n
  have hsq := znet_rpow_sq hW τ
  have hmin := znet_min_shift sz n hd hz0 hshift a b
  have hfl := znet_min_floor sz n hd hz0 hz1 hN a b
  set s := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hs
  set m := min (calB sz n z.im 0 ^ ((1 : ℝ) / 5) * calB sz n z.im (distB sz n a b)) (calB sz n z.im 0 ^ 2)
    with hm
  have hm0 : 0 ≤ m := le_trans (sq_nonneg _) hfl
  unfold qdBound at hY ⊢
  rw [← hsq]
  have hY' : Y ≤ s * (4 * m) := hY.trans (mul_le_mul_of_nonneg_left hmin (by linarith))
  nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ s - 5)]

/-- **Cover lemma for `(G_bound)`**: every `ω` in the bad event at `τ` lies in the per-point bad event at `τ/2` of a
net point (`32 ≤ N`, `5 ≤ W^{τ/2}`, `ε > 0`); deterministic, for every `ω`. -/
theorem locBad1_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n)
    (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w)
    (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ))
    (ω : sz.SeqΩ) (hω : locBad1 sz κ ε τ n ω) : ∃ w ∈ S, locBad1z sz (τ / 2) n w ω := by
  obtain ⟨z, hz, x, y, hxy⟩ := hω
  obtain ⟨w, hwS, hre, him⟩ := hcov z hz
  refine ⟨w, hwS, ?_⟩
  by_contra hnb
  unfold locBad1z at hnb
  push Not at hnb
  have hnb' := hnb x y
  have hw := hS w hwS
  obtain ⟨hzu, hwu, hshift, hζ⟩ := znet_geom sz n hε h32 hz hw hre him
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (by linarith)
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hz0 : 0 < z.im := lt_of_lt_of_le hu0 hzu
  have hK : 0 ≤ distB sz n (STblk sz n x) (STblk sz n y) := by unfold distB; positivity
  have hfloor := znet_floor sz n (by omega) hz0 hz.2.2 hK
  have hshiftB := calB_shift_le sz n hz0 hK hshift
  have hGd := znet_G_diff sz n ω hu0 hzu hwu hζ x y
  have hMd := znet_m_diff hu0 hzu hwu hζ
  have hMb : ‖Mband sz n z x y - Mband sz n w x y‖ ≤ 2 * ((Nsz sz n)⁻¹) ^ 5 := by
    unfold Mband
    split_ifs
    · exact hMd
    · simp only [sub_self, norm_zero]; positivity
  have hsplit : sz.Gn n z ω x y - Mband sz n z x y =
      (sz.Gn n w ω x y - Mband sz n w x y) +
        ((sz.Gn n z ω x y - sz.Gn n w ω x y) - (Mband sz n z x y - Mband sz n w x y)) := by ring
  have hX : ‖sz.Gn n z ω x y - Mband sz n z x y‖ ≤
      ‖sz.Gn n w ω x y - Mband sz n w x y‖ + 4 * ((Nsz sz n)⁻¹) ^ 5 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := (norm_sub_le (sz.Gn n z ω x y - sz.Gn n w ω x y) (Mband sz n z x y - Mband sz n w x y))
    linarith
  have hW := znet_W_pos sz n
  have hsq := znet_rpow_sq hW τ
  have := znet_loc1_core (s := ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (Bz := calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)))
    (Bw := calB sz n w.im (distB sz n (STblk sz n x) (STblk sz n y))) (u := (Nsz sz n)⁻¹)
    (X := ‖sz.Gn n z ω x y - Mband sz n z x y‖) (Y := ‖sz.Gn n w ω x y - Mband sz n w x y‖)
    (e := 4 * ((Nsz sz n)⁻¹) ^ 5) h5 hshiftB hfloor hu0 hu32 (by positivity) le_rfl (norm_nonneg _)
    (norm_nonneg _) hnb' hX
  rw [hsq] at this
  exact absurd hxy (not_lt.2 this)

/-- **Cover lemma for `(G_bound_ave)`**: as `locBad1_net`. -/
theorem locBad2_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n)
    (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w)
    (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ))
    (ω : sz.SeqΩ) (hω : locBad2 sz κ ε τ n ω) : ∃ w ∈ S, locBad2z sz (τ / 2) n w ω := by
  obtain ⟨z, hz, a, ha⟩ := hω
  obtain ⟨w, hwS, hre, him⟩ := hcov z hz
  refine ⟨w, hwS, ?_⟩
  by_contra hnb
  unfold locBad2z at hnb
  push Not at hnb
  have hnb' := hnb a
  have hw := hS w hwS
  obtain ⟨hzu, hwu, hshift, hζ⟩ := znet_geom sz n hε h32 hz hw hre him
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (by linarith)
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hz0 : 0 < z.im := lt_of_lt_of_le hu0 hzu
  have hfloor := znet_floor sz n (by omega) hz0 hz.2.2 (le_refl (0 : ℝ))
  have hshiftB := calB_shift_le sz n hz0 (le_refl (0 : ℝ)) hshift
  have hMd := znet_m_diff hu0 hzu hwu hζ
  have hAd := znet_avg1 sz n a (fun x => sz.Gn n z ω x x) (fun x => sz.Gn n w ω x x)
    (c := 2 * ((Nsz sz n)⁻¹) ^ 5) (fun x => znet_G_diff sz n ω hu0 hzu hwu hζ x x)
  have hsplit : (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n w ω x x - msc w) +
        (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x -
          (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n w ω x x) -
            (msc z - msc w)) := by ring
  have hX : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z‖ ≤
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n w ω x x - msc w‖ +
        4 * ((Nsz sz n)⁻¹) ^ 5 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x -
          (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n w ω x x) (msc z - msc w)
    linarith
  have hW := znet_W_pos sz n
  have hsq := znet_rpow_sq hW τ
  have := znet_loc2_core (s := ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (Bz := calB sz n z.im 0)
    (Bw := calB sz n w.im 0) (u := (Nsz sz n)⁻¹)
    (X := ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z‖)
    (Y := ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n w ω x x - msc w‖)
    (e := 4 * ((Nsz sz n)⁻¹) ^ 5) h5 hshiftB hfloor hu0 hu32 (by positivity) le_rfl hnb' hX
  rw [hsq] at this
  exact absurd ha (not_lt.2 this)

private theorem znet_c4 {u : ℝ} (hu : 0 < u) : 2 * u ^ 5 * (2 * u⁻¹) = 4 * u ^ 4 := by
  field_simp
  ring

private theorem znet_c3 {u : ℝ} (hu : 0 < u) : 12 * u⁻¹ ^ 4 * (2 * u ^ 7) = 24 * u ^ 3 := by
  field_simp
  ring

/-- **Cover lemma for `(eq:diffu1)`**: as `locBad1_net`, the blocks `a, b` inside. -/
theorem qd1Bad_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n)
    (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w)
    (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ))
    (ω : sz.SeqΩ) (hω : qd1Bad sz κ ε τ n ω) : ∃ w ∈ S, qd1Badz sz (τ / 2) n w ω := by
  obtain ⟨z, hz, a, b, hab⟩ := hω
  obtain ⟨w, hwS, hre, him⟩ := hcov z hz
  refine ⟨w, hwS, ?_⟩
  by_contra hnb
  unfold qd1Badz at hnb
  push Not at hnb
  have hnb' := hnb a b
  have hw := hS w hwS
  obtain ⟨hzu, hwu, hshift, hζ⟩ := znet_geom sz n hε h32 hz hw hre him
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (by linarith)
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hGz : ∀ x y, ‖sz.Gn n z ω x y‖ ≤ ((Nsz sz n)⁻¹)⁻¹ := fun x y => Gn_entry_le sz n ω hu0 hzu x y
  have hGw : ∀ x y, ‖sz.Gn n w ω x y‖ ≤ ((Nsz sz n)⁻¹)⁻¹ := fun x y => Gn_entry_le sz n ω hu0 hwu x y
  have havg := avg2_lip sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ))
    (fun x y => ((‖sz.Gn n w ω x y‖ ^ 2 : ℝ) : ℂ)) (c := 4 * ((Nsz sz n)⁻¹) ^ 4)
    (fun x y => (znet_sq_diff (hGz x y) (hGw x y) (znet_G_diff sz n ω hu0 hzu hwu hζ x y)).trans
      (le_of_eq (znet_c4 hu0))) a b
  have hprof := profPM_lip sz n hu0 hzu hz.2.2 hwu hw.2.2 a b
  have hprof' : ‖profPM sz n z a b - profPM sz n w a b‖ ≤ 24 * ((Nsz sz n)⁻¹) ^ 3 :=
    hprof.trans ((mul_le_mul_of_nonneg_left hζ (by positivity)).trans (le_of_eq (znet_c3 hu0)))
  have hE := znet_num2 hu0 hu32
  have hsplit : avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n z a b =
      (avg2 sz n (fun x y => ((‖sz.Gn n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n w a b) +
        ((avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
          avg2 sz n (fun x y => ((‖sz.Gn n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b) -
            (profPM sz n z a b - profPM sz n w a b)) := by ring
  have hX : ‖avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n z a b‖ ≤
      ‖avg2 sz n (fun x y => ((‖sz.Gn n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n w a b‖ +
        (4 * ((Nsz sz n)⁻¹) ^ 4 + 24 * ((Nsz sz n)⁻¹) ^ 3) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le (avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
          avg2 sz n (fun x y => ((‖sz.Gn n w ω x y‖ ^ 2 : ℝ) : ℂ)) a b)
        (profPM sz n z a b - profPM sz n w a b)
    linarith
  have := znet_qd_core sz n (by omega) hz.2.2 hzu hN1 hshift h5 a b hnb' hE hX
  exact absurd hab (not_lt.2 this)

/-- **Cover lemma for `(eq:diffu2)`**: as `locBad1_net`, the blocks `a, b` inside. -/
theorem qd2Bad_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n)
    (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, sz.locDomain κ ε n w)
    (hcov : ∀ z : ℂ, sz.locDomain κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ))
    (ω : sz.SeqΩ) (hω : qd2Bad sz κ ε τ n ω) : ∃ w ∈ S, qd2Badz sz (τ / 2) n w ω := by
  obtain ⟨z, hz, a, b, hab⟩ := hω
  obtain ⟨w, hwS, hre, him⟩ := hcov z hz
  refine ⟨w, hwS, ?_⟩
  by_contra hnb
  unfold qd2Badz at hnb
  push Not at hnb
  have hnb' := hnb a b
  have hw := hS w hwS
  obtain ⟨hzu, hwu, hshift, hζ⟩ := znet_geom sz n hε h32 hz hw hre him
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (by linarith)
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hGz : ∀ x y, ‖sz.Gn n z ω x y‖ ≤ ((Nsz sz n)⁻¹)⁻¹ := fun x y => Gn_entry_le sz n ω hu0 hzu x y
  have hGw : ∀ x y, ‖sz.Gn n w ω x y‖ ≤ ((Nsz sz n)⁻¹)⁻¹ := fun x y => Gn_entry_le sz n ω hu0 hwu x y
  have havg := avg2_lip sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x)
    (fun x y => sz.Gn n w ω x y * sz.Gn n w ω y x) (c := 4 * ((Nsz sz n)⁻¹) ^ 4)
    (fun x y => (znet_prod_diff (hGw x y) (hGz y x) (znet_G_diff sz n ω hu0 hzu hwu hζ x y)
      (znet_G_diff sz n ω hu0 hzu hwu hζ y x)).trans (le_of_eq (znet_c4 hu0))) a b
  have hprof := profPP_lip sz n hu0 hzu hz.2.2 hwu hw.2.2 a b
  have hprof' : ‖profPP sz n z a b - profPP sz n w a b‖ ≤ 24 * ((Nsz sz n)⁻¹) ^ 3 :=
    hprof.trans ((mul_le_mul_of_nonneg_left hζ (by positivity)).trans (le_of_eq (znet_c3 hu0)))
  have hE := znet_num2 hu0 hu32
  have hsplit : avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b - profPP sz n z a b =
      (avg2 sz n (fun x y => sz.Gn n w ω x y * sz.Gn n w ω y x) a b - profPP sz n w a b) +
        ((avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b -
          avg2 sz n (fun x y => sz.Gn n w ω x y * sz.Gn n w ω y x) a b) -
            (profPP sz n z a b - profPP sz n w a b)) := by ring
  have hX : ‖avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b - profPP sz n z a b‖ ≤
      ‖avg2 sz n (fun x y => sz.Gn n w ω x y * sz.Gn n w ω y x) a b - profPP sz n w a b‖ +
        (4 * ((Nsz sz n)⁻¹) ^ 4 + 24 * ((Nsz sz n)⁻¹) ^ 3) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le (avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b -
          avg2 sz n (fun x y => sz.Gn n w ω x y * sz.Gn n w ω y x) a b)
        (profPP sz n z a b - profPP sz n w a b)
    linarith
  have := znet_qd_core sz n (by omega) hz.2.2 hzu hN1 hshift h5 a b hnb' hE hX
  exact absurd hab (not_lt.2 this)

end Cover

/-! ### The pins `MANetLoc`, `MANetQD` proved: the thresholds, the net, the union bound -/

section Main

/-- The thresholds of the net argument hold eventually along an admissible sequence: `32 ≤ N` (`N → ∞`) and
`5 ≤ W^{τ/2}` (`W → ∞`, `Main_DEL_COND`). -/
private theorem znet_thresholds {d : ℕ} {𝔠 𝔡 : ℝ} (sz : Sizes d) (hA : sz.Admissible 𝔠 𝔡) {τ : ℝ}
    (hτ : 0 < τ) : ∀ᶠ n in atTop, 32 ≤ Nsz sz n ∧ 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by
  have h32 : ∀ᶠ n in atTop, (32 : ℝ) ≤ Nsz sz n := hA.2.2.1.eventually_ge_atTop 32
  have hW : ∀ᶠ n in atTop, (5 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by
    have h := RBM.Green.tendsto_W sz hA.1 hA.2.2.1 hA.2.2.2.1
    exact ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp h).eventually_ge_atTop 5
  exact h32.and hW

/-- **`MANetLoc` proved** (`1_2:1228`): `locSC` from its fixed-`z` form, by the deterministic net of
`zNet_exists`, the cover lemmas `locBad1_net`, `locBad2_net` at `(τ/2, D + 15)`, the union bound and the count. -/
theorem netLoc : MANetLoc := by
  intro hFix d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hF := hFix d hd 𝔠 𝔡 sz hA κ ε (τ / 2) (D + 15) hκ hε (by positivity) (by positivity)
  filter_upwards [hF, znet_thresholds sz hA hτ] with n hn hth
  obtain ⟨h32, h5⟩ := hth
  obtain ⟨S, hcard, hS, hcov⟩ := zNet_exists (ε := ε) sz hκ n
  have hnc := net_count (D := D) S.card (by linarith) hcard
  refine ⟨?_, ?_⟩
  · refine le_trans (net_union_le (Sizes.seqP sz) S {ω | locBad1 sz κ ε τ n ω}
      (fun w => {ω | locBad1z sz (τ / 2) n w ω}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := locBad1_net sz n hd hε h32 h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).1
  · refine le_trans (net_union_le (Sizes.seqP sz) S {ω | locBad2 sz κ ε τ n ω}
      (fun w => {ω | locBad2z sz (τ / 2) n w ω}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := locBad2_net sz n hd hε h32 h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).2

/-- **`MANetQD` proved**: the probability halves of `QDiff` by the net at `(τ/2, D + 15)`; the expectation half
is the one of `QDiffFixed` at `(κ, ε, τ, D)` (already pointwise in `z`, no lift). -/
theorem netQD : MANetQD := by
  intro hFix d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hF := hFix d hd 𝔠 𝔡 sz hA κ ε (τ / 2) (D + 15) hκ hε (by positivity) (by positivity)
  have hF' := hFix d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  filter_upwards [hF, hF', znet_thresholds sz hA hτ] with n hn hn' hth
  obtain ⟨h32, h5⟩ := hth
  obtain ⟨S, hcard, hS, hcov⟩ := zNet_exists (ε := ε) sz hκ n
  have hnc := net_count (D := D) S.card (by linarith) hcard
  refine ⟨⟨?_, ?_⟩, fun z hz a b => (hn' z hz).2 a b⟩
  · refine le_trans (net_union_le (Sizes.seqP sz) S {ω | qd1Bad sz κ ε τ n ω}
      (fun w => {ω | qd1Badz sz (τ / 2) n w ω}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := qd1Bad_net sz n hd hε h32 h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).1.1
  · refine le_trans (net_union_le (Sizes.seqP sz) S {ω | qd2Bad sz κ ε τ n ω}
      (fun w => {ω | qd2Badz sz (τ / 2) n w ω}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := qd2Bad_net sz n hd hε h32 h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).1.2

end Main

/-! ### Compiled nonempty instances at `d = 3` on `SizesInst.sz0` (CLAUDE.md §4 step 2) -/

/-! Instances at `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `n = 0`: `L = 4`,
`W = 32`, `N = 2097152`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`, `ε = 1/20`, `τ = 1/10`, `D = 2` for the pins (as the
merged `inst_locSC`, `inst_QDiff`); `τ = 1` for the cover lemmas at `n = 0` (`W^{τ/2} = √32 ≥ 5`).  `locSCFixed`,
`QDiffFixed` are the fixed-`z` statements, which `fixed_of_ML` proves from the flow outputs owed by ST-6: hypotheses
of the instances; every deterministic hypothesis (`3 ≤ d`, `Admissible`, the positivity of `κ, ε, τ, D`) is
discharged. -/

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- **`MANetLoc` at the instance**: the conclusion of the merged `inst_locSC`, from `locSCFixed`. -/
theorem inst_netLoc (h : locSCFixed) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  netLoc h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **`MANetQD` at the instance**: the conclusion of the merged `inst_QDiff`, from `QDiffFixed`. -/
theorem inst_netQD (h : QDiffFixed) :
    ∀ᶠ n in atTop,
      (Sizes.seqP sz0 {ω | qd1Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z → ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im :=
  netQD h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **The grid at `n = 0`** (`N = 2097152`, `κ = 1/10`, `ε = 1/20`), no hypothesis. -/
theorem inst_zNet :
    ∃ S : Finset ℂ, (S.card : ℝ) ≤ 25 * Nsz sz0 0 ^ (14 : ℕ) ∧ (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) 0 z → ∃ w ∈ S,
        |z.re - w.re| ≤ Nsz sz0 0 ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz0 0 ^ (-7 : ℝ) :=
  zNet_exists sz0 (by norm_num) 0

/-- The grid of `inst_zNet` is nonempty: the domain `𝐃_{1/10,1/20}` at `n = 0` contains `z = i`, which the
cover property sends to a grid point. -/
example :
    ∃ S : Finset ℂ, S.Nonempty ∧ (S.card : ℝ) ≤ 25 * Nsz sz0 0 ^ (14 : ℕ) ∧
      (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) 0 z → ∃ w ∈ S,
        |z.re - w.re| ≤ Nsz sz0 0 ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz0 0 ^ (-7 : ℝ) := by
  obtain ⟨S, h1, h2, h3⟩ := inst_zNet
  obtain ⟨z, hz⟩ := locDomain_nonempty sz0 (κ := 1 / 10) (ε := 1 / 20) (by norm_num) (by norm_num) 0
  obtain ⟨w, hw, -⟩ := h3 z hz
  exact ⟨S, ⟨w, hw⟩, h1, h2, h3⟩

private theorem znet_inst_h32 : 32 ≤ Nsz sz0 0 := by
  change (32 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ)
  rw [sz0_values.2.2.1]
  norm_num

private theorem znet_inst_h5 : 5 ≤ ((sz0.W 0 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [sz0_values.2.1, ← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le (by norm_num)

/-- `locBad1_net` at the instance (`n = 0`, `τ = 1`; the net of `inst_zNet`). -/
example (ω : sz0.SeqΩ) (hω : locBad1 sz0 (1 / 10) (1 / 20) 1 0 ω) :
    ∃ S : Finset ℂ, (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧ ∃ w ∈ S, locBad1z sz0 (1 / 2) 0 w ω := by
  obtain ⟨S, -, hS, hcov⟩ := inst_zNet
  exact ⟨S, hS, locBad1_net sz0 0 le_rfl (τ := 1) (by norm_num) znet_inst_h32 znet_inst_h5 S hS hcov ω hω⟩

/-- `locBad2_net` at the instance. -/
example (ω : sz0.SeqΩ) (hω : locBad2 sz0 (1 / 10) (1 / 20) 1 0 ω) :
    ∃ S : Finset ℂ, (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧ ∃ w ∈ S, locBad2z sz0 (1 / 2) 0 w ω := by
  obtain ⟨S, -, hS, hcov⟩ := inst_zNet
  exact ⟨S, hS, locBad2_net sz0 0 le_rfl (τ := 1) (by norm_num) znet_inst_h32 znet_inst_h5 S hS hcov ω hω⟩

/-- `qd1Bad_net` at the instance. -/
example (ω : sz0.SeqΩ) (hω : qd1Bad sz0 (1 / 10) (1 / 20) 1 0 ω) :
    ∃ S : Finset ℂ, (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧ ∃ w ∈ S, qd1Badz sz0 (1 / 2) 0 w ω := by
  obtain ⟨S, -, hS, hcov⟩ := inst_zNet
  exact ⟨S, hS, qd1Bad_net sz0 0 le_rfl (τ := 1) (by norm_num) znet_inst_h32 znet_inst_h5 S hS hcov ω hω⟩

/-- `qd2Bad_net` at the instance. -/
example (ω : sz0.SeqΩ) (hω : qd2Bad sz0 (1 / 10) (1 / 20) 1 0 ω) :
    ∃ S : Finset ℂ, (∀ w ∈ S, sz0.locDomain (1 / 10) (1 / 20) 0 w) ∧ ∃ w ∈ S, qd2Badz sz0 (1 / 2) 0 w ω := by
  obtain ⟨S, -, hS, hcov⟩ := inst_zNet
  exact ⟨S, hS, qd2Bad_net sz0 0 le_rfl (τ := 1) (by norm_num) znet_inst_h32 znet_inst_h5 S hS hcov ω hω⟩

/-! Concrete applications of the intermediate lemmas (nondegenerate data, `sz0`, `n = 0`). -/

example : volume (Set.Icc (0 : ℝ) 2) ≤ (({0, 1} : Finset ℕ).card : ℝ≥0∞) * 1 := by
  refine net_union_le volume {0, 1} (Set.Icc 0 2) (fun i : ℕ => Set.Icc (i : ℝ) (i + 1)) 1 ?_ ?_
  · intro x hx
    simp only [Set.mem_iUnion, Finset.mem_insert, Finset.mem_singleton, exists_prop]
    by_cases h : x ≤ 1
    · exact ⟨0, Or.inl rfl, by simpa using ⟨hx.1, h⟩⟩
    · refine ⟨1, Or.inr rfl, ?_⟩
      simp only [Set.mem_Icc, Nat.cast_one]
      constructor <;> linarith [hx.2, not_le.1 h]
  · intro i hi
    simp

example : ((25 * 32 ^ 14 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((32 : ℝ) ^ (-((2 : ℝ) + 15))) ≤
    ENNReal.ofReal ((32 : ℝ) ^ (-(2 : ℝ))) :=
  net_count (N := 32) (D := 2) (25 * 32 ^ 14) (by norm_num) (by norm_num)

example : calB sz0 0 (1 / 2) 0 ≤ 2 * calB sz0 0 (1 / 3) 0 :=
  calB_shift_le sz0 0 (by norm_num) le_rfl (by rw [abs_of_nonneg (by norm_num)]; norm_num)

example : Complex.I.im / (1 + Complex.I.im) ≤ 1 - lemT Complex.I := one_sub_lemT_ge (by simp)

example : ‖msc Complex.I - msc (2 * Complex.I)‖ ≤ (1 : ℝ)⁻¹ * (1 : ℝ)⁻¹ * ‖Complex.I - 2 * Complex.I‖ :=
  msc_lip one_pos (by simp) (by norm_num)

example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) : ‖sz0.Gn 0 Complex.I ω x y‖ ≤ (1 : ℝ)⁻¹ :=
  Gn_entry_le sz0 0 ω one_pos (by simp) x y

example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ‖sz0.Gn 0 Complex.I ω x y - sz0.Gn 0 (2 * Complex.I) ω x y‖ ≤
      (1 : ℝ)⁻¹ * (1 : ℝ)⁻¹ * ‖Complex.I - 2 * Complex.I‖ :=
  Gn_entry_lip sz0 0 ω one_pos (by simp) (by norm_num) x y

example (a b : Zd 3 (sz0.L 0)) :
    ‖avg2 sz0 0 (fun _ _ => 1) a b - avg2 sz0 0 (fun _ _ => 0) a b‖ ≤ 1 :=
  avg2_lip sz0 0 _ _ (c := 1) (fun x y => by simp) a b

example (a b : Zd 3 (sz0.L 0)) :
    ‖profPM sz0 0 Complex.I a b - profPM sz0 0 ⟨0, 1 / 2⟩ a b‖ ≤
      12 * ((1 / 2 : ℝ))⁻¹ ^ 4 * ‖Complex.I - ⟨0, 1 / 2⟩‖ :=
  profPM_lip sz0 0 (η := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) a b

example (a b : Zd 3 (sz0.L 0)) :
    ‖profPP sz0 0 Complex.I a b - profPP sz0 0 ⟨0, 1 / 2⟩ a b‖ ≤
      12 * ((1 / 2 : ℝ))⁻¹ ^ 4 * ‖Complex.I - ⟨0, 1 / 2⟩‖ :=
  profPP_lip sz0 0 (η := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) a b

end Inst

end RBM.Endpoints
