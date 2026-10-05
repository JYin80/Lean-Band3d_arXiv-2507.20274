/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.FreeConvStability
import Mathlib.Algebra.Order.Chebyshev

/-!
# The free convolution `v ⊞ sc_t` against a regular reference density

Ticket T2190 (UN-07; design UN-D1 = T2162, `docs/reports/T2162-portmap.md:201`; consumers UN-12
`UNStep1Good`, BA-C2 `UNDensBARow`, the BA consumption of `UNCore`).  New mathematics, no RBM2D
source.  The only ports are inside RBM3D: the contraction argument of
`RBM3D/Universality/FreeConvStability.lean` (T2176, commit `52c856e`, itself a port of RBM2D
`c9a24cf`) is generalised there from `msc` to a reference that is only Lipschitz as a complex
function; the private lemmas used as models (file:line at `52c856e`) are `fcs_mk_zero` `:207`,
`fcs_norm_mk_zero` `:210`, `fcs_sub_ne_zero` `:252`, `fcs_stieltjesVec_im_pos` `:258`,
`fcs_stieltjesVec_differentiableAt` `:274`, `fcs_stieltjesVec_shift` `:283`, `fcsRect_convex`
`:303`, `fcs_sigma` `:323`, `fcs_g_lip`/`fcs_contract` `:449`/`:499`, `fcs_fixed` `:531` and
`fcs_core` `:628`; the model of target 1 is `freeConv_stieltjesVec_sub_le`
(`RBM3D/Universality/FreeConv.lean:149`, the case `s = 0`, `u = u'`).  The copies are `private`
and carry the prefix `FreeConvRegular_`.

All six statements are pinned by the release check `docs/tickets/checks/T2190-check.lean`
(only `Type` → `Type*` in the index binders differs).  Notation: `m = freeConvST u s z` is the
Stieltjes transform of `μ_u ⊞ sc_s` at `z` (`Im z > 0`), `a_i = (u_i - z - s m)⁻¹`, `N = card ι`.

* `freeConvST_sub_le` (target 1): the joint modulus
  `s² (Im m + Im m')² ‖m - m'‖ ≤ 2 (r + ‖z - z'‖)`.  From
  `(m - m')(1 - sP) = N⁻¹ Σ a_i a'_i (u'_i - u_i) + (z - z') P`, `P = N⁻¹ Σ a_i a'_i`,
  `|P| ≤ N⁻¹ Σ |a_i||a'_i| ≤ s⁻¹` (because `s N⁻¹ Σ |a_i|² = s Im m / (Im z + s Im m) < 1`) and
  `Re (1 - sP) ≥ (s/2) N⁻¹ Σ |a_i - conj a'_i|² ≥ (s/2)(Im m + Im m')²` (Cauchy–Schwarz).
* `freeConvST_norm_sq_le` (target 2): `s |m|² ≤ 1`.
* `unDens_freeConvST` (target 3): `UNDens` for `m_n = m_{u_n ⊞ sc_1}` with `Im m_n ≥ c` on the
  window (`C = 1` by target 2, `Lp = 1/(2c²)` by target 1), `ρ_n` the limit along `η ↓ 0` (Cauchy,
  from target 1 in the `η` direction), and the modulus `|Im m_n(E + iη)/π - ρ_n| ≤ η/c²`.
* `freeConv_stable_lip` (target 4): if `v` has Stieltjes transform `ε`-close to the rescaled
  reference `σ mref(σ(w + E₀))`, `σ = s^{-1/2}`, `s = 1 - t`, on the strip
  `|Re w| ≤ c₁`, `c₀ t/4 ≤ Im w ≤ 1/2`, and `mref` is bounded below in `Im` (`≥ c`), bounded
  (`≤ K`) and `Lp`-Lipschitz as a complex function on the box `|Re z - E₀| ≤ δ`, `0 < Im z ≤ 1`,
  then `‖freeConvST v t (iη) - mref(E₀ + iη)‖ ≤ C₀ (ε + t)` for `η ∈ (0, 1/4]`, and the limits
  `ρ, ρ₀` of `Im/π` as `η ↓ 0` exist with `|ρ - ρ₀| ≤ C₀ (ε + t)`.  Route: the Cauchy estimate on
  discs of radius `t c/8` needs no analyticity of the reference
  (`‖m_v ζ - m_v ω‖ ≤ 2ε + 2 Lp t c/8`), `t m_v` is then `1/2`-Lipschitz on the working rectangle,
  `F(ω) = iη + t m_v(ω)` maps the ball of radius `2t(ε + 4 Lp K t)` around `iη + t ref(iη)`
  into itself, Banach gives the fixed point, which is `iη + t freeConvST v t (iη)` by uniqueness
  (`freeConv_existsUnique`), and the fixed points are `2`-Lipschitz in `η`.
  Constants: `c₁ = min (δ/(4(1+A))) (1/8)`, `c₀ = min (c/64) (c/(16 K Lp)) (c₁/(8(K+1)))`,
  `C₀ = 2 + 8 Lp K + K + Lp (A + 1/4)`.
* `freeConv_stable_freeConvST` (target 5): target 4 at `mref = freeConvST u 1` (`K = 1` by target 2,
  `Lp = 1/(2c²)` by target 1); the constants depend on `(c, δ, A)` only.
* `unDens_not_eta_determined` (target 6, finding T2190a): the limit `ρ_n` of the merged pin
  `UNDens` is not determined by `m_n` on `Im z ≥ h_n` for any `h_n > 0`.
* Section 6 (namespace `FreeConvRegularInst`): the bridge `freeConvST (fun _ => 0) 1 = msc` and the
  compiled nonempty instances of all six targets.
-/

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-! ### 1. The joint modulus and the norm bound (targets 1, 2) -/

section Joint

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `a_i = (u_i - z - s m)⁻¹`. -/
private def FreeConvRegular_a (u : ι → ℝ) (s : ℝ) (z m : ℂ) (i : ι) : ℂ :=
  ((u i : ℂ) - z - (s : ℂ) * m)⁻¹

private lemma FreeConvRegular_card_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
  exact_mod_cast Fintype.card_pos

omit [Fintype ι] [Nonempty ι] in
private lemma FreeConvRegular_denom_im (u : ι → ℝ) (s : ℝ) (z m : ℂ) (i : ι) :
    ((u i : ℂ) - z - (s : ℂ) * m).im = -(z.im + s * m.im) := by
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.im_ofReal_mul]
  ring

omit [Fintype ι] [Nonempty ι] in
private lemma FreeConvRegular_denom_ne (u : ι → ℝ) {s : ℝ} (hs : 0 ≤ s) {z m : ℂ}
    (hz : 0 < z.im) (hm : 0 < m.im) (i : ι) : (u i : ℂ) - z - (s : ℂ) * m ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  rw [FreeConvRegular_denom_im, Complex.zero_im] at h2
  nlinarith [mul_nonneg hs hm.le]

omit [Fintype ι] [Nonempty ι] in
private lemma FreeConvRegular_a_im (u : ι → ℝ) (s : ℝ) (z m : ℂ) (i : ι) :
    (FreeConvRegular_a u s z m i).im =
      (z.im + s * m.im) * Complex.normSq (FreeConvRegular_a u s z m i) := by
  unfold FreeConvRegular_a
  rw [Complex.inv_im, Complex.normSq_inv, FreeConvRegular_denom_im]
  ring

/-- `N m = Σ a_i` from the equation `m = N⁻¹ Σ a_i`. -/
private lemma FreeConvRegular_sum_eq (u : ι → ℝ) (s : ℝ) (z m : ℂ)
    (heq : m = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((u i : ℂ) - z - (s : ℂ) * m)⁻¹) :
    (((Fintype.card ι : ℝ) : ℂ)) * m = ∑ i, FreeConvRegular_a u s z m i := by
  have hN : (((Fintype.card ι : ℝ) : ℂ)) ≠ 0 := by
    have := FreeConvRegular_card_pos (ι := ι)
    exact_mod_cast this.ne'
  have h2 : (((Fintype.card ι : ℝ) : ℂ)) = (Fintype.card ι : ℂ) := Complex.ofReal_natCast _
  have h1 : (((Fintype.card ι : ℝ) : ℂ)) * m =
      (((Fintype.card ι : ℝ) : ℂ)) * ((Fintype.card ι : ℂ)⁻¹ *
        ∑ i, ((u i : ℂ) - z - (s : ℂ) * m)⁻¹) := congrArg _ heq
  rw [h1, h2, mul_inv_cancel_left₀ (by rw [← h2]; exact hN)]
  rfl

/-- Mean square: `(N⁻¹ Σ f)² ≤ N⁻¹ Σ f²`, in the form `(Σ f)² ≤ N Σ f²`. -/
private lemma FreeConvRegular_sq_sum_le (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := f)
  simpa using h

/-- One point: with `a_i = (u_i - z - s m)⁻¹` and `Xs = Σ |a_i|²`,
`N Im m = Σ Im a_i = (Im z + s Im m) Xs`, `s Xs ≤ N` and `N |m|² ≤ Xs`. -/
private lemma FreeConvRegular_one (u : ι → ℝ) {s : ℝ} (hs : 0 ≤ s) {z m : ℂ} (hz : 0 < z.im)
    (hm : 0 < m.im)
    (heq : m = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((u i : ℂ) - z - (s : ℂ) * m)⁻¹) :
    (Fintype.card ι : ℝ) * m.im = ∑ i, (FreeConvRegular_a u s z m i).im ∧
    s * ∑ i, Complex.normSq (FreeConvRegular_a u s z m i) ≤ (Fintype.card ι : ℝ) ∧
    (Fintype.card ι : ℝ) * ‖m‖ ^ 2 ≤ ∑ i, Complex.normSq (FreeConvRegular_a u s z m i) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN : 0 < N := FreeConvRegular_card_pos
  have hsum := FreeConvRegular_sum_eq u s z m heq
  set Xs : ℝ := ∑ i, Complex.normSq (FreeConvRegular_a u s z m i) with hXs
  have h0 : N * m.im = ∑ i, (FreeConvRegular_a u s z m i).im := by
    have h := congrArg Complex.im hsum
    rw [Complex.im_ofReal_mul, Complex.im_sum] at h
    exact h
  have h1 : N * m.im = (z.im + s * m.im) * Xs := by
    rw [h0, hXs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => FreeConvRegular_a_im u s z m i
  have hpos : 0 < z.im + s * m.im := by nlinarith [mul_nonneg hs hm.le]
  have h2 : s * Xs ≤ N := by
    have h : s * Xs * (z.im + s * m.im) ≤ N * (z.im + s * m.im) := by
      have e : s * Xs * (z.im + s * m.im) = s * (N * m.im) := by rw [h1]; ring
      rw [e]; nlinarith [mul_pos hN hz]
    exact le_of_mul_le_mul_right h hpos
  have h3 : N * ‖m‖ ^ 2 ≤ Xs := by
    have hnorm : N * ‖m‖ ≤ ∑ i, ‖FreeConvRegular_a u s z m i‖ := by
      have h := congrArg norm hsum
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le] at h
      rw [h]; exact norm_sum_le _ _
    have hcs := FreeConvRegular_sq_sum_le (fun i => ‖FreeConvRegular_a u s z m i‖)
    have hXs' : ∑ i, ‖FreeConvRegular_a u s z m i‖ ^ 2 = Xs := by
      rw [hXs]; exact Finset.sum_congr rfl fun i _ => Complex.sq_norm _
    simp only [hXs'] at hcs
    have h4 : (N * ‖m‖) ^ 2 ≤ N * Xs := by
      calc (N * ‖m‖) ^ 2 ≤ (∑ i, ‖FreeConvRegular_a u s z m i‖) ^ 2 := by gcongr
        _ ≤ N * Xs := hcs
    have h5 : N * (N * ‖m‖ ^ 2) ≤ N * Xs := by nlinarith
    exact le_of_mul_le_mul_left h5 hN
  exact ⟨h0, h2, h3⟩

/-- Two points: the identity `(m - m')(1 - sP) = N⁻¹ Σ a_i a'_i (u'_i - u_i) + (z - z') P`,
`|P| ≤ s⁻¹`, `Re (1 - sP) ≥ (s/2)(Im m + Im m')²`, in the unnormalised form
`N` times each side. -/
private lemma FreeConvRegular_two (u u' : ι → ℝ) (r s : ℝ) (hs : 0 < s)
    (hr : ∀ i, |u i - u' i| ≤ r) {z z' m m' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im)
    (hm : 0 < m.im) (hm' : 0 < m'.im)
    (heq : m = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((u i : ℂ) - z - (s : ℂ) * m)⁻¹)
    (heq' : m' = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((u' i : ℂ) - z' - (s : ℂ) * m')⁻¹) :
    s ^ 2 * (m.im + m'.im) ^ 2 * ‖m - m'‖ ≤ 2 * (r + ‖z - z'‖) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN : 0 < N := FreeConvRegular_card_pos
  obtain ⟨h0, h2, -⟩ := FreeConvRegular_one u hs.le hz hm heq
  obtain ⟨h0', h2', -⟩ := FreeConvRegular_one u' hs.le hz' hm' heq'
  have hsum := FreeConvRegular_sum_eq u s z m heq
  have hsum' := FreeConvRegular_sum_eq u' s z' m' heq'
  set a := FreeConvRegular_a u s z m with ha
  set a' := FreeConvRegular_a u' s z' m' with ha'
  set Xs : ℝ := ∑ i, Complex.normSq (a i) with hXs
  set Xs' : ℝ := ∑ i, Complex.normSq (a' i) with hXs'
  have hr0 : 0 ≤ r := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact (abs_nonneg _).trans (hr i)
  -- the pointwise identity
  have hdiff : ∀ i, a i - a' i = a i * a' i *
      ((((u' i - u i : ℝ)) : ℂ) + ((z - z') + (s : ℂ) * (m - m'))) := by
    intro i
    have hd := FreeConvRegular_denom_ne u hs.le hz hm i
    have hd' := FreeConvRegular_denom_ne u' hs.le hz' hm' i
    simp only [ha, ha', FreeConvRegular_a]
    field_simp
    push_cast
    ring
  set Ps : ℂ := ∑ i, a i * a' i with hPs
  set Qs : ℂ := ∑ i, a i * a' i * (((u' i - u i : ℝ)) : ℂ) with hQs
  have h3 : (N : ℂ) * (m - m') = Qs + ((z - z') + (s : ℂ) * (m - m')) * Ps := by
    calc (N : ℂ) * (m - m') = ∑ i, (a i - a' i) := by
          rw [mul_sub, hsum, hsum', Finset.sum_sub_distrib]
      _ = ∑ i, (a i * a' i * (((u' i - u i : ℝ)) : ℂ) +
            ((z - z') + (s : ℂ) * (m - m')) * (a i * a' i)) :=
          Finset.sum_congr rfl fun i _ => by rw [hdiff i]; ring
      _ = Qs + ((z - z') + (s : ℂ) * (m - m')) * Ps := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h4 : (m - m') * ((N : ℂ) - (s : ℂ) * Ps) = Qs + (z - z') * Ps := by
    linear_combination h3
  -- bounds on `Ps`, `Qs`
  set T : ℝ := ∑ i, ‖a i‖ * ‖a' i‖ with hT
  have hTle : T ≤ (Xs + Xs') / 2 := by
    have : ∀ i ∈ (Finset.univ : Finset ι), ‖a i‖ * ‖a' i‖ ≤
        (Complex.normSq (a i) + Complex.normSq (a' i)) / 2 := by
      intro i _
      rw [← Complex.sq_norm, ← Complex.sq_norm]
      nlinarith [sq_nonneg (‖a i‖ - ‖a' i‖)]
    calc T ≤ ∑ i, (Complex.normSq (a i) + Complex.normSq (a' i)) / 2 := Finset.sum_le_sum this
      _ = (Xs + Xs') / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hPsn : ‖Ps‖ ≤ T := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => norm_mul _ _
  have hQsn : ‖Qs‖ ≤ r * T := by
    refine (norm_sum_le _ _).trans ?_
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have := hr i
    have h0' : 0 ≤ ‖a i‖ * ‖a' i‖ := by positivity
    nlinarith
  have hsT : s * T ≤ N := by
    have : s * ((Xs + Xs') / 2) ≤ N := by nlinarith
    calc s * T ≤ s * ((Xs + Xs') / 2) := mul_le_mul_of_nonneg_left hTle hs.le
      _ ≤ N := this
  -- the real part
  set S : ℝ := ∑ i, ((a i).im + (a' i).im) ^ 2 with hS
  have hSge : N * (m.im + m'.im) ^ 2 ≤ S := by
    have hcs := FreeConvRegular_sq_sum_le (fun i => (a i).im + (a' i).im)
    have hsum2 : ∑ i, ((a i).im + (a' i).im) = N * (m.im + m'.im) := by
      rw [Finset.sum_add_distrib, ← h0, ← h0']; ring
    simp only [hsum2] at hcs
    have h5 : N * (N * (m.im + m'.im) ^ 2) ≤ N * S := by nlinarith
    exact le_of_mul_le_mul_left h5 hN
  have hRe : 2 * Ps.re ≤ (Xs + Xs') - S := by
    have hpt : ∀ i ∈ (Finset.univ : Finset ι), 2 * (a i * a' i).re ≤
        (Complex.normSq (a i) + Complex.normSq (a' i)) - ((a i).im + (a' i).im) ^ 2 := by
      intro i _
      rw [Complex.mul_re, Complex.normSq_apply, Complex.normSq_apply]
      nlinarith [sq_nonneg ((a i).re - (a' i).re)]
    calc 2 * Ps.re = ∑ i, 2 * (a i * a' i).re := by
          rw [hPs, Complex.re_sum, Finset.mul_sum]
      _ ≤ ∑ i, ((Complex.normSq (a i) + Complex.normSq (a' i)) -
            ((a i).im + (a' i).im) ^ 2) := Finset.sum_le_sum hpt
      _ = (Xs + Xs') - S := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- `D = N - s Ps`
  set D : ℂ := (N : ℂ) - (s : ℂ) * Ps with hD
  have hDre : D.re = N - s * Ps.re := by
    rw [hD, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hDge : s * S / 2 ≤ D.re := by
    rw [hDre]
    nlinarith
  have hDn : ‖m - m'‖ * D.re ≤ (r + ‖z - z'‖) * T := by
    calc ‖m - m'‖ * D.re ≤ ‖m - m'‖ * ‖D‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (norm_nonneg _)
      _ = ‖(m - m') * D‖ := (norm_mul _ _).symm
      _ = ‖Qs + (z - z') * Ps‖ := by rw [hD, h4]
      _ ≤ ‖Qs‖ + ‖(z - z') * Ps‖ := norm_add_le _ _
      _ ≤ r * T + ‖z - z'‖ * T := by
          rw [norm_mul]
          exact add_le_add hQsn (mul_le_mul_of_nonneg_left hPsn (norm_nonneg _))
      _ = (r + ‖z - z'‖) * T := by ring
  have hμ : 0 ≤ ‖m - m'‖ := norm_nonneg _
  have hR : 0 ≤ r + ‖z - z'‖ := by positivity
  have key : ‖m - m'‖ * s ^ 2 * (N * (m.im + m'.im) ^ 2) ≤ 2 * (r + ‖z - z'‖) * N := by
    calc ‖m - m'‖ * s ^ 2 * (N * (m.im + m'.im) ^ 2) ≤ ‖m - m'‖ * s ^ 2 * S := by
          gcongr
      _ = 2 * (‖m - m'‖ * s * (s * S / 2)) := by ring
      _ ≤ 2 * (‖m - m'‖ * s * D.re) := by
          gcongr
      _ = 2 * (s * (‖m - m'‖ * D.re)) := by ring
      _ ≤ 2 * (s * ((r + ‖z - z'‖) * T)) := by
          gcongr
      _ = 2 * ((r + ‖z - z'‖) * (s * T)) := by ring
      _ ≤ 2 * ((r + ‖z - z'‖) * N) := by gcongr
      _ = 2 * (r + ‖z - z'‖) * N := by ring
  have key2 : (s ^ 2 * (m.im + m'.im) ^ 2 * ‖m - m'‖) * N ≤ (2 * (r + ‖z - z'‖)) * N := by
    nlinarith
  exact le_of_mul_le_mul_right key2 hN

end Joint

/-- **Target 1 (`freeConvST_sub_le`)**: the joint modulus of `(u, z) ↦ m_{u ⊞ sc_s}(z)`, for every
`s > 0`, every pair of vectors on the same index set and every pair of points of the upper half
plane (no window, no lower bound assumed; the lower bound of `Im` enters only through the left
side).  Route: `(m - m')(1 - sP) = N⁻¹ Σ a_i a'_i (u'_i - u_i) + (z - z') P`, `|P| ≤ s⁻¹`,
`Re (1 - sP) ≥ (s/2)(Im m + Im m')²`. -/
theorem freeConvST_sub_le :
    ∀ {ι : Type*} [Fintype ι] [Nonempty ι] (u u' : ι → ℝ) (r s : ℝ), 0 < s → (∀ i, |u i - u' i| ≤ r) →
      ∀ z z' : ℂ, 0 < z.im → 0 < z'.im →
        s ^ 2 * ((freeConvST u s z).im + (freeConvST u' s z').im) ^ 2 *
            ‖freeConvST u s z - freeConvST u' s z'‖ ≤ 2 * (r + ‖z - z'‖) := by
  intro ι _ _ u u' r s hs hr z z' hz hz'
  obtain ⟨hm, heq⟩ := isFreeConv51_freeConvST u hs.le z hz
  obtain ⟨hm', heq'⟩ := isFreeConv51_freeConvST u' hs.le z' hz'
  exact FreeConvRegular_two u u' r s hs hr hz hz' hm hm' heq heq'

/-- **Target 2 (`freeConvST_norm_sq_le`)**: `s |m_{u ⊞ sc_s}(z)|² ≤ 1`. -/
theorem freeConvST_norm_sq_le :
    ∀ {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ) (s : ℝ), 0 ≤ s → ∀ z : ℂ, 0 < z.im →
      s * ‖freeConvST u s z‖ ^ 2 ≤ 1 := by
  intro ι _ _ u s hs z hz
  obtain ⟨hm, heq⟩ := isFreeConv51_freeConvST u hs z hz
  obtain ⟨-, h2, h3⟩ := FreeConvRegular_one u hs hz hm heq
  have hN := FreeConvRegular_card_pos (ι := ι)
  have h4 : (Fintype.card ι : ℝ) * (s * ‖freeConvST u s z‖ ^ 2) ≤ (Fintype.card ι : ℝ) * 1 := by
    nlinarith
  exact le_of_mul_le_mul_left h4 hN

/-! ### 2. Generic helpers: limits along `η ↓ 0`, distances on a vertical line -/

/-- A function into a complete metric space that is Lipschitz on `(0, a]` has a limit as `x ↓ 0`. -/
private lemma FreeConvRegular_exists_tendsto {α : Type*} [MetricSpace α] [CompleteSpace α]
    (f : ℝ → α) {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (h : ∀ x ∈ Set.Ioc (0 : ℝ) a, ∀ y ∈ Set.Ioc (0 : ℝ) a, dist (f x) (f y) ≤ L * |x - y|) :
    ∃ p : α, Tendsto f (𝓝[>] 0) (𝓝 p) := by
  have hcau : Cauchy (map f (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun δ hδ => ⟨f '' Set.Ioo 0 (min (δ / (2 * (L + 1))) a), ?_, ?_⟩⟩
    · exact mem_map.mpr (mem_of_superset (Ioo_mem_nhdsGT (lt_min (by positivity) ha))
        (Set.subset_preimage_image _ _))
    · rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩ _ ⟨y, ⟨hy0, hy1⟩, rfl⟩
      have hm1 := min_le_left (δ / (2 * (L + 1))) a
      have hm2 := min_le_right (δ / (2 * (L + 1))) a
      have hl := h x ⟨hx0, by linarith⟩ y ⟨hy0, by linarith⟩
      have hxy : |x - y| < δ / (2 * (L + 1)) := by rw [abs_lt]; constructor <;> linarith
      have hL1 : 0 < L + 1 := by linarith
      calc dist (f x) (f y) ≤ L * |x - y| := hl
        _ ≤ (L + 1) * |x - y| := by nlinarith [abs_nonneg (x - y)]
        _ < (L + 1) * (δ / (2 * (L + 1))) := mul_lt_mul_of_pos_left hxy hL1
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
  exact CompleteSpace.complete hcau

private lemma FreeConvRegular_mk_zero (η : ℝ) : (⟨0, η⟩ : ℂ) = (η : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

private lemma FreeConvRegular_norm_mk_zero (η : ℝ) : ‖(⟨0, η⟩ : ℂ)‖ = |η| := by
  rw [FreeConvRegular_mk_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- Distance between two points of the same vertical line. -/
private lemma FreeConvRegular_norm_vert (x η η' : ℝ) : ‖(⟨x, η⟩ : ℂ) - ⟨x, η'⟩‖ = |η - η'| := by
  have : (⟨x, η⟩ : ℂ) - ⟨x, η'⟩ = ⟨0, η - η'⟩ := by apply Complex.ext <;> simp
  rw [this, FreeConvRegular_norm_mk_zero]

/-- Distance between two points of the same horizontal line. -/
private lemma FreeConvRegular_norm_horiz (x y η : ℝ) : ‖(⟨x, η⟩ : ℂ) - ⟨y, η⟩‖ = |x - y| := by
  have : (⟨x, η⟩ : ℂ) - ⟨y, η⟩ = ((x - y : ℝ) : ℂ) := by apply Complex.ext <;> simp
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-- The Lipschitz bound of `m_{u ⊞ sc_1}` from the lower bound of `Im` at the two points. -/
private lemma FreeConvRegular_lip_one {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ) {c : ℝ}
    (hc : 0 < c) {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im)
    (h : c ≤ (freeConvST u 1 z).im) (h' : c ≤ (freeConvST u 1 z').im) :
    ‖freeConvST u 1 z - freeConvST u 1 z'‖ ≤ 1 / (2 * c ^ 2) * ‖z - z'‖ := by
  have h1 := freeConvST_sub_le u u 0 1 one_pos (fun i => by simp) z z' hz hz'
  rw [one_pow, one_mul, zero_add] at h1
  have h2 : 4 * c ^ 2 ≤ ((freeConvST u 1 z).im + (freeConvST u 1 z').im) ^ 2 := by nlinarith
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (freeConvST u 1 z - freeConvST u 1 z')]

/-- `|m_{u ⊞ sc_1}| ≤ 1`. -/
private lemma FreeConvRegular_norm_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ)
    {z : ℂ} (hz : 0 < z.im) : ‖freeConvST u 1 z‖ ≤ 1 := by
  have h := freeConvST_norm_sq_le u 1 zero_le_one z hz
  rw [one_mul] at h
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg (freeConvST u 1 z)]

/-! ### 3. Target 3: the pin `UNDens` for `m_n = m_{u_n ⊞ sc_1}` -/

/-- **Target 3 (`unDens_freeConvST`)**: a sequence `m_n = m_{u_n ⊞ sc_1}` with `Im m_n ≥ c` on the
window satisfies the merged pin `UNDens` (`C = 1`, `Lp = 1/(2c²)`), and in addition the uniform
`η`-modulus of the limit that `UNDens` does not contain (target 6). -/
theorem unDens_freeConvST :
    ∀ {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)] (u : ∀ n, ι n → ℝ) (E δ c : ℝ),
      0 < δ → 0 < c →
      (∀ᶠ n in atTop, ∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 →
        c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) →
      ∃ ρ : ℕ → ℝ, UNDens (fun n => freeConvST (u n) 1) E ρ δ ∧
        ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 →
          |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n| ≤ η / c ^ 2 := by
  intro ι _ _ u E δ c hδ hc hev
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the `η`-modulus at one `n`
  have hηlip : ∀ n, (∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 →
        c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) →
      ∀ η ∈ Set.Ioc (0 : ℝ) 10, ∀ η' ∈ Set.Ioc (0 : ℝ) 10,
        dist ((freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi)
          ((freeConvST (u n) 1 ⟨E, η'⟩).im / Real.pi) ≤ 1 / (2 * c ^ 2 * Real.pi) * |η - η'| := by
    intro n hn η hη η' hη'
    have hl := FreeConvRegular_lip_one (u n) hc (z := ⟨E, η⟩) (z' := ⟨E, η'⟩) hη.1 hη'.1
      (hn E η (by simpa using hδ.le) hη.1 hη.2) (hn E η' (by simpa using hδ.le) hη'.1 hη'.2)
    rw [FreeConvRegular_norm_vert] at hl
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hpi]
    have h1 : |(freeConvST (u n) 1 ⟨E, η⟩).im - (freeConvST (u n) 1 ⟨E, η'⟩).im| ≤
        ‖freeConvST (u n) 1 ⟨E, η⟩ - freeConvST (u n) 1 ⟨E, η'⟩‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    rw [div_le_iff₀ hpi]
    calc |(freeConvST (u n) 1 ⟨E, η⟩).im - (freeConvST (u n) 1 ⟨E, η'⟩).im|
        ≤ 1 / (2 * c ^ 2) * |η - η'| := h1.trans hl
      _ = 1 / (2 * c ^ 2 * Real.pi) * |η - η'| * Real.pi := by field_simp
  have hex : ∀ n, (∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 →
        c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) →
      ∃ p : ℝ, Tendsto (fun η : ℝ => (freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 p) :=
    fun n hn => FreeConvRegular_exists_tendsto _ (a := 10) (by norm_num) (by positivity)
      (hηlip n hn)
  set ρ : ℕ → ℝ := fun n =>
    limUnder (𝓝[>] (0 : ℝ)) (fun η : ℝ => (freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi) with hρ
  have hlim : ∀ n, (∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 →
        c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) →
      Tendsto (fun η : ℝ => (freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n)) :=
    fun n hn => tendsto_nhds_limUnder (hex n hn)
  refine ⟨ρ, ⟨hδ, c, 1, 1 / (2 * c ^ 2), hc, one_pos, by positivity, ?_⟩, ?_⟩
  · filter_upwards [hev] with n hn
    refine ⟨fun x η hx hη hη10 => ⟨hn x η hx hη hη10, ?_⟩, fun x y η hx hy hη hη10 => ?_,
      hlim n hn⟩
    · exact (Complex.im_le_norm _).trans (FreeConvRegular_norm_le_one (u n) hη)
    · have hl := FreeConvRegular_lip_one (u n) hc (z := ⟨x, η⟩) (z' := ⟨y, η⟩) hη hη
        (hn x η hx hη hη10) (hn y η hy hη hη10)
      rw [FreeConvRegular_norm_horiz] at hl
      refine le_trans ?_ hl
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
  · filter_upwards [hev] with n hn η hη hη10
    have hb : ∀ η' ∈ Set.Ioo (0 : ℝ) η,
        |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - (freeConvST (u n) 1 ⟨E, η'⟩).im / Real.pi| ≤
          1 / (2 * c ^ 2 * Real.pi) * η := by
      intro η' hη'
      have := hηlip n hn η ⟨hη, hη10⟩ η' ⟨hη'.1, by linarith [hη'.2]⟩
      rw [Real.dist_eq] at this
      refine this.trans ?_
      have : |η - η'| ≤ η := by rw [abs_of_pos (by linarith [hη'.2])]; linarith [hη'.1]
      have h0 : 0 ≤ 1 / (2 * c ^ 2 * Real.pi) := by positivity
      exact mul_le_mul_of_nonneg_left this h0
    have hlimabs : Tendsto (fun η' : ℝ =>
        |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - (freeConvST (u n) 1 ⟨E, η'⟩).im / Real.pi|)
        (𝓝[>] 0) (𝓝 |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n|) :=
      ((tendsto_const_nhds.sub (hlim n hn)).abs)
    have h2 : |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n| ≤
        1 / (2 * c ^ 2 * Real.pi) * η :=
      le_of_tendsto hlimabs (eventually_of_mem (Ioo_mem_nhdsGT hη) hb)
    refine h2.trans ?_
    have h3 : 1 / (2 * c ^ 2 * Real.pi) * η = η / c ^ 2 * (1 / (2 * Real.pi)) := by
      field_simp
    rw [h3]
    have h4 : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    have h5 : 0 ≤ η / c ^ 2 := by positivity
    nlinarith

/-! ### 4. Target 6: the limit `ρ_n` of `UNDens` is not determined by `m_n` at height `h_n` -/

/-- **Target 6 (`unDens_not_eta_determined`, finding T2190a)**: the limit `ρ_n` in `UNDens` is
not determined by `m_n` on any region `Im z ≥ h_n`, `h_n > 0`: a sequence equal to `msc` there
satisfies `UNDens` with `ρ_n = ρ_sc(0) + 1/(2π)`, while `un_dens_msc_zero` gives
`UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1/2)`. -/
theorem unDens_not_eta_determined :
    ∀ h : ℕ → ℝ, (∀ n, 0 < h n) →
      ∃ (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ), UNDens m 0 ρ (1 / 2) ∧
        (∀ n (z : ℂ), h n ≤ z.im → m n z = msc z) ∧ ∀ n, ρ n = rhoSC 0 + 1 / (2 * Real.pi) := by
  intro h hh
  obtain ⟨-, c, C, Lp, hc, hC, hLp, hev⟩ := un_dens_msc_zero
  obtain ⟨n₀, hb, hl, ht⟩ := hev.exists
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨fun n z => msc z + (if z.im < h n then Complex.I / 2 else 0),
    fun _ => rhoSC 0 + 1 / (2 * Real.pi), ⟨by norm_num, c, C + 1 / 2, Lp, hc, by positivity, hLp,
      Eventually.of_forall fun n => ⟨?_, ?_, ?_⟩⟩, ?_, fun _ => rfl⟩
  · intro x η hx hη hη10
    obtain ⟨h1, h2⟩ := hb x η hx hη hη10
    by_cases hcase : η < h n
    · simp only [hcase, ite_true, Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
      constructor <;> linarith
    · simp only [hcase, ite_false, add_zero]
      constructor <;> linarith
  · intro x y η hx hy hη hη10
    have := hl x y η hx hy hη hη10
    by_cases hcase : η < h n
    · simp only [hcase, ite_true, Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
      convert this using 2
      ring
    · simp only [hcase, ite_false, add_zero]
      exact this
  · have h1 : Tendsto (fun η : ℝ => (msc ⟨0, η⟩).im / Real.pi + 1 / (2 * Real.pi)) (𝓝[>] 0)
        (𝓝 (rhoSC 0 + 1 / (2 * Real.pi))) := ht.add_const _
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (hh n)] with η hη
    have hcase : (⟨0, η⟩ : ℂ).im < h n := hη.2
    simp only [hcase, ite_true, Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
    field_simp
  · intro n z hz
    simp [not_lt.mpr hz]

/-! ### 5. Stability against a Lipschitz reference (targets 4, 5) -/

section Stability

/-- Facts about `σ = s^{-1/2}` for `s = 1 - t`, `0 < t ≤ 1/2`. -/
private lemma FreeConvRegular_sigma {s t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) (hs : s = 1 - t) :
    0 < Real.sqrt s ∧ 1 ≤ (Real.sqrt s)⁻¹ ∧ (Real.sqrt s)⁻¹ ≤ 1 + t := by
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hs1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr (by rw [hs]; linarith)
  refine ⟨hsq, ?_, ?_⟩
  · rw [le_inv_comm₀ one_pos hsq, inv_one]; exact hs1
  · have h : (1 + t)⁻¹ ≤ Real.sqrt s := by
      apply Real.le_sqrt_of_sq_le
      rw [inv_pow, hs, inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith [mul_pos ht ht, mul_pos (mul_pos ht ht) ht]
    calc (Real.sqrt s)⁻¹ ≤ ((1 + t)⁻¹)⁻¹ := inv_anti₀ (by positivity) h
      _ = 1 + t := inv_inv _

/-- The reference `m_ref(w) = σ mref(σ (w + E₀))`, `σ = s^{-1/2}`. -/
private def FreeConvRegular_ref (mref : ℂ → ℂ) (σ E₀ : ℝ) (w : ℂ) : ℂ :=
  (σ : ℂ) * mref ((σ : ℂ) * (w + E₀))

/-- The parameters of the stability argument and the hypotheses on them (all of them are
consequences of the hypotheses of `freeConv_stable_lip` and of the choice of `c₀, c₁`). -/
private structure FreeConvRegular_Par (c K Lp δ A c₀ c₁ σ t ε E₀ : ℝ) (mref : ℂ → ℂ) : Prop where
  hc : 0 < c
  hcK : c ≤ K
  hLp : 0 < Lp
  hδ : 0 < δ
  hA : 0 ≤ A
  hc₀ : 0 < c₀
  hc₀c : c₀ ≤ c / 2
  hc₁ : 0 < c₁
  hc₁8 : c₁ ≤ 1 / 8
  hc₁δ : c₁ * (1 + A) ≤ δ / 4
  ht : 0 < t
  htc : t ≤ c / 64
  htK : t * K * Lp ≤ c / 16
  ht1 : t * (K + 1) ≤ c₁ / 8
  hσ1 : 1 ≤ σ
  hσ2 : σ ≤ 1 + t
  hε0 : 0 ≤ ε
  hεc : ε ≤ c / 64
  hE₀ : |E₀| ≤ A
  hbox : ∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (mref z).im ∧ ‖mref z‖ ≤ K
  hlip : ∀ z z' : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 →
    |z'.re - E₀| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mref z - mref z'‖ ≤ Lp * ‖z - z'‖

variable {c K Lp δ A c₀ c₁ σ t ε E₀ : ℝ} {mref : ℂ → ℂ}

private lemma FreeConvRegular_Par.hK (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref) :
    0 < K := lt_of_lt_of_le P.hc P.hcK

private lemma FreeConvRegular_Par.tc₁ (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref) :
    t ≤ c₁ / 8 := by
  have := P.ht1; have := P.hK; have := P.ht
  nlinarith

private lemma FreeConvRegular_Par.tK₁ (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref) :
    t * K ≤ c₁ / 8 := by
  have := P.ht1; have := P.hK; have := P.ht
  nlinarith

private lemma FreeConvRegular_Par.tLp (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref) :
    t * Lp ≤ 1 / 16 := by
  have h1 := P.htK
  have h2 := P.hcK
  have h3 := P.hc
  have h4 := P.ht
  have h5 := P.hLp
  have h6 : t * Lp * c ≤ t * K * Lp := by nlinarith [mul_pos h4 h5]
  have h7 : t * Lp * c ≤ c / 16 := h6.trans h1
  by_contra hcon
  push Not at hcon
  nlinarith

private lemma FreeConvRegular_Par.σ2 (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref) :
    σ ≤ 65 / 64 := by
  have := P.hσ2; have := P.tc₁; have := P.hc₁8
  linarith

/-- Points of the strip are mapped by `w ↦ σ (w + E₀)` into the box. -/
private lemma FreeConvRegular_box (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {w : ℂ} (hre : |w.re| ≤ c₁) (him0 : 0 < w.im) (him1 : w.im ≤ 1 / 2) :
    |((σ : ℂ) * (w + E₀)).re - E₀| ≤ δ ∧ 0 < ((σ : ℂ) * (w + E₀)).im ∧
      ((σ : ℂ) * (w + E₀)).im ≤ 1 := by
  have hσ1 := P.hσ1
  have hσ2 := P.σ2
  have hre' : ((σ : ℂ) * (w + E₀)).re = σ * (w.re + E₀) := by
    rw [Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re]
  have him' : ((σ : ℂ) * (w + E₀)).im = σ * w.im := by
    rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hre']
    have e : σ * (w.re + E₀) - E₀ = σ * w.re + (σ - 1) * E₀ := by ring
    rw [e]
    have h1 : σ - 1 ≤ c₁ / 8 := by have := P.hσ2; have := P.tc₁; linarith
    have hA := P.hA
    calc |σ * w.re + (σ - 1) * E₀| ≤ |σ * w.re| + |(σ - 1) * E₀| := abs_add_le _ _
      _ = σ * |w.re| + (σ - 1) * |E₀| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ),
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - 1)]
      _ ≤ σ * c₁ + (σ - 1) * A := by
          have hE := P.hE₀
          have h2 : 0 ≤ σ - 1 := by linarith
          have h3 : 0 ≤ σ := by linarith
          exact add_le_add (mul_le_mul_of_nonneg_left hre h3) (mul_le_mul_of_nonneg_left hE h2)
      _ ≤ (1 + c₁ / 8) * c₁ + (c₁ / 8) * A := by
          have hc₁ := P.hc₁
          gcongr
          linarith
      _ ≤ 65 / 64 * (c₁ * (1 + A)) := by
          have hc₁ := P.hc₁
          have hc₁8 := P.hc₁8
          nlinarith
      _ ≤ 65 / 64 * (δ / 4) := by gcongr; exact P.hc₁δ
      _ ≤ δ := by linarith [P.hδ]
  · rw [him']; exact mul_pos (by linarith) him0
  · rw [him']; nlinarith

private lemma FreeConvRegular_ref_bound (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {w : ℂ} (hre : |w.re| ≤ c₁) (him0 : 0 < w.im) (him1 : w.im ≤ 1 / 2) :
    c ≤ (FreeConvRegular_ref mref σ E₀ w).im ∧ ‖FreeConvRegular_ref mref σ E₀ w‖ ≤ 2 * K := by
  obtain ⟨h1, h2, h3⟩ := FreeConvRegular_box P hre him0 him1
  obtain ⟨hb1, hb2⟩ := P.hbox _ h1 h2 h3
  have hσ1 := P.hσ1
  have hσ2 := P.σ2
  have hK := P.hK
  unfold FreeConvRegular_ref
  constructor
  · rw [Complex.im_ofReal_mul]; nlinarith [P.hc]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (mref ((σ : ℂ) * (w + E₀)))]

private lemma FreeConvRegular_ref_lip (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {w₁ w₂ : ℂ} (h1re : |w₁.re| ≤ c₁) (h1im0 : 0 < w₁.im) (h1im1 : w₁.im ≤ 1 / 2)
    (h2re : |w₂.re| ≤ c₁) (h2im0 : 0 < w₂.im) (h2im1 : w₂.im ≤ 1 / 2) :
    ‖FreeConvRegular_ref mref σ E₀ w₁ - FreeConvRegular_ref mref σ E₀ w₂‖ ≤
      2 * Lp * ‖w₁ - w₂‖ := by
  obtain ⟨a1, a2, a3⟩ := FreeConvRegular_box P h1re h1im0 h1im1
  obtain ⟨b1, b2, b3⟩ := FreeConvRegular_box P h2re h2im0 h2im1
  have hl := P.hlip _ _ a1 a2 a3 b1 b2 b3
  have hσ1 := P.hσ1
  have hσ2 := P.σ2
  have hLp := P.hLp
  have e : FreeConvRegular_ref mref σ E₀ w₁ - FreeConvRegular_ref mref σ E₀ w₂ =
      (σ : ℂ) * (mref ((σ : ℂ) * (w₁ + E₀)) - mref ((σ : ℂ) * (w₂ + E₀))) := by
    unfold FreeConvRegular_ref; ring
  have hzd : ‖(σ : ℂ) * (w₁ + E₀) - (σ : ℂ) * (w₂ + E₀)‖ = σ * ‖w₁ - w₂‖ := by
    rw [show (σ : ℂ) * (w₁ + E₀) - (σ : ℂ) * (w₂ + E₀) = (σ : ℂ) * (w₁ - w₂) by ring, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hzd] at hl
  calc σ * ‖mref ((σ : ℂ) * (w₁ + E₀)) - mref ((σ : ℂ) * (w₂ + E₀))‖
      ≤ σ * (Lp * (σ * ‖w₁ - w₂‖)) := mul_le_mul_of_nonneg_left hl (by linarith)
    _ = σ ^ 2 * Lp * ‖w₁ - w₂‖ := by ring
    _ ≤ 2 * Lp * ‖w₁ - w₂‖ := by
        have : σ ^ 2 ≤ 2 := by nlinarith
        gcongr

/-- The working rectangle. -/
private def FreeConvRegular_rect (B lo hi : ℝ) : Set ℂ :=
  {w : ℂ | |w.re| ≤ B ∧ lo ≤ w.im ∧ w.im ≤ hi}

private lemma FreeConvRegular_rect_convex (B lo hi : ℝ) :
    Convex ℝ (FreeConvRegular_rect B lo hi) := by
  intro x hx y hy a b ha hb hab
  simp only [FreeConvRegular_rect, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul] at hx hy ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · calc |a * x.re + b * y.re| ≤ |a * x.re| + |b * y.re| := abs_add_le _ _
      _ = a * |x.re| + b * |y.re| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B + b * B := by gcongr
      _ = B := by rw [← add_mul, hab, one_mul]
  · calc lo = a * lo + b * lo := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x.im + b * y.im :=
          add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
  · calc a * x.im + b * y.im ≤ a * hi + b * hi :=
          add_le_add (mul_le_mul_of_nonneg_left hx3 ha) (mul_le_mul_of_nonneg_left hy3 hb)
      _ = hi := by rw [← add_mul, hab, one_mul]

/-- The rectangle lies in the strip of the closeness hypothesis. -/
private lemma FreeConvRegular_rect_strip (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {w : ℂ} (hw : w ∈ FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8)) :
    |w.re| ≤ c₁ ∧ c₀ * t / 4 ≤ w.im ∧ w.im ≤ 1 / 2 := by
  obtain ⟨h1, h2, h3⟩ := hw
  have hc₁ := P.hc₁
  have hc₀c := P.hc₀c
  have ht := P.ht
  have hc := P.hc
  refine ⟨by linarith, ?_, by linarith⟩
  have : c₀ * t / 4 ≤ t * c / 4 := by nlinarith
  linarith

/-! #### Elementary facts about `mV` (copies of the private lemmas of `FreeConvStability.lean`) -/

private lemma FreeConvRegular_sub_ne_zero {a : ℝ} {ω : ℂ} (hω : 0 < ω.im) : (a : ℂ) - ω ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at h2
  linarith

private lemma FreeConvRegular_mV_im_pos {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {ω : ℂ}
    (hω : 0 < ω.im) : 0 < (mV v ω).im := by
  have hform : (mV v ω).im =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, ω.im / Complex.normSq ((v i : ℂ) - ω) := by
    unfold mV
    rw [show (((Fintype.card n : ℕ) : ℂ))⁻¹ = ((((Fintype.card n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast], Complex.im_ofReal_mul, Complex.im_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im]
    ring
  rw [hform]
  have hc : (0 : ℝ) < ((Fintype.card n : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  refine mul_pos (by positivity) (Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty)
  exact div_pos hω (Complex.normSq_pos.mpr (FreeConvRegular_sub_ne_zero hω))

private lemma FreeConvRegular_mV_differentiableAt {n : Type*} [Fintype n] (v : n → ℝ) {ω : ℂ}
    (hω : 0 < ω.im) : DifferentiableAt ℂ (mV v) ω := by
  have e : mV v = fun z => (Fintype.card n : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z)⁻¹ := rfl
  rw [e]
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum fun i _ => ?_
  exact ((differentiableAt_const _).sub differentiableAt_id).inv
    (FreeConvRegular_sub_ne_zero hω)

/-- Shift identity: the fixed-point equation for `m` is `m = m_v(z + t m)`. -/
private lemma FreeConvRegular_mV_shift {n : Type*} [Fintype n] (v : n → ℝ) (z t m : ℂ) :
    mV v (z + t * m) =
      ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - t * m)⁻¹ := by
  unfold mV
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

/-! #### The contraction -/

/-- **Cauchy estimate without analyticity of the reference, and mean value**: `t m_v` is
`1/2`-Lipschitz on the rectangle.  On a disc of radius `ρ = t c/8` inside the strip,
`‖m_v ζ - m_v ω‖ ≤ 2ε + 2 Lp ρ`, hence `‖m_v'(ω)‖ ≤ 2ε/ρ + 2 Lp`. -/
private lemma FreeConvRegular_contract (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {n : Type*} [Fintype n] (v : n → ℝ)
    (hyp : ∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV v w - FreeConvRegular_ref mref σ E₀ w‖ ≤ ε)
    {ω₁ ω₂ : ℂ} (h₁ : ω₁ ∈ FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8))
    (h₂ : ω₂ ∈ FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8)) :
    t * ‖mV v ω₂ - mV v ω₁‖ ≤ 1 / 2 * ‖ω₂ - ω₁‖ := by
  have hc := P.hc
  have ht := P.ht
  have hLp := P.hLp
  have hc₁ := P.hc₁
  have hc₁8 := P.hc₁8
  have hc₀c := P.hc₀c
  have hc₀ := P.hc₀
  set ρ : ℝ := t * c / 8 with hρ
  have hρpos : 0 < ρ := by positivity
  have htcK : t * c ≤ t * K := mul_le_mul_of_nonneg_left P.hcK ht.le
  have hρ1 : ρ ≤ c₁ / 64 := by
    have := P.tK₁
    rw [hρ]; linarith
  set Cst : ℝ := (2 * ε + 2 * Lp * ρ) / ρ with hCst
  have hrect_im : ∀ x ∈ FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8), 0 < x.im := fun x hx =>
    lt_of_lt_of_le (by positivity) hx.2.1
  -- the closed ball around a point of the rectangle lies in the strip
  have hball : ∀ x ∈ FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8),
      ∀ w ∈ Metric.closedBall x ρ,
      |w.re| ≤ c₁ ∧ c₀ * t / 4 ≤ w.im ∧ w.im ≤ 1 / 2 ∧ 0 < w.im := by
    intro x hx w hw
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre : |w.re - x.re| ≤ ρ := by
      have := Complex.abs_re_le_norm (w - x); rw [Complex.sub_re] at this; linarith
    have him : |w.im - x.im| ≤ ρ := by
      have := Complex.abs_im_le_norm (w - x); rw [Complex.sub_im] at this; linarith
    rw [abs_le] at hre him hx1
    have h4 : c₀ * t / 4 ≤ t * c / 8 := by nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · rw [hρ] at him; linarith
    · linarith
    · rw [hρ] at him
      have : 0 < t * c / 8 := by positivity
      linarith
  have hderiv : ∀ x ∈ FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8), ‖deriv (mV v) x‖ ≤ Cst := by
    intro x hx
    set g : ℂ → ℂ := fun ζ => mV v ζ - mV v x with hg
    have hdiff : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ g w := fun w hw =>
      (FreeConvRegular_mV_differentiableAt v hw).sub_const _
    have hU : DifferentiableOn ℂ g {w : ℂ | 0 < w.im} := fun w hw =>
      (hdiff w hw).differentiableWithinAt
    have hsub : Metric.closedBall x ρ ⊆ {w : ℂ | 0 < w.im} := fun w hw =>
      (hball x hx w hw).2.2.2
    have hxs := FreeConvRegular_rect_strip P hx
    have hbound : ∀ ζ ∈ Metric.sphere x ρ, ‖g ζ‖ ≤ 2 * ε + 2 * Lp * ρ := by
      intro ζ hζ
      obtain ⟨h1, h2, h3, h4⟩ := hball x hx ζ (Metric.sphere_subset_closedBall hζ)
      have hζx : ‖ζ - x‖ = ρ := by rw [← dist_eq_norm]; exact hζ
      have a1 := hyp ζ h1 h2 h3
      have a2 := hyp x hxs.1 hxs.2.1 hxs.2.2
      have a3 := FreeConvRegular_ref_lip P (w₁ := ζ) (w₂ := x) h1 h4 h3 hxs.1 (hrect_im x hx)
        hxs.2.2
      rw [hζx] at a3
      have e : g ζ = (mV v ζ - FreeConvRegular_ref mref σ E₀ ζ) +
          (FreeConvRegular_ref mref σ E₀ ζ - FreeConvRegular_ref mref σ E₀ x) -
          (mV v x - FreeConvRegular_ref mref σ E₀ x) := by
        simp only [hg]; ring
      rw [e]
      calc ‖(mV v ζ - FreeConvRegular_ref mref σ E₀ ζ) +
            (FreeConvRegular_ref mref σ E₀ ζ - FreeConvRegular_ref mref σ E₀ x) -
            (mV v x - FreeConvRegular_ref mref σ E₀ x)‖
          ≤ ‖(mV v ζ - FreeConvRegular_ref mref σ E₀ ζ) +
              (FreeConvRegular_ref mref σ E₀ ζ - FreeConvRegular_ref mref σ E₀ x)‖ +
            ‖mV v x - FreeConvRegular_ref mref σ E₀ x‖ := norm_sub_le _ _
        _ ≤ ‖mV v ζ - FreeConvRegular_ref mref σ E₀ ζ‖ +
              ‖FreeConvRegular_ref mref σ E₀ ζ - FreeConvRegular_ref mref σ E₀ x‖ +
            ‖mV v x - FreeConvRegular_ref mref σ E₀ x‖ := by
              gcongr; exact norm_add_le _ _
        _ ≤ ε + 2 * Lp * ρ + ε := by gcongr
        _ = 2 * ε + 2 * Lp * ρ := by ring
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos
      (hU.diffContOnCl_ball hsub) hbound
    rwa [show deriv g x = deriv (mV v) x from deriv_sub_const _] at this
  have hmv := (FreeConvRegular_rect_convex (c₁ / 2) (t * c / 4) (3 / 8)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => FreeConvRegular_mV_differentiableAt v (hrect_im x hx)) hderiv h₁ h₂
  have htC : t * Cst ≤ 1 / 2 := by
    have e : t * Cst = 16 * ε / c + 2 * Lp * t := by
      rw [hCst, hρ]; field_simp; ring
    rw [e]
    have h1 : 16 * ε / c ≤ 1 / 4 := by
      rw [div_le_iff₀ hc]; have := P.hεc; linarith
    have h2 : 2 * Lp * t ≤ 1 / 8 := by have := P.tLp; nlinarith
    linarith
  calc t * ‖mV v ω₂ - mV v ω₁‖ ≤ t * (Cst * ‖ω₂ - ω₁‖) := mul_le_mul_of_nonneg_left hmv ht.le
    _ = (t * Cst) * ‖ω₂ - ω₁‖ := by ring
    _ ≤ 1 / 2 * ‖ω₂ - ω₁‖ := mul_le_mul_of_nonneg_right htC (norm_nonneg _)

/-! #### The fixed point -/

/-- **Fixed point near `ω* = iη + t ref(iη)`** (Banach), identified with `freeConvST` by the
uniqueness half of `freeConv_existsUnique`. -/
private lemma FreeConvRegular_fixed (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ)
    (hyp : ∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV v w - FreeConvRegular_ref mref σ E₀ w‖ ≤ ε)
    {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ((⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩) ∈
        FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8) ∧
      ‖((⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩) -
        ((⟨0, η⟩ : ℂ) + (t : ℂ) * FreeConvRegular_ref mref σ E₀ ⟨0, η⟩)‖ ≤
          2 * t * (ε + 4 * Lp * K * t) := by
  have hc := P.hc
  have ht := P.ht
  have hLp := P.hLp
  have hK := P.hK
  have hc₁ := P.hc₁
  have hc₁8 := P.hc₁8
  have htK₁ := P.tK₁
  set R := FreeConvRegular_rect (c₁ / 2) (t * c / 4) (3 / 8) with hR
  -- the point `iη` and `M = ref(iη)`
  have hre0 : |(⟨0, η⟩ : ℂ).re| ≤ c₁ := by
    change |(0 : ℝ)| ≤ c₁
    rw [abs_zero]; exact hc₁.le
  have him0 : 0 < (⟨0, η⟩ : ℂ).im := hη
  have him1 : (⟨0, η⟩ : ℂ).im ≤ 1 / 2 := by change η ≤ 1 / 2; linarith
  set M := FreeConvRegular_ref mref σ E₀ ⟨0, η⟩ with hM
  obtain ⟨hMim, hMn⟩ := FreeConvRegular_ref_bound P hre0 him0 him1
  rw [← hM] at hMim hMn
  have hMre : |M.re| ≤ 2 * K := (Complex.abs_re_le_norm M).trans hMn
  have hMimle : M.im ≤ 2 * K := (le_abs_self _).trans ((Complex.abs_im_le_norm M).trans hMn)
  set ωs : ℂ := (⟨0, η⟩ : ℂ) + (t : ℂ) * M with hωs
  have hωs_re : ωs.re = t * M.re := by simp [ωs]
  have hωs_im : ωs.im = η + t * M.im := by simp [ωs]
  set r : ℝ := 2 * t * (ε + 4 * Lp * K * t) with hr
  have hε0 := P.hε0
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have htcK : t * c ≤ t * K := mul_le_mul_of_nonneg_left P.hcK ht.le
  have hr1 : r ≤ 3 * (t * c) / 4 := by
    have e : r = 2 * t * ε + 8 * t * (t * K * Lp) := by rw [hr]; ring
    have h1 : 2 * t * ε ≤ 2 * t * (c / 64) := mul_le_mul_of_nonneg_left P.hεc (by positivity)
    have h2 : 8 * t * (t * K * Lp) ≤ 8 * t * (c / 16) :=
      mul_le_mul_of_nonneg_left P.htK (by positivity)
    rw [e]; nlinarith [mul_pos ht hc]
  have hωsre : |ωs.re| ≤ 2 * (t * K) := by
    rw [hωs_re, abs_mul, abs_of_pos ht]; nlinarith
  have hωsim_lo : t * c ≤ ωs.im := by
    rw [hωs_im]; nlinarith
  have hωsim_hi : ωs.im ≤ 1 / 4 + 2 * (t * K) := by
    rw [hωs_im]; nlinarith
  set S := Metric.closedBall ωs r with hS
  have hSC : S ⊆ R := by
    intro w hw
    rw [hS, Metric.mem_closedBall, dist_eq_norm] at hw
    have hre : |w.re - ωs.re| ≤ r := by
      have := Complex.abs_re_le_norm (w - ωs); rw [Complex.sub_re] at this; linarith
    have him : |w.im - ωs.im| ≤ r := by
      have := Complex.abs_im_le_norm (w - ωs); rw [Complex.sub_im] at this; linarith
    rw [abs_le] at hre him hωsre
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · linarith
    · linarith
  set F : ℂ → ℂ := fun w => (⟨0, η⟩ : ℂ) + (t : ℂ) * mV v w with hF
  have hFdist : ∀ x ∈ R, ∀ y ∈ R, dist (F x) (F y) ≤ 1 / 2 * dist x y := by
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    have e : F x - F y = (t : ℂ) * (mV v x - mV v y) := by
      simp only [F]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact FreeConvRegular_contract P v hyp hy hx
  have hωsS : ωs ∈ S := Metric.mem_closedBall_self hr0
  have hωsR : ωs ∈ R := hSC hωsS
  have hωss := FreeConvRegular_rect_strip P hωsR
  have hωsim0 : 0 < ωs.im := lt_of_lt_of_le (by positivity) hωsR.2.1
  have hFωs : ‖F ωs - ωs‖ ≤ t * (ε + 4 * Lp * K * t) := by
    have e : F ωs - ωs = (t : ℂ) * ((mV v ωs - FreeConvRegular_ref mref σ E₀ ωs) +
        (FreeConvRegular_ref mref σ E₀ ωs - M)) := by
      simp only [F, hωs]; ring
    have h1 := hyp ωs hωss.1 hωss.2.1 hωss.2.2
    have h2 := FreeConvRegular_ref_lip P (w₁ := ωs) (w₂ := ⟨0, η⟩) hωss.1 hωsim0 hωss.2.2
      hre0 him0 him1
    rw [← hM] at h2
    have h3 : ‖ωs - (⟨0, η⟩ : ℂ)‖ ≤ 2 * (t * K) := by
      have : ωs - (⟨0, η⟩ : ℂ) = (t : ℂ) * M := by simp only [hωs]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
      nlinarith
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    refine mul_le_mul_of_nonneg_left ?_ ht.le
    calc ‖(mV v ωs - FreeConvRegular_ref mref σ E₀ ωs) + (FreeConvRegular_ref mref σ E₀ ωs - M)‖
        ≤ ‖mV v ωs - FreeConvRegular_ref mref σ E₀ ωs‖ +
          ‖FreeConvRegular_ref mref σ E₀ ωs - M‖ := norm_add_le _ _
      _ ≤ ε + 2 * Lp * ‖ωs - (⟨0, η⟩ : ℂ)‖ := add_le_add h1 h2
      _ ≤ ε + 2 * Lp * (2 * (t * K)) := by gcongr
      _ = ε + 4 * Lp * K * t := by ring
  have hmaps : Set.MapsTo F S S := by
    intro w hw
    have hwC := hSC hw
    rw [hS, Metric.mem_closedBall] at hw ⊢
    calc dist (F w) ωs ≤ dist (F w) (F ωs) + dist (F ωs) ωs := dist_triangle _ _ _
      _ ≤ 1 / 2 * dist w ωs + t * (ε + 4 * Lp * K * t) :=
          add_le_add (hFdist w hwC ωs hωsR) (by rw [dist_eq_norm]; exact hFωs)
      _ ≤ 1 / 2 * r + t * (ε + 4 * Lp * K * t) := by gcongr
      _ = r := by rw [hr]; ring
  have hcontr : ContractingWith (2⁻¹ : NNReal) (hmaps.restrict F S S) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [Set.MapsTo.val_restrict_apply]
    have := hFdist x (hSC x.2) y (hSC y.2)
    simpa using this
  obtain ⟨y, hyS, hyfix, -, -⟩ :=
    hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps hωsS (edist_ne_top _ _)
  have hyC := hSC hyS
  have hyim : 0 < y.im := lt_of_lt_of_le (by positivity) hyC.2.1
  set m := mV v y with hm
  have hmim : 0 < m.im := FreeConvRegular_mV_im_pos v hyim
  have hFy : (⟨0, η⟩ : ℂ) + (t : ℂ) * m = y := hyfix
  have heq : m = ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - ⟨0, η⟩ - (t : ℂ) * m)⁻¹ := by
    rw [← FreeConvRegular_mV_shift, hFy]
  have hz : 0 < (⟨0, η⟩ : ℂ).im := hη
  have hfc : freeConvST v t ⟨0, η⟩ = m :=
    (freeConv_existsUnique v ht.le hz).unique (isFreeConv51_freeConvST v ht.le _ hz) ⟨hmim, heq⟩
  have hW : (⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩ = y := by rw [hfc, hFy]
  rw [hW]
  refine ⟨hyC, ?_⟩
  rw [hS, Metric.mem_closedBall, dist_eq_norm] at hyS
  exact hyS

/-! #### The reference against `mref`, the limit `η ↓ 0` and the core estimate -/

/-- `‖ref(iη) - mref(E₀ + iη)‖ ≤ (σ - 1) K + Lp (σ - 1)(|E₀| + η) ≤ t (K + Lp (A + 1/4))`. -/
private lemma FreeConvRegular_ref_close (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ‖FreeConvRegular_ref mref σ E₀ ⟨0, η⟩ - mref ⟨E₀, η⟩‖ ≤ t * (K + Lp * (A + 1 / 4)) := by
  have hc₁ := P.hc₁
  have hLp := P.hLp
  have hK := P.hK
  have hA := P.hA
  have ht := P.ht
  have hσ1 := P.hσ1
  have hσt : σ - 1 ≤ t := by have := P.hσ2; linarith
  have hre0 : |(⟨0, η⟩ : ℂ).re| ≤ c₁ := by
    change |(0 : ℝ)| ≤ c₁
    rw [abs_zero]; exact hc₁.le
  have him0 : 0 < (⟨0, η⟩ : ℂ).im := hη
  have him1 : (⟨0, η⟩ : ℂ).im ≤ 1 / 2 := by change η ≤ 1 / 2; linarith
  obtain ⟨h1, h2, h3⟩ := FreeConvRegular_box P hre0 him0 him1
  set z₀ : ℂ := (σ : ℂ) * ((⟨0, η⟩ : ℂ) + E₀) with hz₀
  obtain ⟨-, hb₀⟩ := P.hbox z₀ h1 h2 h3
  have hz₁a : |(⟨E₀, η⟩ : ℂ).re - E₀| ≤ δ := by
    change |E₀ - E₀| ≤ δ
    rw [sub_self, abs_zero]; exact P.hδ.le
  have hz₁b : 0 < (⟨E₀, η⟩ : ℂ).im := hη
  have hz₁c : (⟨E₀, η⟩ : ℂ).im ≤ 1 := by change η ≤ 1; linarith
  have hl := P.hlip z₀ ⟨E₀, η⟩ h1 h2 h3 hz₁a hz₁b hz₁c
  have e : FreeConvRegular_ref mref σ E₀ ⟨0, η⟩ - mref ⟨E₀, η⟩ =
      ((σ - 1 : ℝ) : ℂ) * mref z₀ + (mref z₀ - mref ⟨E₀, η⟩) := by
    unfold FreeConvRegular_ref; push_cast; ring
  have hzd : z₀ - (⟨E₀, η⟩ : ℂ) = ((σ - 1 : ℝ) : ℂ) * ((E₀ : ℂ) + (η : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [hz₀] <;> ring
  have hzn : ‖z₀ - (⟨E₀, η⟩ : ℂ)‖ ≤ t * (A + 1 / 4) := by
    rw [hzd, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h4 : ‖(E₀ : ℂ) + (η : ℂ) * Complex.I‖ ≤ A + 1 / 4 := by
      calc ‖(E₀ : ℂ) + (η : ℂ) * Complex.I‖ ≤ ‖(E₀ : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |E₀| + η := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hη]
        _ ≤ A + 1 / 4 := by linarith [P.hE₀]
    exact mul_le_mul hσt h4 (norm_nonneg _) ht.le
  rw [e]
  calc ‖((σ - 1 : ℝ) : ℂ) * mref z₀ + (mref z₀ - mref ⟨E₀, η⟩)‖
      ≤ ‖((σ - 1 : ℝ) : ℂ) * mref z₀‖ + ‖mref z₀ - mref ⟨E₀, η⟩‖ := norm_add_le _ _
    _ ≤ t * K + Lp * (t * (A + 1 / 4)) := by
        refine add_le_add ?_ (hl.trans (mul_le_mul_of_nonneg_left hzn hLp.le))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        exact mul_le_mul hσt hb₀ (norm_nonneg _) ht.le
    _ = t * (K + Lp * (A + 1 / 4)) := by ring

/-- **The core estimate and the limit `η ↓ 0`** (the generalisation of `fcs_core` of
`FreeConvStability.lean` from `msc` to a Lipschitz reference). -/
private lemma FreeConvRegular_core (P : FreeConvRegular_Par c K Lp δ A c₀ c₁ σ t ε E₀ mref)
    {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ)
    (hyp : ∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV v w - FreeConvRegular_ref mref σ E₀ w‖ ≤ ε) :
    ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
      Tendsto (fun η : ℝ => (mref ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
      |ρ - ρ₀| ≤ (2 + 8 * Lp * K + K + Lp * (A + 1 / 4)) * (ε + t) ∧
      ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4), ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖ ≤
        (2 + 8 * Lp * K + K + Lp * (A + 1 / 4)) * (ε + t) := by
  have ht := P.ht
  have hLp := P.hLp
  have hK := P.hK
  have hA := P.hA
  have hε0 := P.hε0
  set C₀ : ℝ := 2 + 8 * Lp * K + K + Lp * (A + 1 / 4) with hC₀
  set W : ℝ → ℂ := fun η => (⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩ with hW
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hfcW : ∀ η : ℝ, (W η - ⟨0, η⟩) / t = freeConvST v t ⟨0, η⟩ := fun η => by
    simp only [W]; field_simp; ring
  have hfcsv : ∀ η : ℝ, 0 < η → freeConvST v t ⟨0, η⟩ = mV v (W η) := fun η hη => by
    simp only [W]
    rw [FreeConvRegular_mV_shift]
    exact (isFreeConv51_freeConvST v ht.le _ hη).2
  -- the pointwise bound against `ref`
  have hbound : ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
      ‖freeConvST v t ⟨0, η⟩ - FreeConvRegular_ref mref σ E₀ ⟨0, η⟩‖ ≤
        2 * (ε + 4 * Lp * K * t) := by
    rintro η ⟨hη, hηle⟩
    have h := (FreeConvRegular_fixed P v hyp hη hηle).2
    have e : ((⟨0, η⟩ : ℂ) + (t : ℂ) * freeConvST v t ⟨0, η⟩) -
        ((⟨0, η⟩ : ℂ) + (t : ℂ) * FreeConvRegular_ref mref σ E₀ ⟨0, η⟩) =
        (t : ℂ) * (freeConvST v t ⟨0, η⟩ - FreeConvRegular_ref mref σ E₀ ⟨0, η⟩) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at h
    have h2 : t * ‖freeConvST v t ⟨0, η⟩ - FreeConvRegular_ref mref σ E₀ ⟨0, η⟩‖ ≤
        t * (2 * (ε + 4 * Lp * K * t)) := by linarith
    exact le_of_mul_le_mul_left h2 ht
  -- the pointwise bound against `mref`
  have hfinal : ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
      ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖ ≤ C₀ * (ε + t) := by
    rintro η ⟨hη, hηle⟩
    have h1 := hbound η ⟨hη, hηle⟩
    have h2 := FreeConvRegular_ref_close P hη hηle
    have ha : 0 ≤ 8 * Lp * K + K + Lp * (A + 1 / 4) := by positivity
    calc ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖
        = ‖(freeConvST v t ⟨0, η⟩ - FreeConvRegular_ref mref σ E₀ ⟨0, η⟩) +
            (FreeConvRegular_ref mref σ E₀ ⟨0, η⟩ - mref ⟨E₀, η⟩)‖ := by ring_nf
      _ ≤ ‖freeConvST v t ⟨0, η⟩ - FreeConvRegular_ref mref σ E₀ ⟨0, η⟩‖ +
            ‖FreeConvRegular_ref mref σ E₀ ⟨0, η⟩ - mref ⟨E₀, η⟩‖ := norm_add_le _ _
      _ ≤ 2 * (ε + 4 * Lp * K * t) + t * (K + Lp * (A + 1 / 4)) := add_le_add h1 h2
      _ ≤ C₀ * (ε + t) := by
          rw [hC₀]
          nlinarith [mul_nonneg ha hε0]
  -- the fixed points are `2`-Lipschitz in `η`
  have hWlip : ∀ η₁ ∈ Set.Ioc (0 : ℝ) (1 / 4), ∀ η₂ ∈ Set.Ioc (0 : ℝ) (1 / 4),
      dist (W η₁) (W η₂) ≤ 2 * |η₁ - η₂| := by
    rintro η₁ ⟨h1, h1'⟩ η₂ ⟨h2, h2'⟩
    have hC1 := (FreeConvRegular_fixed P v hyp h1 h1').1
    have hC2 := (FreeConvRegular_fixed P v hyp h2 h2').1
    have hc := FreeConvRegular_contract P v hyp hC2 hC1
    have e : W η₁ - W η₂ = (⟨0, η₁ - η₂⟩ : ℂ) +
        (t : ℂ) * (mV v (W η₁) - mV v (W η₂)) := by
      rw [← hfcsv η₁ h1, ← hfcsv η₂ h2]
      simp only [W]
      apply Complex.ext <;> simp <;> ring
    have hc' : t * ‖mV v (W η₁) - mV v (W η₂)‖ ≤ 1 / 2 * ‖W η₁ - W η₂‖ := hc
    have h3 : ‖W η₁ - W η₂‖ ≤ |η₁ - η₂| + 1 / 2 * ‖W η₁ - W η₂‖ := by
      calc ‖W η₁ - W η₂‖ = ‖(⟨0, η₁ - η₂⟩ : ℂ) +
            (t : ℂ) * (mV v (W η₁) - mV v (W η₂))‖ := by rw [e]
        _ ≤ ‖(⟨0, η₁ - η₂⟩ : ℂ)‖ + ‖(t : ℂ) * (mV v (W η₁) - mV v (W η₂))‖ := norm_add_le _ _
        _ ≤ |η₁ - η₂| + 1 / 2 * ‖W η₁ - W η₂‖ := by
          rw [FreeConvRegular_norm_mk_zero, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg ht.le]
          linarith
    rw [dist_eq_norm]
    linarith
  obtain ⟨W₀, hW₀⟩ := FreeConvRegular_exists_tendsto W (a := 1 / 4) (L := 2) (by norm_num)
    (by norm_num) hWlip
  have hmk : Tendsto (fun η : ℝ => (⟨0, η⟩ : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun η : ℝ => (η : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.mul continuous_const
    have h0 := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul] at h0
    simp_rw [FreeConvRegular_mk_zero]
    exact h0.mono_left nhdsWithin_le_nhds
  have hfc : Tendsto (fun η : ℝ => freeConvST v t ⟨0, η⟩) (𝓝[>] 0) (𝓝 ((W₀ - 0) / t)) :=
    ((hW₀.sub hmk).div_const (t : ℂ)).congr hfcW
  set m₀ := (W₀ - 0) / (t : ℂ) with hm₀
  -- the limit of the reference
  have hmlip : ∀ η ∈ Set.Ioc (0 : ℝ) 1, ∀ η' ∈ Set.Ioc (0 : ℝ) 1,
      dist (mref ⟨E₀, η⟩) (mref ⟨E₀, η'⟩) ≤ Lp * |η - η'| := by
    rintro η ⟨h1, h1'⟩ η' ⟨h2, h2'⟩
    have ha : ∀ x : ℝ, |(⟨E₀, x⟩ : ℂ).re - E₀| ≤ δ := fun x => by
      change |E₀ - E₀| ≤ δ
      rw [sub_self, abs_zero]; exact P.hδ.le
    have := P.hlip ⟨E₀, η⟩ ⟨E₀, η'⟩ (ha η) h1 h1' (ha η') h2 h2'
    rw [FreeConvRegular_norm_vert] at this
    rwa [dist_eq_norm]
  obtain ⟨p, hp⟩ := FreeConvRegular_exists_tendsto (fun η : ℝ => mref ⟨E₀, η⟩) (a := 1)
    (L := Lp) one_pos hLp.le hmlip
  have hdiff : ‖m₀ - p‖ ≤ C₀ * (ε + t) := by
    have hlim : Tendsto (fun η : ℝ => ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖) (𝓝[>] 0)
        (𝓝 ‖m₀ - p‖) := (hfc.sub hp).norm
    exact le_of_tendsto hlim (eventually_of_mem (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
      hfinal)
  refine ⟨m₀.im / Real.pi, p.im / Real.pi, ((Complex.continuous_im.tendsto m₀).comp hfc).div_const
    Real.pi, ((Complex.continuous_im.tendsto p).comp hp).div_const Real.pi, ?_, hfinal⟩
  rw [← sub_div, abs_div, abs_of_pos Real.pi_pos]
  have h1 : |m₀.im - p.im| ≤ ‖m₀ - p‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  calc |m₀.im - p.im| / Real.pi ≤ C₀ * (ε + t) / Real.pi := by
        gcongr; exact h1.trans hdiff
    _ ≤ C₀ * (ε + t) := by
        have h0 : 0 ≤ C₀ * (ε + t) := by positivity
        exact div_le_self h0 (by linarith [Real.pi_gt_three])

end Stability

/-! #### The constants and the targets 4, 5 (continued) -/

/-- `c₁ = min (δ/(4(1+A))) (1/8)`. -/
private def FreeConvRegular_c₁ (δ A : ℝ) : ℝ := min (δ / (4 * (1 + A))) (1 / 8)

/-- `c₀ = min (c/64) (c/(16 K Lp)) (c₁/(8(K+1)))`. -/
private def FreeConvRegular_c₀ (c K Lp δ A : ℝ) : ℝ :=
  min (min (c / 64) (c / (16 * K * Lp))) (FreeConvRegular_c₁ δ A / (8 * (K + 1)))

/-- `C₀ = 2 + 8 Lp K + K + Lp (A + 1/4)`. -/
private def FreeConvRegular_C₀ (K Lp A : ℝ) : ℝ := 2 + 8 * Lp * K + K + Lp * (A + 1 / 4)

private lemma FreeConvRegular_consts {c K Lp δ A : ℝ} (hc : 0 < c) (hK : 0 < K) (hLp : 0 < Lp)
    (hδ : 0 < δ) (hA : 0 ≤ A) :
    0 < FreeConvRegular_c₀ c K Lp δ A ∧
      FreeConvRegular_c₀ c K Lp δ A ≤ FreeConvRegular_c₁ δ A ∧
      FreeConvRegular_c₁ δ A ≤ δ / (4 * (1 + A)) ∧ 0 < FreeConvRegular_C₀ K Lp A := by
  have hc₁0 : 0 < FreeConvRegular_c₁ δ A := lt_min (by positivity) (by norm_num)
  have hc₀0 : 0 < FreeConvRegular_c₀ c K Lp δ A :=
    lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  refine ⟨hc₀0, ?_, min_le_left _ _, by unfold FreeConvRegular_C₀; positivity⟩
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The stability estimate with the explicit constants `c₀, c₁, C₀`. -/
private lemma FreeConvRegular_main {c K Lp δ A : ℝ} (hc : 0 < c) (hK : 0 < K) (hLp : 0 < Lp)
    (hδ : 0 < δ) (hA : 0 ≤ A) (mref : ℂ → ℂ) (E₀ : ℝ) (hE₀ : |E₀| ≤ A)
    (hbox : ∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (mref z).im ∧ ‖mref z‖ ≤ K)
    (hlip : ∀ z z' : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 →
      |z'.re - E₀| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mref z - mref z'‖ ≤ Lp * ‖z - z'‖)
    {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) (s t ε : ℝ) (ht : 0 < t)
    (htc : t ≤ FreeConvRegular_c₀ c K Lp δ A) (hs : s = 1 - t) (hε0 : 0 ≤ ε)
    (hεc : ε ≤ FreeConvRegular_c₀ c K Lp δ A)
    (hyp : ∀ w : ℂ, |w.re| ≤ FreeConvRegular_c₁ δ A →
      FreeConvRegular_c₀ c K Lp δ A * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * mref ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) :
    ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
      Tendsto (fun η : ℝ => (mref ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
      |ρ - ρ₀| ≤ FreeConvRegular_C₀ K Lp A * (ε + t) ∧
      ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4), ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖ ≤
        FreeConvRegular_C₀ K Lp A * (ε + t) := by
  obtain ⟨hc₀0, hc₀c₁, hc₁δ', -⟩ := FreeConvRegular_consts hc hK hLp hδ hA
  set c₁ := FreeConvRegular_c₁ δ A with hc₁def
  set c₀ := FreeConvRegular_c₀ c K Lp δ A with hc₀def
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le hc₀0 hc₀c₁
  have hc₁8 : c₁ ≤ 1 / 8 := min_le_right _ _
  have hc₁δ : c₁ * (1 + A) ≤ δ / 4 := by
    rw [le_div_iff₀ (by positivity)] at hc₁δ'
    linarith
  have hc₀a : c₀ ≤ c / 64 := (min_le_left _ _).trans (min_le_left _ _)
  have hc₀b : c₀ ≤ c / (16 * K * Lp) := (min_le_left _ _).trans (min_le_right _ _)
  have hc₀d : c₀ ≤ c₁ / (8 * (K + 1)) := min_le_right _ _
  have hcK : c ≤ K := by
    have h1 : |(⟨E₀, 1⟩ : ℂ).re - E₀| ≤ δ := by
      change |E₀ - E₀| ≤ δ
      rw [sub_self, abs_zero]; exact hδ.le
    obtain ⟨h2, h3⟩ := hbox ⟨E₀, 1⟩ h1 (by change (0 : ℝ) < 1; norm_num)
      (by change (1 : ℝ) ≤ 1; exact le_rfl)
    exact h2.trans ((Complex.im_le_norm _).trans h3)
  have htK : t * K * Lp ≤ c / 16 := by
    have h : t ≤ c / (16 * K * Lp) := htc.trans hc₀b
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have ht1 : t * (K + 1) ≤ c₁ / 8 := by
    have h : t ≤ c₁ / (8 * (K + 1)) := htc.trans hc₀d
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have ht12 : t ≤ 1 / 2 := by nlinarith
  obtain ⟨hsq, hσ1, hσ2⟩ := FreeConvRegular_sigma ht ht12 hs
  have P : FreeConvRegular_Par c K Lp δ A c₀ c₁ (Real.sqrt s)⁻¹ t ε E₀ mref :=
    ⟨hc, hcK, hLp, hδ, hA, hc₀0, hc₀a.trans (by linarith), hc₁0, hc₁8, hc₁δ, ht,
      htc.trans hc₀a, htK, ht1, hσ1, hσ2, hε0, hεc.trans hc₀a, hE₀, hbox, hlip⟩
  have hyp' : ∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖mV v w - FreeConvRegular_ref mref (Real.sqrt s)⁻¹ E₀ w‖ ≤ ε := by
    intro w h1 h2 h3
    have e : (((Real.sqrt s)⁻¹ : ℝ) : ℂ) = (Real.sqrt s : ℂ)⁻¹ := Complex.ofReal_inv _
    unfold FreeConvRegular_ref
    rw [e]
    exact hyp w h1 h2 h3
  exact FreeConvRegular_core P v hyp'

/-- **Target 4 (`freeConv_stable_lip`)**: stability of the free convolution `v ⊞ sc_t` against an
abstract reference `mref` that is bounded below in `Im`, bounded and Lipschitz (as a complex
function) on the box `|Re z - E₀| ≤ δ`, `0 < Im z ≤ 1`.  The reference enters through the rescaled
closeness hypothesis of `FreeConvStability.freeConv_stable_local` (`msc` replaced by `mref`); the
price is the term `t`.  Constants: `c₁ = min (δ/(4(1+A))) (1/8)`,
`c₀ = min (c/64) (c/(16 K Lp)) (c₁/(8(K+1)))`, `C₀ = 2 + 8 Lp K + K + Lp (A + 1/4)`. -/
theorem freeConv_stable_lip :
    ∀ c K Lp δ A : ℝ, 0 < c → 0 < K → 0 < Lp → 0 < δ → 0 ≤ A →
      ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ δ / (4 * (1 + A)) ∧ 0 < C₀ ∧
        ∀ (mref : ℂ → ℂ) (E₀ : ℝ), |E₀| ≤ A →
          (∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (mref z).im ∧ ‖mref z‖ ≤ K) →
          (∀ z z' : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 →
            |z'.re - E₀| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mref z - mref z'‖ ≤ Lp * ‖z - z'‖) →
          ∀ {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ →
            s = 1 - t → 0 ≤ ε → ε ≤ c₀ →
            (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
              ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * mref ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) →
            ∃ ρ ρ₀ : ℝ,
              Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
              Tendsto (fun η : ℝ => (mref ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
              |ρ - ρ₀| ≤ C₀ * (ε + t) ∧
              ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
                ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖ ≤ C₀ * (ε + t) := by
  intro c K Lp δ A hc hK hLp hδ hA
  obtain ⟨h0, h1, h2, h3⟩ := FreeConvRegular_consts hc hK hLp hδ hA
  refine ⟨FreeConvRegular_c₀ c K Lp δ A, FreeConvRegular_c₁ δ A, FreeConvRegular_C₀ K Lp A,
    h0, h1, h2, h3, ?_⟩
  intro mref E₀ hE₀ hbox hlip n _ _ v s t ε ht htc hs hε0 hεc hyp
  exact FreeConvRegular_main hc hK hLp hδ hA mref E₀ hE₀ hbox hlip v s t ε ht htc hs hε0 hεc hyp

/-- **Target 5 (`freeConv_stable_freeConvST`)**: target 4 at the reference `mref = m_{u ⊞ sc_1}`
(the block Anderson `m(z, g)` is of this form, T2189 `BAm_eq_freeConvST`; the semicircle is
`u ≡ 0`): only the lower bound of `Im` on the box is assumed; the constants do not depend on `u`,
`ι` or `card ι` (`K = 1` by target 2, `Lp = 1/(2c²)` by target 1). -/
theorem freeConv_stable_freeConvST :
    ∀ c δ A : ℝ, 0 < c → 0 < δ → 0 ≤ A →
      ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ δ / (4 * (1 + A)) ∧ 0 < C₀ ∧
        ∀ {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ) (E₀ : ℝ), |E₀| ≤ A →
          (∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (freeConvST u 1 z).im) →
          ∀ {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ →
            s = 1 - t → 0 ≤ ε → ε ≤ c₀ →
            (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
              ‖mV v w - (Real.sqrt s : ℂ)⁻¹ *
                freeConvST u 1 ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) →
            ∃ ρ ρ₀ : ℝ,
              Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
              Tendsto (fun η : ℝ => (freeConvST u 1 ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
              |ρ - ρ₀| ≤ C₀ * (ε + t) ∧
              ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
                ‖freeConvST v t ⟨0, η⟩ - freeConvST u 1 ⟨E₀, η⟩‖ ≤ C₀ * (ε + t) := by
  intro c δ A hc hδ hA
  have hLp : 0 < 1 / (2 * c ^ 2) := by positivity
  obtain ⟨h0, h1, h2, h3⟩ := FreeConvRegular_consts hc one_pos hLp hδ hA
  refine ⟨FreeConvRegular_c₀ c 1 (1 / (2 * c ^ 2)) δ A, FreeConvRegular_c₁ δ A,
    FreeConvRegular_C₀ 1 (1 / (2 * c ^ 2)) A, h0, h1, h2, h3, ?_⟩
  intro ι _ _ u E₀ hE₀ hlow n _ _ v s t ε ht htc hs hε0 hεc hyp
  refine FreeConvRegular_main hc one_pos hLp hδ hA (freeConvST u 1) E₀ hE₀ ?_ ?_ v s t ε ht htc
    hs hε0 hεc hyp
  · intro z hz1 hz2 hz3
    exact ⟨hlow z hz1 hz2 hz3, FreeConvRegular_norm_le_one u hz2⟩
  · intro z z' hz1 hz2 hz3 hz1' hz2' hz3'
    exact FreeConvRegular_lip_one u hc hz2 hz2' (hlow z hz1 hz2 hz3) (hlow z' hz1' hz2' hz3')

/-! ### 6. Compiled nonempty instances (CLAUDE.md §4 step 2)

Namespace `RBM.Univ.FreeConvRegularInst`.  Targets 1, 2 and 6 are applied at concrete data with
every hypothesis discharged.  Target 3 is applied at the constant sequence `u n = uI` (`Fin 2`),
`E = 0`, `δ = 1/2`, `c = 1/20`, with the lower bound `c ≤ Im m_{uI ⊞ sc_1}` derived from target 1
against the zero vector (`m_{0 ⊞ sc_1} = msc`, the bridge below) and `un_msc_im_ge`.  Targets 4
and 5 are applied at `mref = msc`, `E₀ = 0`, `A = 0`, `δ = 1/2`, `c = 9/100`, `K = 1`, `Lp = 62`
(`stable_lip_msc`) and at `u = uI`, `E₀ = 0`, `A = 0`, `δ = 1/2`, `c = 1/20`
(`stable_freeConvST_uI`): the constants are those the theorem produces, `t = c₀`, `ε = c₀/2`,
`s = 1 - c₀`; the index type `n` and `v : n → ℝ` stay arbitrary, and the `Fin 3` corollaries are the
data of the ticket.  The closeness hypothesis on the strip is another gate's input (supplied
downstream by the local law; the T2190 preflight (ii-b) found it satisfied by `N`-point quantile
data only for `N ≳ 5·10^5` already at a larger `c₀`, so a Lean witness is not feasible, DECISIONS
§56) and stays a hypothesis of the instances; because `n` and `v` are arbitrary it is not tied to
one small `n`; every other hypothesis is discharged. -/

namespace FreeConvRegularInst

/-- **Bridge**: the free convolution of `δ₀` with `sc_1` is the semicircle,
`freeConvST (fun _ => 0) 1 z = msc z` for `0 < Im z`, on every finite nonempty index type. -/
theorem freeConvST_zero_eq_msc {ι : Type*} [Fintype ι] [Nonempty ι] {z : ℂ} (hz : 0 < z.im) :
    freeConvST (fun _ : ι => (0 : ℝ)) 1 z = msc z := by
  have hm := msc_im_pos hz
  have hmsc := msc_add_eq_neg_inv hz
  have h1 : -z - msc z = (msc z)⁻¹ := by linear_combination -hmsc
  have h2 : (-z - msc z)⁻¹ = msc z := by rw [h1, inv_inv]
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have heq : msc z = ((Fintype.card ι : ℕ) : ℂ)⁻¹ *
      ∑ i : ι, (((fun _ : ι => (0 : ℝ)) i : ℂ) - z - ((1 : ℝ) : ℂ) * msc z)⁻¹ := by
    simp only [Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_sub, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [inv_mul_cancel_left₀ hc]
    exact h2.symm
  exact (freeConv_existsUnique (fun _ : ι => (0 : ℝ)) zero_le_one hz).unique
    (isFreeConv51_freeConvST (fun _ : ι => (0 : ℝ)) zero_le_one z hz) ⟨hm, heq⟩

/-- The bridge at `Fin 1` and `Fin 2`. -/
example : (∀ z : ℂ, 0 < z.im → freeConvST (fun _ : Fin 1 => (0 : ℝ)) 1 z = msc z) ∧
    (∀ z : ℂ, 0 < z.im → freeConvST (fun _ : Fin 2 => (0 : ℝ)) 1 z = msc z) :=
  ⟨fun _ hz => freeConvST_zero_eq_msc hz, fun _ hz => freeConvST_zero_eq_msc hz⟩

/-- Target 1 at `Fin 2`, `u = (-1, 1)`, `u' = (-1, 1/2)`, `r = 1/2`, `s = 1`, `z = i`, `z' = 1 + i`. -/
example :
    (1 : ℝ) ^ 2 * ((freeConvST (![-1, 1] : Fin 2 → ℝ) 1 Complex.I).im +
        (freeConvST (![-1, 1 / 2] : Fin 2 → ℝ) 1 (1 + Complex.I)).im) ^ 2 *
      ‖freeConvST (![-1, 1] : Fin 2 → ℝ) 1 Complex.I -
        freeConvST (![-1, 1 / 2] : Fin 2 → ℝ) 1 (1 + Complex.I)‖ ≤
    2 * ((1 / 2 : ℝ) + ‖(Complex.I : ℂ) - (1 + Complex.I)‖) :=
  freeConvST_sub_le (![-1, 1] : Fin 2 → ℝ) (![-1, 1 / 2] : Fin 2 → ℝ) (1 / 2) 1 one_pos
    (by intro i; fin_cases i <;> norm_num) Complex.I (1 + Complex.I) (by simp) (by simp)

/-- Target 2 at `Fin 3`, `u = (-1, 0, 1)`, `s = 1/2`, `z = i/10`. -/
example : (1 / 2 : ℝ) * ‖freeConvST (![-1, 0, 1] : Fin 3 → ℝ) (1 / 2) (Complex.I / 10)‖ ^ 2 ≤ 1 :=
  freeConvST_norm_sq_le (![-1, 0, 1] : Fin 3 → ℝ) (1 / 2) (by norm_num) (Complex.I / 10)
    (by simp)

/-- The data `uI = (-10⁻⁴, 10⁻⁴)` on `Fin 2`. -/
def uI : Fin 2 → ℝ := ![-1 / 10000, 1 / 10000]

/-- `Im m_{uI ⊞ sc_1} ≥ 1/20` on `|Re z| ≤ 1/2`, `0 < Im z ≤ 10`: target 1 against the zero
vector, `m_{0 ⊞ sc_1} = msc`, `Im msc ≥ 9/100` (`un_msc_im_ge`):
`9/100 - 2·10⁻⁴/(9/100)² ≥ 1/20`. -/
theorem uI_lower {z : ℂ} (hre : |z.re| ≤ 1 / 2) (hz : 0 < z.im) (hz10 : z.im ≤ 10) :
    1 / 20 ≤ (freeConvST uI 1 z).im := by
  obtain ⟨hm, -⟩ := isFreeConv51_freeConvST uI zero_le_one z hz
  have h1 := freeConvST_sub_le uI (fun _ : Fin 2 => (0 : ℝ)) (1 / 10000) 1 one_pos
    (by intro i; fin_cases i <;> norm_num [uI]) z z hz hz
  rw [freeConvST_zero_eq_msc hz, sub_self, norm_zero, add_zero] at h1
  have hb := un_msc_im_ge hz hz10 hre
  set a := (freeConvST uI 1 z).im with ha
  set b := (msc z).im with hb'
  set d := ‖freeConvST uI 1 z - msc z‖ with hd
  have hd1 : b - a ≤ d := by
    have : |a - b| ≤ d := by
      rw [ha, hb', hd, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have := neg_abs_le (a - b)
    linarith
  by_contra hcon
  push Not at hcon
  have hd2 : 4 / 100 ≤ d := by linarith
  have hab : 9 / 100 ≤ a + b := by linarith
  have h2 : (9 / 100 : ℝ) ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have h3 : (9 / 100 : ℝ) ^ 2 * (4 / 100) ≤ (a + b) ^ 2 * d :=
    mul_le_mul h2 hd2 (by norm_num) (by positivity)
  norm_num at h1 h3
  linarith

/-- Target 3 at the constant sequence `u n = uI`, `E = 0`, `δ = 1/2`, `c = 1/20`: all hypotheses
discharged. -/
example : ∃ ρ : ℕ → ℝ, UNDens (fun _ : ℕ => freeConvST uI 1) 0 ρ (1 / 2) ∧
    ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 →
      |(freeConvST uI 1 ⟨0, η⟩).im / Real.pi - ρ n| ≤ η / (1 / 20 : ℝ) ^ 2 :=
  unDens_freeConvST (ι := fun _ : ℕ => Fin 2) (fun _ => uI) 0 (1 / 2) (1 / 20) (by norm_num)
    (by norm_num)
    (Eventually.of_forall fun _ x η hx hη hη10 => uI_lower (z := ⟨x, η⟩)
      (by simpa using hx) hη hη10)

/-- **Target 4, instance** at `mref = msc`, `E₀ = 0`, `A = 0`, `δ = 1/2`, `c = 9/100`, `K = 1`
(`norm_msc_lt_one`), `Lp = 62` (target 1 through the bridge: `1/(2c²) = 61.73 ≤ 62`); the
constants are those of the theorem, `t = c₀`, `ε = c₀/2`, `s = 1 - c₀`.  The index type `n` and
`v : n → ℝ` stay arbitrary; the closeness hypothesis, the one input of another gate (it needs a
large `n`, see the header of this section), stays a hypothesis, every other hypothesis is
discharged. -/
theorem stable_lip_msc : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧
    0 < C₀ ∧ ∀ {n : Type} [Fintype n] [Nonempty n] (v : n → ℝ),
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * c₀ / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt (1 - c₀) : ℂ)⁻¹ *
          msc ((Real.sqrt (1 - c₀) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ c₀ / 2) →
      ∃ ρ ρ₀ : ℝ,
        Tendsto (fun η : ℝ => (freeConvST v c₀ ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (msc ⟨((0 : ℝ)), η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
        |ρ - ρ₀| ≤ C₀ * (c₀ / 2 + c₀) ∧
        ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
          ‖freeConvST v c₀ ⟨0, η⟩ - msc ⟨(0 : ℝ), η⟩‖ ≤ C₀ * (c₀ / 2 + c₀) := by
  obtain ⟨c₀, c₁, C₀, hc₀, hc₀c₁, hc₁, hC₀, H⟩ := freeConv_stable_lip (9 / 100) 1 62 (1 / 2) 0
    (by norm_num) one_pos (by norm_num) (by norm_num) le_rfl
  refine ⟨c₀, c₁, C₀, hc₀, hc₀c₁, hc₁, hC₀, ?_⟩
  intro n _ _ v hyp
  refine H msc 0 (by simp) ?_ ?_ v (1 - c₀) c₀ (c₀ / 2) hc₀ le_rfl rfl (by positivity)
    (by linarith) hyp
  · intro z hz1 hz2 hz3
    refine ⟨un_msc_im_ge hz2 (by linarith) (by simpa using hz1), (norm_msc_lt_one hz2).le⟩
  · intro z z' hz1 hz2 hz3 hz1' hz2' hz3'
    have hlow : ∀ y : ℂ, |y.re - 0| ≤ 1 / 2 → 0 < y.im → y.im ≤ 1 → 9 / 100 ≤ (msc y).im :=
      fun y hy1 hy2 hy3 => un_msc_im_ge hy2 (by linarith) (by simpa using hy1)
    have h := FreeConvRegular_lip_one (fun _ : Fin 1 => (0 : ℝ)) (c := 9 / 100) (by norm_num)
      hz2 hz2' (by rw [freeConvST_zero_eq_msc hz2]; exact hlow z hz1 hz2 hz3)
      (by rw [freeConvST_zero_eq_msc hz2']; exact hlow z' hz1' hz2' hz3')
    rw [freeConvST_zero_eq_msc hz2, freeConvST_zero_eq_msc hz2'] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)

/-- The same instance at `n = Fin 3`, `v : Fin 3 → ℝ` arbitrary (the data of the ticket). -/
example : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧ 0 < C₀ ∧
    ∀ v : Fin 3 → ℝ,
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * c₀ / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt (1 - c₀) : ℂ)⁻¹ *
          msc ((Real.sqrt (1 - c₀) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ c₀ / 2) →
      ∃ ρ ρ₀ : ℝ,
        Tendsto (fun η : ℝ => (freeConvST v c₀ ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (msc ⟨((0 : ℝ)), η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
        |ρ - ρ₀| ≤ C₀ * (c₀ / 2 + c₀) ∧
        ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
          ‖freeConvST v c₀ ⟨0, η⟩ - msc ⟨(0 : ℝ), η⟩‖ ≤ C₀ * (c₀ / 2 + c₀) := by
  obtain ⟨c₀, c₁, C₀, h0, h1, h2, h3, H⟩ := stable_lip_msc
  exact ⟨c₀, c₁, C₀, h0, h1, h2, h3, fun v hv => H v hv⟩

/-- **Target 5, instance** at `u = uI`, `E₀ = 0`, `A = 0`, `δ = 1/2`, `c = 1/20`; the constants are
those of the theorem, `t = c₀`, `ε = c₀/2`, `s = 1 - c₀`; the index type `n` and `v` stay
arbitrary and the closeness hypothesis stays a hypothesis, as for `stable_lip_msc`. -/
theorem stable_freeConvST_uI : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧
    c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧ 0 < C₀ ∧
    ∀ {n : Type} [Fintype n] [Nonempty n] (v : n → ℝ),
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * c₀ / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt (1 - c₀) : ℂ)⁻¹ *
          freeConvST uI 1 ((Real.sqrt (1 - c₀) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ c₀ / 2) →
      ∃ ρ ρ₀ : ℝ,
        Tendsto (fun η : ℝ => (freeConvST v c₀ ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (freeConvST uI 1 ⟨(0 : ℝ), η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
        |ρ - ρ₀| ≤ C₀ * (c₀ / 2 + c₀) ∧
        ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
          ‖freeConvST v c₀ ⟨0, η⟩ - freeConvST uI 1 ⟨(0 : ℝ), η⟩‖ ≤ C₀ * (c₀ / 2 + c₀) := by
  obtain ⟨c₀, c₁, C₀, hc₀, hc₀c₁, hc₁, hC₀, H⟩ := freeConv_stable_freeConvST (1 / 20) (1 / 2) 0
    (by norm_num) (by norm_num) le_rfl
  refine ⟨c₀, c₁, C₀, hc₀, hc₀c₁, hc₁, hC₀, ?_⟩
  intro n _ _ v hyp
  exact H uI 0 (by simp) (fun z hz1 hz2 hz3 => uI_lower (by simpa using hz1) hz2 (by linarith)) v
    (1 - c₀) c₀ (c₀ / 2) hc₀ le_rfl rfl (by positivity) (by linarith) hyp

/-- The same instance at `n = Fin 3`, `v : Fin 3 → ℝ` arbitrary (the data of the ticket). -/
example : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧ 0 < C₀ ∧
    ∀ v : Fin 3 → ℝ,
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * c₀ / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt (1 - c₀) : ℂ)⁻¹ *
          freeConvST uI 1 ((Real.sqrt (1 - c₀) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ c₀ / 2) →
      ∃ ρ ρ₀ : ℝ,
        Tendsto (fun η : ℝ => (freeConvST v c₀ ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (freeConvST uI 1 ⟨(0 : ℝ), η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
        |ρ - ρ₀| ≤ C₀ * (c₀ / 2 + c₀) ∧
        ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
          ‖freeConvST v c₀ ⟨0, η⟩ - freeConvST uI 1 ⟨(0 : ℝ), η⟩‖ ≤ C₀ * (c₀ / 2 + c₀) := by
  obtain ⟨c₀, c₁, C₀, h0, h1, h2, h3, H⟩ := stable_freeConvST_uI
  exact ⟨c₀, c₁, C₀, h0, h1, h2, h3, fun v hv => H v hv⟩

/-- Target 6 at `h n = 1/(n+1)`, together with `un_dens_msc_zero`: two `UNDens` data
(`m n = msc + 1_{Im z < h n} i/2` and `m n = msc`) that agree on `Im z ≥ 1/(n+1)` and have
different limits, `ρ 0 ≠ rhoSC 0`. -/
example : ∃ (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ), UNDens m 0 ρ (1 / 2) ∧
    UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) ∧
    (∀ (n : ℕ) (z : ℂ), 1 / ((n : ℝ) + 1) ≤ z.im → m n z = msc z) ∧ ρ 0 ≠ rhoSC 0 := by
  obtain ⟨m, ρ, h1, h2, h3⟩ := unDens_not_eta_determined (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun n => by positivity)
  refine ⟨m, ρ, h1, un_dens_msc_zero, h2, ?_⟩
  rw [h3 0]
  have : 0 < 1 / (2 * Real.pi) := by positivity
  intro h
  linarith

end FreeConvRegularInst

end RBM.Univ
