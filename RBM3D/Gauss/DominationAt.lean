/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.StochDomAt
import RBM3D.Gauss.Domination
import RBM3D.Gauss.SteinMatrix
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ProductMeasure

/-!
# Moments and `≺` at the scale `N = (W L)^d`; countable-product Stein

Everything here is stated for a size sequence `size : ℕ → ℕ` (for `sz : Sizes d`:
`sz.size n = (W n L n)^d`) and the `≺` of `RBM3D/Defs/StochDomAt.lean`; `HighProbAt`,
`StochDomAt` are defined there.  The index-scale versions are in `RBM3D/Gauss/Domination.lean`
and `RBM3D/Gauss/SteinMatrix.lean`.

## Contents

* `MomentDomAt`, the moment hypothesis along an admissible sequence with physical matrix
  dimension `size l`; `stochDomAt_of_momentDomAt` (moments `⇒ ≺`); `highProbAt_univ`.
* The reverse bridge (`≺ ⇒ moments`, with a whole-space envelope):
  `integrable_abs_evenPow_of_envelope`, `momentDomAt_of_stochDomAt`, and
  `momentDomAt_of_stochDomAt_of_nonneg` for a non-negative family.
* The independent centred Gaussian measure on a countable product (namespace
  `RBM.Gauss.GaussianProduct`): `Sample`, `law`, `law_pi`, `map_update` (resampling one
  coordinate leaves the law invariant) and `stein` (Stein's identity in one coordinate).
-/

noncomputable section


namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Moments imply `≺` at the scale `size` -/

section Markov

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- The moment hypothesis along an admissible sequence with physical matrix dimension
`size l`. The size, not the sequence index `l`, appears in every power. -/
def MomentDomAt (P : Measure Ω) (size : ℕ → ℕ) {U : ℕ → Type*}
    (Y : ∀ l, U l → Ω → ℝ) (Φ : ∀ l, U l → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u,
    ∫ ω, |Y l u ω| ^ (2 * p) ∂P ≤
      C * ((size l : ℝ) ^ (ε * p) * Φ l u ^ (2 * p))

/-- Moments imply stochastic domination along admissible dimensions. Both the parameter
cardinality and the threshold are measured against `size l`; the measure `P` is common to the
whole sequence. -/
theorem stochDomAt_of_momentDomAt {U : ℕ → Type*} [∀ l, Fintype (U l)]
    (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop)
    {Ccard : ℝ}
    (hcard : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ Ccard)
    {Y : ∀ l, U l → Ω → ℝ} {Φ : ∀ l, U l → ℝ}
    (hΦ : ∀ l u, 0 < Φ l u)
    (hint : ∀ (p l : ℕ) (u : U l), Integrable (fun ω => |Y l u ω| ^ (2 * p)) P)
    (hmom : MomentDomAt P size Y Φ) :
    StochDomAt P size Y (fun l u _ => Φ l u) := by
  intro τ hτ D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + Ccard + 1) / τ)
  have hDp : D + Ccard + 1 ≤ τ * (p : ℝ) := by
    rw [div_le_iff₀ hτ] at hp
    linarith
  obtain ⟨C, hC0, hCN⟩ := hmom τ hτ p
  have hexp : 0 < τ * (p : ℝ) - (D + Ccard) := by linarith
  filter_upwards [hcard, hCN, hsize.eventually (eventually_ge_atTop 1),
    hsize.eventually (eventually_le_rpow C hexp)] with l hcardl hNl hsize1 hCle
  have hNpos : (0 : ℝ) < size l := by exact_mod_cast hsize1
  have hNge1 : (1 : ℝ) ≤ size l := by exact_mod_cast hsize1
  have hsingle (u : U l) :
      P {ω | (size l : ℝ) ^ τ * Φ l u < Y l u ω} ≤
        ENNReal.ofReal ((size l : ℝ) ^ (-(D + Ccard))) := by
    have hΦu := hΦ l u
    have ht : 0 < (size l : ℝ) ^ τ * Φ l u :=
      mul_pos (Real.rpow_pos_of_pos hNpos τ) hΦu
    refine (meas_gt_le_of_moment P ht (hint p l u) (hNl u)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    set a : ℝ := (size l : ℝ) ^ (τ * (p : ℝ)) with ha_def
    have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
    have hb : (0 : ℝ) < Φ l u ^ (2 * p) := by positivity
    have h1 : ((size l : ℝ) ^ τ * Φ l u) ^ (2 * p) =
        a * a * Φ l u ^ (2 * p) := by
      rw [mul_pow, ha_def, ← Real.rpow_natCast ((size l : ℝ) ^ τ) (2 * p),
        ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      push_cast
      ring_nf
    have h2 : C * (a * Φ l u ^ (2 * p)) /
        (a * a * Φ l u ^ (2 * p)) = C * a⁻¹ := by
      field_simp
    have h3 : a⁻¹ = (size l : ℝ) ^ (-(τ * (p : ℝ))) := by
      rw [ha_def, Real.rpow_neg hNpos.le]
    rw [h1, h2]
    calc C * a⁻¹ ≤ (size l : ℝ) ^ (τ * (p : ℝ) - (D + Ccard)) * a⁻¹ :=
          mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 ha.le)
      _ = (size l : ℝ) ^ (-(D + Ccard)) := by
          rw [h3, ← Real.rpow_add hNpos]
          congr 1
          ring
  have hp' : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + Ccard)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hset : badSetAt size Y (fun l u _ => Φ l u) τ l =
      ⋃ u, {ω | (size l : ℝ) ^ τ * Φ l u < Y l u ω} := by
    ext ω
    simp [badSetAt]
  calc P (badSetAt size Y (fun l u _ => Φ l u) τ l)
      ≤ ∑ u : U l, P {ω | (size l : ℝ) ^ τ * Φ l u < Y l u ω} := by
        rw [hset]
        exact measure_iUnion_fintype_le P _
    _ ≤ ∑ _u : U l, ENNReal.ofReal ((size l : ℝ) ^ (-(D + Ccard))) :=
        Finset.sum_le_sum fun u _ => hsingle u
    _ = ENNReal.ofReal (Fintype.card (U l) *
          (size l : ℝ) ^ (-(D + Ccard))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ Ccard *
          (size l : ℝ) ^ (-(D + Ccard))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcardl hp')
    _ = ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring_nf

end Markov

/-! ### Good events at the scale `size`

The time-net lemmas `netSize`, `netPt`, `card_net_le` of `RBM3D/Gauss/Domination.lean` (index
`N : ℕ`) are used with `N := size l`. -/

section Uniform

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- The whole sample space is a valid good event at every physical dimension. -/
theorem highProbAt_univ (P : Measure Ω) (size : ℕ → ℕ) :
    HighProbAt P size (fun _ => Set.univ) := by
  intro D _
  exact Eventually.of_forall fun _ => by simp

end Uniform

/-! ### The reverse bridge at the scale `size` -/

section Reverse

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- A whole-space pointwise envelope makes every even power integrable. -/
theorem integrable_abs_evenPow_of_envelope {Y : Ω → ℝ} {M : ℝ}
    (hmeas : Measurable Y) (hbound : ∀ ω, |Y ω| ≤ M) (p : ℕ) :
    Integrable (fun ω => |Y ω| ^ (2 * p)) P := by
  have hm : Measurable (fun ω => |Y ω| ^ (2 * p)) := by
    have hma : Measurable fun ω => |Y ω| := by
      simpa [Real.norm_eq_abs] using hmeas.norm
    exact hma.pow_const _
  refine Integrable.mono' (integrable_const (M ^ (2 * p)))
    hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (Y ω)) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hbound ω) _

/-- Reverse bridge along admissible physical dimensions and a common probability measure. -/
theorem momentDomAt_of_stochDomAt (size : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop) {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ}
    {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (size N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), |Y N u ω| ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (size N : ℝ) ^ Kenv)
    (hdom : StochDomAt P size (fun N u ω => |Y N u ω|) (fun N u _ => Φ N u)) :
    MomentDomAt P size Y Φ := by
  intro ε hε p
  have hPuniv : (0 : ℝ) ≤ P.real Set.univ := measureReal_nonneg
  refine ⟨P.real Set.univ + 1, by linarith, ?_⟩
  set τ : ℝ := ε / 2 with hτ_def
  have hτ : 0 < τ := half_pos hε
  set D' : ℝ := 2 * p * (Kenv + B) + 1 with hD'_def
  have hD'0 : 0 < D' := by
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hKB : (0 : ℝ) ≤ 2 * (p : ℝ) * (Kenv + B) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hD'_def]; linarith
  filter_upwards [hΦlow, hEnvpoly, hdom τ hτ D' hD'0, hsize.eventually (eventually_ge_atTop 1)] with
    N hΦN hEN hbad hN1
  intro u
  have hNpos : (0 : ℝ) < size N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hN1
  -- the threshold and the exceptional set for this single `u`
  set c : ℝ := (size N : ℝ) ^ τ * Φ N u with hc_def
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos hNpos τ) (hΦ N u)
  set S : Set Ω := {ω | c < |Y N u ω|} with hS_def
  have habs : Measurable fun ω => |Y N u ω| := by
    simpa [Real.norm_eq_abs] using (hmeas N u).norm
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const habs
  have hSsub : S ⊆ badSetAt size (fun N u ω => |Y N u ω|)
      (fun N u _ => Φ N u) τ N := fun ω hω => ⟨u, hω⟩
  have hPS : P.real S ≤ (size N : ℝ) ^ (-D') := by
    rw [measureReal_def]
    calc (P S).toReal ≤ (ENNReal.ofReal ((size N : ℝ) ^ (-D'))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hSsub).trans hbad)
      _ = (size N : ℝ) ^ (-D') := ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _)
  -- the pointwise split
  have hEnvpow : (0 : ℝ) ≤ Env N ^ (2 * p) := pow_nonneg (hEnv0 N) _
  have hcpow : (0 : ℝ) ≤ c ^ (2 * p) := pow_nonneg hc0.le _
  have hpt : ∀ ω, |Y N u ω| ^ (2 * p)
      ≤ c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have h1 : |Y N u ω| ^ (2 * p) ≤ Env N ^ (2 * p) :=
        pow_le_pow_left₀ (abs_nonneg _) (henv N u ω) _
      linarith
    · rw [Set.indicator_of_notMem hω]
      have h1 : |Y N u ω| ≤ c := not_lt.1 hω
      have h2 : |Y N u ω| ^ (2 * p) ≤ c ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg _) h1 _
      linarith
  have hRHSint : Integrable
      (fun ω => c ^ (2 * p) + Set.indicator S (fun _ => Env N ^ (2 * p)) ω) P :=
    (integrable_const _).add ((integrable_const _).indicator hSmeas)
  have hint : Integrable (fun ω => |Y N u ω| ^ (2 * p)) P :=
    integrable_abs_evenPow_of_envelope (hmeas N u) (henv N u) p
  have hle := integral_mono hint hRHSint hpt
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hSmeas), integral_const,
    integral_indicator_const _ hSmeas, smul_eq_mul, smul_eq_mul] at hle
  -- the main part is exactly `N^{εp} Φ^{2p}`
  have hmain : c ^ (2 * p) = (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    rw [hc_def, mul_pow, ← Real.rpow_natCast ((size N : ℝ) ^ τ) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 2
    rw [hτ_def]
    push_cast
    ring
  -- the exceptional part is negligible
  have hΦpow : (size N : ℝ) ^ (-(B * (2 * p))) ≤ Φ N u ^ (2 * p) := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _) (hΦN u) (2 * p)
    refine le_trans (le_of_eq ?_) h
    rw [← Real.rpow_natCast ((size N : ℝ) ^ (-B)) (2 * p), ← Real.rpow_mul hNpos.le]
    congr 1
    push_cast
    ring
  have htail : P.real S * Env N ^ (2 * p) ≤ (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
    have h1 : Env N ^ (2 * p) ≤ ((size N : ℝ) ^ Kenv) ^ (2 * p) :=
      pow_le_pow_left₀ (hEnv0 N) hEN _
    have h2 : ((size N : ℝ) ^ Kenv) ^ (2 * p) = (size N : ℝ) ^ (Kenv * (2 * p)) := by
      rw [← Real.rpow_natCast ((size N : ℝ) ^ Kenv) (2 * p), ← Real.rpow_mul hNpos.le]
      congr 1
      push_cast
      ring
    have hStep : P.real S * Env N ^ (2 * p) ≤
        (size N : ℝ) ^ (-D') * (size N : ℝ) ^ (Kenv * (2 * p)) := by
      refine mul_le_mul hPS (h2 ▸ h1) hEnvpow (Real.rpow_nonneg hNpos.le _)
    have hExp : (size N : ℝ) ^ (-D') * (size N : ℝ) ^ (Kenv * (2 * p))
        = (size N : ℝ) ^ (-(B * (2 * p)) + -1) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      rw [hD'_def]
      ring
    have hDrop : (size N : ℝ) ^ (-(B * (2 * p)) + -1) ≤ (size N : ℝ) ^ (-(B * (2 * p))) := by
      refine Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
    have hεp : (1 : ℝ) ≤ (size N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow hNge1 (mul_nonneg hε.le (Nat.cast_nonneg p))
    have hΦ2p : (0 : ℝ) ≤ Φ N u ^ (2 * p) := pow_nonneg (hΦ N u).le _
    calc P.real S * Env N ^ (2 * p) ≤ (size N : ℝ) ^ (-(B * (2 * p))) := by
          rw [hExp] at hStep; exact hStep.trans hDrop
      _ ≤ Φ N u ^ (2 * p) := hΦpow
      _ ≤ (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by nlinarith
  -- assemble
  have hmainpos : (0 : ℝ) ≤ (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (pow_nonneg (hΦ N u).le _)
  calc ∫ ω, |Y N u ω| ^ (2 * p) ∂P
      ≤ P.real Set.univ * c ^ (2 * p) + P.real S * Env N ^ (2 * p) := hle
    _ ≤ P.real Set.univ * ((size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))
        + (size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p) := by
          rw [hmain]; linarith
    _ = (P.real Set.univ + 1) * ((size N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p)) := by ring

/-- **The reverse bridge for a non-negative family, at the scale `size`**: the same as
`momentDomAt_of_stochDomAt`, for `0 ≤ Y`, with the envelope hypothesis `Y ≤ Env`; the proof
is the two lines from `momentDomAt_of_stochDomAt`. -/
theorem momentDomAt_of_stochDomAt_of_nonneg (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop)
    {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ} {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hY0 : ∀ N (u : U N) (ω : Ω), 0 ≤ Y N u ω)
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable (Y N u))
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (size N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), Y N u ω ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (size N : ℝ) ^ Kenv)
    (hdom : StochDomAt P size Y (fun N u _ => Φ N u)) :
    MomentDomAt P size Y Φ := by
  have habs : (fun N (u : U N) (ω : Ω) => |Y N u ω|) = Y := by
    funext N u ω; exact abs_of_nonneg (hY0 N u ω)
  refine momentDomAt_of_stochDomAt size hsize hmeas hΦ hB hΦlow hEnv0 hKenv ?_ hEnvpoly ?_
  · intro N u ω; rw [abs_of_nonneg (hY0 N u ω)]; exact henv N u ω
  · rw [habs]; exact hdom

end Reverse

end RBM.Gauss

/-! ## Countable-product resampling and Stein

The independent centred Gaussian measure on a countable product, its invariance under
resampling one coordinate, and Stein's identity in one coordinate.  The resampling map `upd` and
the one-dimensional identity `integral_mul_gaussianReal_complex'` are in
`RBM3D/Gauss/SteinMatrix.lean`. -/
namespace RBM.Gauss.GaussianProduct

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The sample space with one independent real coordinate at each index. -/
abbrev Sample (ι : Type*) := ι → ℝ

/-- Independent centred Gaussian coordinates with specified variances. -/
noncomputable def law (v : ι → ℝ≥0) : Measure (Sample ι) :=
  Measure.infinitePi fun c => gaussianReal 0 (v c)

instance (v : ι → ℝ≥0) : IsProbabilityMeasure (law v) := by
  unfold law
  infer_instance

omit [Countable ι] [DecidableEq ι] in
/-- Measurable rectangles witness the independence of the coordinate laws. -/
theorem law_pi (v : ι → ℝ≥0) {s : Finset ι} {t : ι → Set ℝ}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    law v (Set.pi (↑s) t) = ∏ i ∈ s, (gaussianReal 0 (v i)) (t i) := by
  unfold law
  exact Measure.infinitePi_pi _ ht

omit [Countable ι] in
/-- Replacing one coordinate by an independent copy of its law preserves the product law. -/
theorem map_update (v : ι → ℝ≥0) (c : ι) :
    ((law v).prod (gaussianReal 0 (v c))).map (upd c) = law v := by
  classical
  have hUm : Measurable (upd c) := measurable_upd c
  change _ = Measure.infinitePi _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hst : MeasurableSet (Set.pi (↑s) t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply hUm hst]
  by_cases hc : c ∈ s
  · have hpre : upd c ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑(s.erase c)) t) ×ˢ t c := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_erase,
        Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · intro h
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [← upd_of_ne c p hi.2]
          exact h i hi.1
        · rw [← upd_self c p]
          exact h c hc
      · rintro ⟨h1, h2⟩ i hi
        by_cases hic : i = c
        · subst hic
          rwa [upd_self]
        · rw [upd_of_ne c p hic]
          exact h1 i ⟨hi, hic⟩
    rw [hpre, Measure.prod_prod, law_pi v (fun i _ => ht i), ← Finset.prod_erase_mul s _ hc]
  · have hpre : upd c ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑s) t) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Set.mem_univ, and_true,
        Finset.mem_coe]
      constructor
      · intro h i hi
        rw [← upd_of_ne c p (fun hh => hc (hh ▸ hi))]
        exact h i hi
      · intro h i hi
        rw [upd_of_ne c p (fun hh => hc (hh ▸ hi))]
        exact h i hi
    rw [hpre, Measure.prod_prod, measure_univ, mul_one, law_pi v (fun i _ => ht i)]
/-- Coordinatewise complex Stein identity for a genuine product Gaussian measure.
The derivative is along the fibre obtained by varying only coordinate `c`. -/
theorem stein (v : ι → ℝ≥0) (c : ι) (g g' : Sample ι → ℂ)
    (hgc : Continuous g) (hg'c : Continuous g')
    (hderiv : ∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t))
      (g' ω) (ω c))
    (hgb : ∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C)
    (hg'b : ∃ C : ℝ, ∀ ω, ‖g' ω‖ ≤ C) :
    ∫ ω, ω c • g ω ∂(law v) = (v c : ℝ) • ∫ ω, g' ω ∂(law v) := by
  obtain ⟨C₀, hC₀⟩ := hgb
  obtain ⟨C₁, hC₁⟩ := hg'b
  have hC : ∀ ω, ‖g ω‖ ≤ max C₀ C₁ := fun ω => (hC₀ ω).trans (le_max_left _ _)
  have hC' : ∀ ω, ‖g' ω‖ ≤ max C₀ C₁ := fun ω => (hC₁ ω).trans (le_max_right _ _)
  have hgm : Measurable g := hgc.measurable
  have hg'm : Measurable g' := hg'c.measurable
  have hUm : Measurable (upd c) := measurable_upd c
  have hfib : ∀ (ω : Sample ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s))
        (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  have hInt : Integrable (fun p : Sample ι × ℝ => p.2 • g (upd c p))
      ((law v).prod (gaussianReal 0 (v c))) := by
    have hbase : Integrable (fun p : Sample ι × ℝ => p.2)
        ((law v).prod (gaussianReal 0 (v c))) :=
      (RBM.integrable_id_gaussianReal (var := v c)).comp_snd (law v)
    refine Integrable.mono' (hbase.abs.const_mul (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (measurable_snd.smul (hgm.comp hUm)).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg p.2)
  have hInt' : Integrable (fun p : Sample ι × ℝ => g' (upd c p))
      ((law v).prod (gaussianReal 0 (v c))) := by
    refine Integrable.mono' (integrable_const (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => hC' _)
    exact (hg'm.comp hUm).aestronglyMeasurable
  have hL : ∫ ω, ω c • g ω ∂(law v)
      = ∫ p : Sample ι × ℝ, p.2 • g (upd c p)
          ∂((law v).prod (gaussianReal 0 (v c))) := by
    conv_lhs => rw [← map_update v c]
    rw [integral_map hUm.aemeasurable (by
      rw [map_update v c]
      exact ((measurable_pi_apply c).smul hgm).aestronglyMeasurable)]
    simp only [upd_self]
  have hR : ∫ ω, g' ω ∂(law v)
      = ∫ p : Sample ι × ℝ, g' (upd c p)
          ∂((law v).prod (gaussianReal 0 (v c))) := by
    conv_lhs => rw [← map_update v c]
    rw [integral_map hUm.aemeasurable (by
      rw [map_update v c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hInt, integral_prod _ hInt', ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  change ∫ t : ℝ, t • g (Function.update ω c t) ∂(gaussianReal 0 (v c))
      = (v c : ℝ) • ∫ t : ℝ, g' (Function.update ω c t) ∂(gaussianReal 0 (v c))
  have hcont : Continuous fun t : ℝ => g' (Function.update ω c t) :=
    hg'c.comp (continuous_update_coord c ω)
  have hst := integral_mul_gaussianReal_complex' (var := v c)
    (f := fun t => g (Function.update ω c t))
    (f' := fun t => g' (Function.update ω c t))
    (C := max C₀ C₁) (hfib ω) hcont (fun t => hC _) (fun t => hC' _)
  simpa only [Complex.real_smul] using hst

end RBM.Gauss.GaussianProduct
