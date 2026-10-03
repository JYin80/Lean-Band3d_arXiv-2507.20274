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

Ticket T2012 (MD-2), second file.  Everything here is stated for a size sequence
`size : ℕ → ℕ` (for `sz : Sizes d`: `sz.size n = (W n L n)^d`) and the `≺` of
`RBM3D/Defs/StochDomAt.lean`; `HighProbAt`, `StochDomAt` are defined there (pinned), never
re-defined here.  The index-scale parts are the merged `RBM3D/Gauss/Domination.lean`,
`Envelope.lean`, `SteinMatrix.lean` and are not edited.

## Ported from `RBM2D` at `c9a24cf` (read-only; line of each declaration cited)

* from `RBM2D/Gauss/Domination.lean`: `MomentDomAt` (`:162`), `stochDomAt_of_momentDomAt` (`:171`,
  moments `⇒ ≺`), `highProbAt_univ` (`:467`), `stochDomAt_Icc_of_holder_on_good` (`:474`, the time
  net at the scale `size`), `momentDomAt_constant_one_example` (`:649`);
* from `RBM2D/Gauss/MomentBridge.lean`: `integrable_abs_evenPow_of_envelope` (`:29`),
  `momentDomAt_of_stochDomAt` (`:170`, `≺ ⇒ moments`, with the whole-space envelope);
* from `RBM2D/Gauss/SteinMatrix.lean` (namespace `RBM.Gauss.GaussianProduct`): `Sample`, `law`
  (`:29`, `:32`), `law_pi` (`:83`), `map_update` (`:91`), `stein` (`:134`) and the example
  (`:199`).  The merged `RBM.Gauss.upd`, `upd_self`, `upd_of_ne`, `measurable_upd`,
  `continuous_update_coord` and `integral_mul_gaussianReal_complex'` are RBM2D's `update`,
  `update_self`, `update_of_ne`, `measurable_update`, `continuous_update_coord`,
  `integral_mul_gaussianReal_complex_all`; they are used instead of re-declared.
* `RBM2D/Gauss/Envelope.lean` at `c9a24cf` is the deterministic resolvent envelope
  (`norm_green_le`, derivative bounds; the resolvent bound has its analogue in
  `RBM3D/Analysis/Resolvent.lean`); it has no `size`-indexed statement, so nothing is ported
  from it.
  `momentDom_green_of_stochDom` (`MomentBridge.lean:325`) needs `green`, `norm_green_le`, which this
  project does not have; it is not ported.

## New here (no RBM2D source)

`momentDomAt_of_stochDomAt_of_nonneg`, `momentDomAt_of_normStochDomAt`: the scale versions of the
merged `momentDom_of_stochDom_of_nonneg`, `momentDom_of_normStochDom`, short consequences of
`momentDomAt_of_stochDomAt`; `Sizes.seqP_eq_law`; the instances at `sz0`.
-/

noncomputable section


namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Moments imply `≺` at the scale `size` (`RBM2D/Gauss/Domination.lean:160–242`) -/

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

/-! ### The time net at the scale `size` (`RBM2D/Gauss/Domination.lean:466–596`)

The net lemmas `netSize`, `netPt`, `card_net_le`, ... are the merged `RBM3D/Gauss/Domination.lean`
(index `N : ℕ`, used here at `N := size l`). -/

section Uniform

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- The whole sample space is a valid good event at every physical dimension. -/
theorem highProbAt_univ (P : Measure Ω) (size : ℕ → ℕ) :
    HighProbAt P size (fun _ => Set.univ) := by
  intro D _
  exact Eventually.of_forall fun _ => by simp

/-- The time-net bridge along admissible matrix dimensions. On the good event the modulus
is deterministic; its complement has super-polynomially small probability in `size l`. -/
theorem stochDomAt_Icc_of_holder_on_good (size : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop) {T : ℝ} (hT : 0 < T)
    {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hγ : 0 < γ) {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (size N : ℝ) ^ (-B) ≤ Φ N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProbAt P size Ξ)
    (hHol : ∀ (N : ℕ) (ω : Ω), ω ∈ Ξ N →
      ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (size N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDomAt P size (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDomAt P size (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) := by
  set A : ℝ := (K + B + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + B + 1 := by rw [hA_def]; field_simp
  -- step 1 on the net
  have hnet : StochDomAt P size
      (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
        Y N (netPt T A (size N) k) ω)
      (fun N _ _ => Φ N) := by
    refine stochDomAt_of_momentDomAt size hsize
      (hsize.eventually (card_net_le hA)) (Φ := fun N _ => Φ N) (fun N _ => hΦ N)
      (fun p N k => hint p N _) ?_
    intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hCN] with N hN k
    exact hN ⟨netPt T A (size N) k, netPt_mem_Icc hT.le A (size N) k⟩
  -- step 2: transfer from the net to the whole interval
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hTγ : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT γ
  have hsub : ∀ᶠ N : ℕ in atTop,
      badSetAt size (U := fun _ => ↥(Set.Icc (0 : ℝ) T)) (fun N u ω => Y N (u : ℝ) ω)
        (fun N _ _ => Φ N) τ N ⊆
      badSetAt size (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
          Y N (netPt T A (size N) k) ω)
        (fun N _ _ => Φ N) (τ / 2) N ∪ (Ξ N)ᶜ := by
    filter_upwards [hΦlow, hsize.eventually (eventually_ge_atTop 1),
      hsize.eventually (eventually_le_rpow 2 hτ2),
      hsize.eventually (eventually_le_rpow (T ^ γ) one_pos)] with N hΦN hN1 hN2 hNT
    have hNpos : (0 : ℝ) < size N := by exact_mod_cast hN1
    have hNge1 : (1 : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hN1
    have hTN : T ^ γ ≤ (size N : ℝ) := by rwa [Real.rpow_one] at hNT
    have hm : (0 : ℝ) < (netSize A (size N) : ℝ) := by exact_mod_cast netSize_pos A (size N)
    have hmge : (size N : ℝ) ^ A ≤ (netSize A (size N) : ℝ) := rpow_le_netSize A (size N)
    have hNA : (0 : ℝ) < (size N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
    have hr2 : (0 : ℝ) < (size N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
    -- the net error is at most `N^{τ/2} Φ(N)`
    have herr : (size N : ℝ) ^ K * (T / (netSize A (size N) : ℝ)) ^ γ ≤
        (size N : ℝ) ^ (τ / 2) * Φ N := by
      have hstep1 : T / (netSize A (size N) : ℝ) ≤ T / (size N : ℝ) ^ A :=
        div_le_div_of_nonneg_left hT.le hNA hmge
      have hstep1' : (T / (netSize A (size N) : ℝ)) ^ γ ≤ (T / (size N : ℝ) ^ A) ^ γ :=
        Real.rpow_le_rpow (div_pos hT hm).le hstep1 hγ.le
      have hKpos : (0 : ℝ) < (size N : ℝ) ^ K := Real.rpow_pos_of_pos hNpos K
      have hstep2 : (size N : ℝ) ^ K * (T / (netSize A (size N) : ℝ)) ^ γ
          ≤ (size N : ℝ) ^ K * (T / (size N : ℝ) ^ A) ^ γ :=
        mul_le_mul_of_nonneg_left hstep1' hKpos.le
      have hpowA : ((size N : ℝ) ^ A) ^ γ = (size N : ℝ) ^ (K + B + 1) := by
        rw [← Real.rpow_mul hNpos.le, hAγ]
      have hdiv : (T / (size N : ℝ) ^ A) ^ γ = T ^ γ / (size N : ℝ) ^ (K + B + 1) := by
        rw [Real.div_rpow hT.le hNA.le, hpowA]
      have hexp : K - (K + B + 1) = -B + -1 := by ring
      have hKA : (size N : ℝ) ^ K / (size N : ℝ) ^ (K + B + 1) =
          (size N : ℝ) ^ (-B) * (size N : ℝ)⁻¹ := by
        rw [← Real.rpow_sub hNpos, ← Real.rpow_neg_one (size N : ℝ), ← Real.rpow_add hNpos, hexp]
      have hstep3 : (size N : ℝ) ^ K * (T / (size N : ℝ) ^ A) ^ γ
          = T ^ γ * ((size N : ℝ) ^ (-B) * (size N : ℝ)⁻¹) := by
        rw [hdiv, ← hKA]; ring
      have hinvn : (0 : ℝ) ≤ (size N : ℝ)⁻¹ := by positivity
      have hstep4 : T ^ γ * ((size N : ℝ) ^ (-B) * (size N : ℝ)⁻¹) ≤
          T ^ γ * (Φ N * (size N : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦN hinvn) hTγ.le
      have hstep5 : T ^ γ * (Φ N * (size N : ℝ)⁻¹) ≤ (size N : ℝ) ^ (τ / 2) * Φ N := by
        have hTinv : T ^ γ * (size N : ℝ)⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ hNpos, one_mul]; exact hTN
        have h1 : (1 : ℝ) ≤ (size N : ℝ) ^ (τ / 2) := Real.one_le_rpow hNge1 hτ2.le
        have heq : T ^ γ * (Φ N * (size N : ℝ)⁻¹) = (T ^ γ * (size N : ℝ)⁻¹) * Φ N := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (hTinv.trans h1) (hΦ N).le
      linarith
    -- and `N^τ ≥ 2 N^{τ/2}`
    have hdouble : 2 * (size N : ℝ) ^ (τ / 2) ≤ (size N : ℝ) ^ τ := by
      have heq := UnifDetDom.rpow_half_mul_rpow_half (size N) hτ
      nlinarith [hr2.le]
    rintro ω ⟨u, hu⟩
    by_cases hω : ω ∈ Ξ N
    swap
    · exact Or.inr hω
    refine Or.inl ?_
    obtain ⟨k, hk⟩ := exists_netPt_close hT A (size N) u.2
    refine ⟨k, ?_⟩
    have hhol := hHol N ω hω u.1 u.2 (netPt T A (size N) k) (netPt_mem_Icc hT.le A (size N) k)
    have hle : |Y N u.1 ω - Y N (netPt T A (size N) k) ω| ≤ (size N : ℝ) ^ (τ / 2) * Φ N := by
      refine hhol.trans (le_trans ?_ herr)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le)
        (Real.rpow_pos_of_pos hNpos K).le
    have hdiff : Y N u.1 ω - Y N (netPt T A (size N) k) ω ≤ (size N : ℝ) ^ (τ / 2) * Φ N :=
      (le_abs_self _).trans hle
    have hmul : 2 * (size N : ℝ) ^ (τ / 2) * Φ N ≤ (size N : ℝ) ^ τ * Φ N :=
      mul_le_mul_of_nonneg_right hdouble (hΦ N).le
    simp only
    linarith
  filter_upwards [hsub, hnet (τ / 2) hτ2 (D + 1) (by linarith),
    hΞ (D + 1) (by linarith), hsize.eventually (eventually_two_mul_rpow_le D)] with N h1 h2 h3 h4
  have hp : (0 : ℝ) ≤ (size N : ℝ) ^ (-(D + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg (size N)) _
  calc P (badSetAt size (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
        (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) τ N)
      ≤ P (badSetAt size (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
          Y N (netPt T A (size N) k) ω) (fun N _ _ => Φ N) (τ / 2) N ∪ (Ξ N)ᶜ) :=
        measure_mono h1
    _ ≤ P (badSetAt size (fun (N : ℕ) (k : Fin (netSize A (size N) + 1)) ω =>
          Y N (netPt T A (size N) k) ω) (fun N _ _ => Φ N) (τ / 2) N) + P (Ξ N)ᶜ :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((size N : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size N : ℝ) ^ (-(D + 1))) := add_le_add h2 h3
    _ = ENNReal.ofReal (2 * (size N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h4

end Uniform

/-- A positive nonzero instance of the admissible-size moment hypothesis.
`RBM2D/Gauss/Domination.lean:648`. -/
theorem momentDomAt_constant_one_example :
    MomentDomAt (Measure.dirac ()) (fun l => l + 1) (U := fun _ => Unit)
      (fun _ _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro ε hε p
  refine ⟨1, one_pos, ?_⟩
  exact Eventually.of_forall fun l u => by
    have hsize : (1 : ℝ) ≤ (l + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le l)
    have hp : 0 ≤ ε * (p : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
    have hpow : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) ^ (ε * p) :=
      Real.one_le_rpow hsize hp
    simpa using hpow

/-! ### The reverse bridge at the scale `size` (`RBM2D/Gauss/MomentBridge.lean`) -/

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

/-- **The reverse bridge for a non-negative family, at the scale `size`** (new: the scale version
of the merged `momentDom_of_stochDom_of_nonneg`, `RBM2D/Gauss/MomentBridge.lean:288` at the index
scale; the proof is the same two lines from `momentDomAt_of_stochDomAt`). -/
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

/-- **The reverse bridge for `NormStochDomAt`, at the scale `size`** (new: the scale version of the
merged `momentDom_of_normStochDom`, `RBM2D/Gauss/MomentBridge.lean:307` at the index scale). -/
theorem momentDomAt_of_normStochDomAt (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop)
    {U : ℕ → Type*} {V : Type*} [NormedAddCommGroup V]
    {A : ∀ N, U N → Ω → V} {Φ : ∀ N, U N → ℝ} {Env : ℕ → ℝ} {Kenv B : ℝ}
    (hmeas : ∀ (N : ℕ) (u : U N), Measurable fun ω => ‖A N u ω‖)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u, (size N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : U N) (ω : Ω), ‖A N u ω‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (size N : ℝ) ^ Kenv)
    (hdom : NormStochDomAt P size A (fun N u _ => Φ N u)) :
    MomentDomAt P size (fun N u ω => ‖A N u ω‖) Φ :=
  momentDomAt_of_stochDomAt_of_nonneg size hsize (fun _ _ _ => norm_nonneg _) hmeas hΦ hB hΦlow
    hEnv0 hKenv henv hEnvpoly hdom

end Reverse

end RBM.Gauss

/-! ## Countable-product resampling and Stein (`RBM2D/Gauss/SteinMatrix.lean`)

Ported from `RBM2D/Gauss/SteinMatrix.lean` at `c9a24cf`, namespace `RBM.Gauss.GaussianProduct`,
proofs verbatim except the renames `update → upd`, `update_self → upd_self`, `update_of_ne →
upd_of_ne`, `measurable_update → measurable_upd`, `integral_mul_gaussianReal_complex_all →
integral_mul_gaussianReal_complex'` (the merged `RBM3D/Gauss/SteinMatrix.lean` declarations).  -/
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

/-! ### A nonconstant, positive-variance instance -/

/-- A two-coordinate product with unit variance and a nonconstant bounded test function. -/
example :
    (∫ ω : Sample Bool, ω true • (↑(Real.sin (ω true)) : ℂ)
        ∂(law (fun _ : Bool => (1 : ℝ≥0))))
      = ∫ ω : Sample Bool, (↑(Real.cos (ω true)) : ℂ)
          ∂(law (fun _ : Bool => (1 : ℝ≥0))) := by
  let g : Sample Bool → ℂ := fun ω => ↑(Real.sin (ω true))
  let g' : Sample Bool → ℂ := fun ω => ↑(Real.cos (ω true))
  have hg : Continuous g :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_apply true))
  have hg' : Continuous g' :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_apply true))
  have hd : ∀ ω : Sample Bool,
      HasDerivAt (fun t : ℝ => g (Function.update ω true t)) (g' ω) (ω true) := by
    intro ω
    simpa [g, g'] using (Real.hasDerivAt_sin (ω true)).ofReal_comp
  have hb : ∃ C : ℝ, ∀ ω : Sample Bool, ‖g ω‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    simpa only [g, Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (ω true)
  have hb' : ∃ C : ℝ, ∀ ω : Sample Bool, ‖g' ω‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    simpa only [g', Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (ω true)
  simpa [g, g'] using
    (stein (fun _ : Bool => (1 : ℝ≥0)) true g g' hg hg' hd hb hb')

end RBM.Gauss.GaussianProduct

/-! ## Compiled instances at the MD-1 size sequence `sz0`

`sz0 = RBM.Gauss.SizesInst.sz0` (`d = 3`, `N_0 = 2097152`) with the model measure `seqP sz0` and the
random bounded observable `obs n = |sin (ω_{n,(0,0,true)})|` of `RBM3D/Defs/StochDomAt.lean`
(`StochDomAtInst.obs`): every hypothesis of every theorem below is discharged at this data, the
only inputs being `sz0_tendsto` (`N_n → ∞`) and the pointwise bound `0 ≤ obs ≤ 1`. -/

namespace RBM.Gauss.Sizes

open Filter MeasureTheory

/-- The model measure is the countable product law of the coordinate variances: the bridge from
`seqP sz` to `GaussianProduct.law`, so that `GaussianProduct.stein` applies to `seqP sz`. -/
theorem seqP_eq_law {d : ℕ} (sz : Sizes d) : seqP sz = GaussianProduct.law (seqGvar sz) := rfl

end RBM.Gauss.Sizes

namespace RBM.Gauss.DominationAtInst

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal
open RBM.Gauss.SizesInst RBM.Gauss.Sizes RBM.Gauss.StochDomAtInst

theorem measurable_obs (n : ℕ) : Measurable (obs n) := by
  unfold obs
  have hc : Measurable fun ω : SeqΩ sz0 =>
      ω ⟨n, ((0 : Idx 3 (sz0.L n) (sz0.W n)), (0 : Idx 3 (sz0.L n) (sz0.W n)), true)⟩ :=
    measurable_pi_apply _
  exact continuous_abs.measurable.comp (Real.continuous_sin.measurable.comp hc)

theorem integral_le_one {f : SeqΩ sz0 → ℝ} (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    ∫ ω, f ω ∂(seqP sz0) ≤ 1 := by
  calc ∫ ω, f ω ∂(seqP sz0) ≤ ∫ _ω, (1 : ℝ) ∂(seqP sz0) :=
        integral_mono_of_nonneg (ae_of_all _ h0) (integrable_const 1) (ae_of_all _ h1)
    _ = 1 := by simp

theorem integrable_pow_obs (n p : ℕ) (u : ℝ) :
    Integrable (fun ω => |u * obs n ω| ^ (2 * p)) (seqP sz0) := by
  have hm : Measurable fun ω : SeqΩ sz0 => |u * obs n ω| ^ (2 * p) :=
    (continuous_abs.measurable.comp ((measurable_obs n).const_mul u)).pow_const _
  refine Integrable.mono' (integrable_const (|u| ^ (2 * p))) hm.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h0 := obs_nonneg n ω
  have h1 := obs_le_one n ω
  have hle : |u * obs n ω| ≤ |u| := by
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right (abs_nonneg u) h1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (abs_nonneg _) hle _

theorem moment_obs_le (n p : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∫ ω, |u * obs n ω| ^ (2 * p) ∂(seqP sz0) ≤ 1 := by
  refine integral_le_one (fun ω => by positivity) fun ω => ?_
  have h0 := obs_nonneg n ω
  have h1 := obs_le_one n ω
  have hle : |u * obs n ω| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hu0 h0)]
    nlinarith
  exact pow_le_one₀ (abs_nonneg _) hle

/-- The moment hypothesis `MomentDomAt` at `sz0` for the random family `obs` against the control
`1`: `E|obs|^{2p} ≤ 1 ≤ C N^{εp}`. -/
theorem momentDomAt_obs : MomentDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n _ ω => obs n ω) (fun _ _ => (1 : ℝ)) := by
  intro ε hε p
  refine ⟨1, one_pos, Eventually.of_forall fun n _ => ?_⟩
  have h1 : (1 : ℝ) ≤ (sz0.size n : ℝ) ^ (ε * p) :=
    Real.one_le_rpow (by exact_mod_cast Sizes.one_le_size sz0 n)
      (mul_nonneg hε.le (Nat.cast_nonneg _))
  have h2 := moment_obs_le n p (u := 1) zero_le_one le_rfl
  simp only [one_mul, abs_of_nonneg (obs_nonneg n _)] at h2 ⊢
  rw [one_pow, mul_one]
  exact h2.trans h1

/-- **Instance of `stochDomAt_of_momentDomAt`** (moments `⇒ ≺`) at `sz0`, `#U = 1 ≤ N^0`. -/
theorem stochDomAt_obs_of_moment : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n _ ω => obs n ω) (fun _ _ _ => (1 : ℝ)) :=
  stochDomAt_of_momentDomAt sz0.size tendsto_sz0_size (Ccard := 0)
    (Eventually.of_forall fun n => by simp) (Φ := fun _ _ => (1 : ℝ)) (fun _ _ => one_pos)
    (fun p n _ => by simpa using integrable_pow_obs n p 1) momentDomAt_obs

/-- **Instance of `momentDomAt_of_stochDomAt`** (`≺ ⇒` moments, with the whole-space envelope
`obs ≤ 1`): the converse bridge at `sz0`, from `obs ≺ 1` proved by `prec_of_le`. -/
theorem momentDomAt_obs_of_dom : MomentDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n _ ω => obs n ω) (fun _ _ => (1 : ℝ)) :=
  momentDomAt_of_stochDomAt sz0.size tendsto_sz0_size (Env := fun _ => 1) (Kenv := 0) (B := 0)
    (fun n _ => measurable_obs n) (fun _ _ => one_pos) le_rfl
    (Eventually.of_forall fun n _ => by simp) (fun _ => zero_le_one) le_rfl
    (fun n _ ω => by simpa [abs_of_nonneg (obs_nonneg n ω)] using obs_le_one n ω)
    (Eventually.of_forall fun n => by simp)
    (Sizes.prec_of_le sz0 (fun _ _ _ => zero_le_one) fun n _ ω => by
      simpa [abs_of_nonneg (obs_nonneg n ω)] using obs_le_one n ω)

/-- **Instance of `momentDomAt_of_stochDomAt_of_nonneg`** (new at-scale variant) at `sz0`. -/
theorem momentDomAt_obs_of_nonneg : MomentDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n _ ω => obs n ω) (fun _ _ => (1 : ℝ)) :=
  momentDomAt_of_stochDomAt_of_nonneg sz0.size tendsto_sz0_size (Env := fun _ => 1) (Kenv := 0)
    (B := 0) (fun n _ ω => obs_nonneg n ω) (fun n _ => measurable_obs n) (fun _ _ => one_pos)
    le_rfl (Eventually.of_forall fun n _ => by simp) (fun _ => zero_le_one) le_rfl
    (fun n _ ω => obs_le_one n ω) (Eventually.of_forall fun n => by simp)
    (Sizes.prec_of_le sz0 (fun _ _ _ => zero_le_one) fun n _ ω => obs_le_one n ω)

/-- **Instance of `momentDomAt_of_normStochDomAt`** (new at-scale variant) at `sz0`: the norm of a
real-valued family (`E = ℝ`). -/
theorem momentDomAt_obs_of_norm : MomentDomAt (seqP sz0) sz0.size (U := fun _ => Unit)
    (fun n _ ω => ‖obs n ω‖) (fun _ _ => (1 : ℝ)) :=
  momentDomAt_of_normStochDomAt sz0.size tendsto_sz0_size (A := fun n _ ω => obs n ω)
    (Env := fun _ => 1) (Kenv := 0) (B := 0)
    (fun n _ => (measurable_obs n).norm) (fun _ _ => one_pos) le_rfl
    (Eventually.of_forall fun n _ => by simp) (fun _ => zero_le_one) le_rfl
    (fun n _ ω => by simpa [Real.norm_eq_abs, abs_of_nonneg (obs_nonneg n ω)] using obs_le_one n ω)
    (Eventually.of_forall fun n => by simp)
    (Sizes.prec_of_le sz0 (fun _ _ _ => zero_le_one) fun n _ ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (obs_nonneg n ω)] using obs_le_one n ω)

/-- The time-dependent random family `Y_n(u) = u · obs n`, Lipschitz in `u` with constant `1`. -/
def Yt (n : ℕ) (u : ℝ) (ω : SeqΩ sz0) : ℝ := u * obs n ω

/-- **Instance of `stochDomAt_Icc_of_holder_on_good`** (the time net at the scale `sz0.size`):
`Y_n(u) = u · obs n`, `u ∈ [0, 1]`, modulus `K = 0`, `γ = 1`, control `Φ = 1`, `B = 0`, good event
`Ξ = univ` (`highProbAt_univ`), moments `E|u · obs|^{2p} ≤ 1`; the conclusion is `≺` uniformly over
the whole interval `[0, 1]`. -/
theorem stochDomAt_Icc_Yt : StochDomAt (seqP sz0) sz0.size
    (U := fun _ => ↥(Set.Icc (0 : ℝ) 1)) (fun n u ω => Yt n (u : ℝ) ω) (fun _ _ _ => (1 : ℝ)) :=
  stochDomAt_Icc_of_holder_on_good sz0.size tendsto_sz0_size (T := 1) one_pos (K := 0) (B := 0)
    (γ := 1) le_rfl le_rfl one_pos (Y := Yt) (Φ := fun _ => (1 : ℝ)) (fun _ => one_pos)
    (Eventually.of_forall fun n => by simp) (Ξ := fun _ => Set.univ) (highProbAt_univ _ _)
    (fun n ω _ u hu u' hu' => by
      have h0 := obs_nonneg n ω
      have h1 := obs_le_one n ω
      simp only [Yt, Real.rpow_zero, Real.rpow_one, one_mul]
      rw [← sub_mul, abs_mul, abs_of_nonneg h0]
      exact mul_le_of_le_one_right (abs_nonneg _) h1)
    (fun p n u => integrable_pow_obs n p u)
    (fun ε hε p => by
      refine ⟨1, one_pos, Eventually.of_forall fun n u => ?_⟩
      have h1 : (1 : ℝ) ≤ (sz0.size n : ℝ) ^ (ε * p) :=
        Real.one_le_rpow (by exact_mod_cast Sizes.one_le_size sz0 n)
          (mul_nonneg hε.le (Nat.cast_nonneg _))
      have h2 := moment_obs_le n p u.2.1 u.2.2
      simp only [Yt, one_pow, mul_one, one_mul]
      exact h2.trans h1)

/-- **Instance of `integrable_abs_evenPow_of_envelope`**: the whole-space envelope `obs ≤ 1` makes
every even power of `|obs n|` integrable. -/
theorem integrable_abs_obs (n p : ℕ) : Integrable (fun ω => |obs n ω| ^ (2 * p)) (seqP sz0) :=
  integrable_abs_evenPow_of_envelope (measurable_obs n) (M := 1)
    (fun ω => by rw [abs_of_nonneg (obs_nonneg n ω)]; exact obs_le_one n ω) p

/-- **Instance of `Sizes.seqP_eq_law`**. -/
example : seqP sz0 = GaussianProduct.law (seqGvar sz0) := seqP_eq_law sz0

/-- The coordinate of size index `0` at the position `(0, 0)`, real part. -/
def c0 : SeqCoord sz0 :=
  ⟨0, ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true)⟩

/-- **Instance of `GaussianProduct.law_pi`** at `seqP sz0`: the cylinder
`{ω : ω_{c0} ∈ [-1, 1]}`. -/
theorem law_pi_c0 : GaussianProduct.law (seqGvar sz0)
    (Set.pi (↑({c0} : Finset (SeqCoord sz0))) fun _ => Set.Icc (-1 : ℝ) 1) =
      ∏ i ∈ ({c0} : Finset (SeqCoord sz0)),
        (gaussianReal 0 (seqGvar sz0 i)) (Set.Icc (-1 : ℝ) 1) :=
  GaussianProduct.law_pi (seqGvar sz0) (fun _ _ => measurableSet_Icc)

/-- The coordinate `c0` has positive variance `W^{-d} (1 + 2 d g²)⁻¹ = (32^3)⁻¹ (1 + 6/64²)⁻¹`. -/
theorem gvar_c0_pos : 0 < (seqGvar sz0 c0 : ℝ) := by
  have h : (seqGvar sz0 c0 : ℝ) = svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 0 := by
    simp [seqGvar, gvarF, c0]
    rfl
  rw [h, svarF_diag, sz0_values.2.1, sz0_values.2.2.2]
  norm_num

/-- **Instance of `GaussianProduct.map_update`** at the model measure `seqP sz0` (via
`Sizes.seqP_eq_law`): resampling one coordinate from its own law leaves `seqP sz0` invariant. -/
theorem map_update_seqP (c : SeqCoord sz0) :
    ((seqP sz0).prod (gaussianReal 0 (seqGvar sz0 c))).map (upd c) = seqP sz0 :=
  GaussianProduct.map_update (seqGvar sz0) c

/-- **Instance of `GaussianProduct.stein`** at the model measure `seqP sz0`: the coordinate `c0`,
`g = sin`, `g' = cos` (nonconstant, bounded, with bounded derivative):
`E[ω_c sin ω_c] = Var(ω_c) E[cos ω_c]`. -/
theorem stein_sin_seqP :
    ∫ ω, ω c0 • (↑(Real.sin (ω c0)) : ℂ) ∂(seqP sz0) =
      (seqGvar sz0 c0 : ℝ) • ∫ ω, (↑(Real.cos (ω c0)) : ℂ) ∂(seqP sz0) := by
  have hg : Continuous fun ω : SeqΩ sz0 => (↑(Real.sin (ω c0)) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_apply c0))
  have hg' : Continuous fun ω : SeqΩ sz0 => (↑(Real.cos (ω c0)) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_apply c0))
  have hd : ∀ ω : SeqΩ sz0, HasDerivAt
      (fun t : ℝ => (fun ω : SeqΩ sz0 => (↑(Real.sin (ω c0)) : ℂ)) (Function.update ω c0 t))
      ((fun ω : SeqΩ sz0 => (↑(Real.cos (ω c0)) : ℂ)) ω) (ω c0) := by
    intro ω
    simpa using (Real.hasDerivAt_sin (ω c0)).ofReal_comp
  exact GaussianProduct.stein (seqGvar sz0) c0 _ _ hg hg' hd
    ⟨1, fun ω => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (ω c0)⟩
    ⟨1, fun ω => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (ω c0)⟩

end RBM.Gauss.DominationAtInst
