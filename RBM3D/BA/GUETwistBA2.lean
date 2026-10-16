/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUETwistBA
import RBM3D.BA.TwistAvgB

/-!
# BA-C5 row b′, part 2: the twisted 1-loop law `gueGrid_twistBA` at block Anderson

Ticket T2519 (row b′, target 7; Amend 1 item 5, Amend 2 items 1-3, Amend 3 items 2-3).  Steps 4-5
of Lemma T.7 (TL1, `docs/tickets/T2398-TL-proofs.md:64-78`; its input Lemma 8.3 is `lem:propM`,
`paper/tex/7_8_light_weight.tex:1846-1910`) on the grid times of `gueHBA`, after Steps 1-3 of
`BA/GUETwistBA` (the moment identity, the Hilbert-Schmidt bounds of the derivative terms, the PB
interface):

* §1 the abstract recursion `GUETwistBA_moment_bound` and its tail form
  `GUETwistBA_moment_tail` (bootstrap `TwistAvgB_S1`: the real recursion
  `X^{2p} ≤ C_M ρ Λ (X^{2p-1} + X · X^{2p-1}) + (2p-1) A X^{2p-2} + e` gives `X ≤ C' w B`;
  Markov);
* §2 `GUETwistBA_time`: one grid time `(n, j)` and one pair of blocks,
  `P(s < |T_{qa}|) ≤ (C' ρ² Λ_j / s)^{2p}`;
* §3 `GUETwistBA_step`: one size `n`, the union over the grid times and the pairs of blocks,
  the trivial regime `Λ_j ≥ N^{-τ}` from the entrywise local law;
  §4 **`gueGrid_twistBA`** (text `T2519_HoffBA`, probe `t/T2519` b992c2e7);
  §5 the compiled nonempty instance at `d = 3`, `sz0`, the BA flow datum of `sz0` (PB and the
  K-bound stay hypotheses).

The private statements `TwistAvgB_S1`, `TwistAvgB_markov`, `TwistAvgB_expo`, `TwistAvgB_union`
are read by `open private` (Amend 3 item 3); no `BA/TwistAvg*` file is edited.  Helpers carry the
stem `GUETwistBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open private TwistAvgB_S1 TwistAvgB_markov TwistAvgB_expo TwistAvgB_union from RBM3D.BA.TwistAvgB
open private Hyp_primRhs_one from RBM3D.Universality.GUEPhase.HypA
open private ExpAvgGen_G_cont ExpAvgGen_G_norm ExpAvgGen_Hb_herm ExpAvgGen_Gres_blockMat ExpAvgGen_trG_bdd
  from RBM3D.Chain.ExpAvgGen
open private OneLoop_blockMat_Xmat OneLoop_gloop_one from RBM3D.Universality.GUEPhase.OneLoop
open private GUEOneLoop_H0_herm GUEOneLoop_Mdata from RBM3D.BA.GUEOneLoop

noncomputable section

namespace RBM.BA

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

section Abstract

variable {ι : Type*} [Fintype ι]

theorem GUETwistBA_norm_Phi (p : ℕ) (hp : 1 ≤ p) (x : ℂ) : ‖GUETwistBA_Phi p x‖ = ‖x‖ ^ (2 * p - 1) := by
  unfold GUETwistBA_Phi
  rw [norm_mul, norm_pow, norm_pow, norm_star, ← pow_add]
  congr 1
  omega

theorem GUETwistBA_norm_P_le (p : ℕ) (hp : 1 ≤ p) (Mb : ι → ι → ℂ) (q a : ι) (Dv Tv : ι → ℂ) (Tq R1 R2 : ℂ) :
    ‖∑ p', Mb q p' * (Dv p' * (Mb p' a + Tv p') * GUETwistBA_Phi p Tq) + ((p : ℂ) - 1) * (R1 * (Tq ^ (p - 2) * star Tq ^ p)) +
        (p : ℂ) * (R2 * (((‖Tq‖ ^ (2 * p - 2) : ℝ)) : ℂ))‖ ≤
      ∑ p', ‖Mb q p'‖ * (‖Dv p'‖ * (‖Mb p' a‖ + ‖Tv p'‖) * ‖Tq‖ ^ (2 * p - 1)) + ((p : ℝ) - 1) * (‖R1‖ * ‖Tq‖ ^ (2 * p - 2)) +
        (p : ℝ) * (‖R2‖ * ‖Tq‖ ^ (2 * p - 2)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : ‖∑ p', Mb q p' * (Dv p' * (Mb p' a + Tv p') * GUETwistBA_Phi p Tq)‖ ≤
      ∑ p', ‖Mb q p'‖ * (‖Dv p'‖ * (‖Mb p' a‖ + ‖Tv p'‖) * ‖Tq‖ ^ (2 * p - 1)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p' _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, GUETwistBA_norm_Phi p hp]
    gcongr
    exact norm_add_le _ _
  have hp' : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
    have : (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h2 : ‖((p : ℂ) - 1) * (R1 * (Tq ^ (p - 2) * star Tq ^ p))‖ ≤ ((p : ℝ) - 1) * (‖R1‖ * ‖Tq‖ ^ (2 * p - 2)) := by
    rw [norm_mul, hp', norm_mul]
    rcases Nat.lt_or_ge p 2 with h | h
    · have : p = 1 := by omega
      subst this
      simp
    · refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_of_eq ?_) (norm_nonneg _)) (by linarith)
      rw [norm_mul, norm_pow, norm_pow, norm_star, ← pow_add]
      congr 1
      omega
  have h3 : ‖(p : ℂ) * (R2 * (((‖Tq‖ ^ (2 * p - 2) : ℝ)) : ℂ))‖ ≤ (p : ℝ) * (‖R2‖ * ‖Tq‖ ^ (2 * p - 2)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg (by positivity)]
  calc _ ≤ ‖∑ p', Mb q p' * (Dv p' * (Mb p' a + Tv p') * GUETwistBA_Phi p Tq)‖ +
        ‖((p : ℂ) - 1) * (R1 * (Tq ^ (p - 2) * star Tq ^ p))‖ + ‖(p : ℂ) * (R2 * (((‖Tq‖ ^ (2 * p - 2) : ℝ)) : ℂ))‖ :=
        (norm_add₃_le).trans (le_refl _)
    _ ≤ _ := by linarith


/-- **The moment recursion at the maximiser** (Step 4 of Lemma T.7, abstract form): from the identity `hid` and the pathwise bounds off
the exceptional set `Tex`, `X = max_{q,a} (𝔼 |T_{qa}|^{2p})^{1/2p}` satisfies
`X^{2p} ≤ C_M ρΛ (X^{2p-1} + X · X^{2p-1}) + (2p-1) A X^{2p-2} + (C_M + 2p)(E+1)^{2p+1} δ`. -/
theorem GUETwistBA_moment_bound {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ] [Nonempty ι]
    (Mb : ι → ι → ℂ) (T : ι → ι → Ω' → ℂ) (D : ι → Ω' → ℂ) (R1 R2 : ι → ι → Ω' → ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hTm : ∀ q a, Measurable (T q a))
    {E : ℝ} (hE1 : 1 ≤ E) (hTE : ∀ q a ω, ‖T q a ω‖ ≤ E) (hDE : ∀ q ω, ‖D q ω‖ ≤ E)
    (hRE : ∀ q a ω, ‖R1 q a ω‖ ≤ E ∧ ‖R2 q a ω‖ ≤ E)
    (hMb1 : ∀ q a, ‖Mb q a‖ ≤ 1) {CM : ℝ} (hCM : ∀ q, ∑ p', ‖Mb q p'‖ ≤ CM)
    (Tex : Set Ω') (hTex : MeasurableSet Tex) {δ : ℝ} (hδ : μ.real Tex ≤ δ)
    {ρΛ A : ℝ} (hρΛ : 0 ≤ ρΛ) (hA : 0 ≤ A) (hD : ∀ ω ∉ Tex, ∀ q, ‖D q ω‖ ≤ ρΛ)
    (hR : ∀ ω ∉ Tex, ∀ q a, ‖R1 q a ω‖ ≤ A ∧ ‖R2 q a ω‖ ≤ A)
    (hid : ∀ q a, ∫ ω, ((‖T q a ω‖ ^ (2 * p) : ℝ) : ℂ) ∂μ = ∫ ω, (∑ p', Mb q p' * (D p' ω * (Mb p' a + T p' a ω) *
        GUETwistBA_Phi p (T q a ω)) + ((p : ℂ) - 1) * (R1 q a ω * (T q a ω ^ (p - 2) * star (T q a ω) ^ p)) +
        (p : ℂ) * (R2 q a ω * (((‖T q a ω‖ ^ (2 * p - 2) : ℝ)) : ℂ))) ∂μ) :
    ∃ X : ℝ, 0 ≤ X ∧ (∀ q a, ∫ ω, ‖T q a ω‖ ^ (2 * p) ∂μ ≤ X ^ (2 * p)) ∧
      X ^ (2 * p) ≤ CM * ρΛ * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) + (2 * (p : ℝ) - 1) * A * X ^ (2 * p - 2) +
        (CM + 2 * p) * (E + 1) ^ (2 * p + 1) * δ := by
  classical
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hE0 : 0 ≤ E := by linarith
  have hCM0 : 0 ≤ CM := by
    obtain ⟨i0⟩ := ‹Nonempty ι›
    exact (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hCM i0)
  set Y : ι → ι → ℝ := fun q a => ∫ ω, ‖T q a ω‖ ^ (2 * p) ∂μ with hYdef
  have hY0 : ∀ q a, 0 ≤ Y q a := fun q a => integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  set Xq : ι → ι → ℝ := fun q a => Y q a ^ ((1 : ℝ) / (2 * (p : ℝ))) with hXqdef
  have hXq0 : ∀ q a, 0 ≤ Xq q a := fun q a => Real.rpow_nonneg (hY0 q a) _
  have hXqY : ∀ q a, Xq q a ^ (2 * p) = Y q a := fun q a => TwistAvgA2_root_pow_self (Y q a) (hY0 q a) p hp
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hne : (Finset.univ : Finset (ι × ι)).Nonempty := ⟨(i0, i0), Finset.mem_univ _⟩
  obtain ⟨⟨q, a⟩, -, hqa⟩ := Finset.exists_mem_eq_sup' hne (fun x : ι × ι => Xq x.1 x.2)
  set X := Finset.univ.sup' hne (fun x : ι × ι => Xq x.1 x.2) with hXdef
  have hXle : ∀ q a, Xq q a ≤ X := fun q a => Finset.le_sup' (fun x : ι × ι => Xq x.1 x.2) (Finset.mem_univ (q, a))
  have hX0 : 0 ≤ X := (hXq0 i0 i0).trans (hXle i0 i0)
  have hYX : ∀ q a, Y q a ≤ X ^ (2 * p) := fun q a => by
    rw [← hXqY]; exact pow_le_pow_left₀ (hXq0 q a) (hXle q a) _
  refine ⟨X, hX0, hYX, ?_⟩
  have hXqa : Xq q a = X := hqa.symm
  have hYqa : Y q a = X ^ (2 * p) := by rw [← hXqY q a, hXqa]
  -- measurability and bounds of the real integrands
  have hnT : ∀ q a, Measurable fun ω => ‖T q a ω‖ := fun q a => (hTm q a).norm
  have hnT0 : ∀ q a ω, 0 ≤ ‖T q a ω‖ := fun _ _ _ => norm_nonneg _
  -- the pointwise bound
  set Fg : Ω' → ℝ := fun ω => ρΛ * ∑ p', ‖Mb q p'‖ * ((1 + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1)) +
    (2 * (p : ℝ) - 1) * A * ‖T q a ω‖ ^ (2 * p - 2) with hFg
  set Fb : ℝ := (CM + 2 * p) * (E + 1) ^ (2 * p + 1) with hFb
  have hFb0 : 0 ≤ Fb := by positivity
  have hFg0 : ∀ ω, 0 ≤ Fg ω := fun ω => by
    have : 0 ≤ 2 * (p : ℝ) - 1 := by linarith
    simp only [hFg]
    positivity
  have hpt : ∀ ω, ‖∑ p', Mb q p' * (D p' ω * (Mb p' a + T p' a ω) * GUETwistBA_Phi p (T q a ω)) +
      ((p : ℂ) - 1) * (R1 q a ω * (T q a ω ^ (p - 2) * star (T q a ω) ^ p)) +
      (p : ℂ) * (R2 q a ω * (((‖T q a ω‖ ^ (2 * p - 2) : ℝ)) : ℂ))‖ ≤ Fg ω + Tex.indicator (fun _ => Fb) ω := by
    intro ω
    refine (GUETwistBA_norm_P_le p hp Mb q a (fun p' => D p' ω) (fun p' => T p' a ω) (T q a ω) (R1 q a ω) (R2 q a ω)).trans ?_
    by_cases hω : ω ∈ Tex
    · rw [Set.indicator_of_mem hω]
      have h1 : ∑ p', ‖Mb q p'‖ * (‖D p' ω‖ * (‖Mb p' a‖ + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1)) ≤
          ∑ p', ‖Mb q p'‖ * (E * (1 + E) * E ^ (2 * p - 1)) := by
        refine Finset.sum_le_sum fun p' _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have := hTE q a ω
        have := hTE p' a ω
        have := hMb1 p' a
        have := hDE p' ω
        gcongr
      have h2 : ∑ p', ‖Mb q p'‖ * (E * (1 + E) * E ^ (2 * p - 1)) ≤ CM * (E * (1 + E) * E ^ (2 * p - 1)) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hCM q) (by positivity)
      have h3 : ((p : ℝ) - 1) * (‖R1 q a ω‖ * ‖T q a ω‖ ^ (2 * p - 2)) ≤ ((p : ℝ) - 1) * (E * E ^ (2 * p - 2)) := by
        have := (hRE q a ω).1
        have := hTE q a ω
        have h0 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
        gcongr
      have h4 : (p : ℝ) * (‖R2 q a ω‖ * ‖T q a ω‖ ^ (2 * p - 2)) ≤ (p : ℝ) * (E * E ^ (2 * p - 2)) := by
        have := (hRE q a ω).2
        have := hTE q a ω
        gcongr
      have hEe : E * E ^ (2 * p - 2) = E ^ (2 * p - 1) := by rw [← pow_succ']; congr 1; omega
      have hEe2 : E * (1 + E) * E ^ (2 * p - 1) = (1 + E) * E ^ (2 * p) := by
        have : E * E ^ (2 * p - 1) = E ^ (2 * p) := by rw [← pow_succ']; congr 1; omega
        calc E * (1 + E) * E ^ (2 * p - 1) = (1 + E) * (E * E ^ (2 * p - 1)) := by ring
          _ = _ := by rw [this]
      have hE5 : (1 + E) * E ^ (2 * p) ≤ (E + 1) ^ (2 * p + 1) := by
        rw [pow_succ]
        have : E ^ (2 * p) ≤ (E + 1) ^ (2 * p) := pow_le_pow_left₀ hE0 (by linarith) _
        nlinarith [pow_nonneg hE0 (2 * p), pow_nonneg (by linarith : (0 : ℝ) ≤ E + 1) (2 * p)]
      have hE6 : E ^ (2 * p - 1) ≤ (E + 1) ^ (2 * p + 1) :=
        (pow_le_pow_left₀ hE0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
      have hFg1 := hFg0 ω
      have hsum : ∑ p', ‖Mb q p'‖ * (‖D p' ω‖ * (‖Mb p' a‖ + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1)) +
          ((p : ℝ) - 1) * (‖R1 q a ω‖ * ‖T q a ω‖ ^ (2 * p - 2)) + (p : ℝ) * (‖R2 q a ω‖ * ‖T q a ω‖ ^ (2 * p - 2)) ≤
          CM * ((1 + E) * E ^ (2 * p)) + (2 * (p : ℝ) - 1) * E ^ (2 * p - 1) := by
        rw [hEe2] at h1 h2
        rw [hEe] at h3 h4
        linarith
      have hfin : CM * ((1 + E) * E ^ (2 * p)) + (2 * (p : ℝ) - 1) * E ^ (2 * p - 1) ≤ Fb := by
        have hA1 : CM * ((1 + E) * E ^ (2 * p)) ≤ CM * (E + 1) ^ (2 * p + 1) := mul_le_mul_of_nonneg_left hE5 hCM0
        have hA2 : (2 * (p : ℝ) - 1) * E ^ (2 * p - 1) ≤ 2 * p * (E + 1) ^ (2 * p + 1) :=
          mul_le_mul (by linarith) hE6 (pow_nonneg hE0 _) (by positivity)
        simp only [hFb]
        nlinarith [hA1, hA2]
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      have h1 : ∑ p', ‖Mb q p'‖ * (‖D p' ω‖ * (‖Mb p' a‖ + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1)) ≤
          ρΛ * ∑ p', ‖Mb q p'‖ * ((1 + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun p' _ => ?_
        have hd := hD ω hω p'
        have hm := hMb1 p' a
        have : ‖D p' ω‖ * (‖Mb p' a‖ + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1) ≤
            ρΛ * ((1 + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1)) := by
          have h0 : 0 ≤ ‖T q a ω‖ ^ (2 * p - 1) := pow_nonneg (norm_nonneg _) _
          have h5 : ‖D p' ω‖ * (‖Mb p' a‖ + ‖T p' a ω‖) ≤ ρΛ * (1 + ‖T p' a ω‖) := by
            apply mul_le_mul hd (by linarith) (by positivity) hρΛ
          calc _ ≤ (ρΛ * (1 + ‖T p' a ω‖)) * ‖T q a ω‖ ^ (2 * p - 1) := mul_le_mul_of_nonneg_right h5 h0
            _ = _ := by ring
        calc ‖Mb q p'‖ * (‖D p' ω‖ * (‖Mb p' a‖ + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1)) ≤
            ‖Mb q p'‖ * (ρΛ * ((1 + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1))) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = ρΛ * (‖Mb q p'‖ * ((1 + ‖T p' a ω‖) * ‖T q a ω‖ ^ (2 * p - 1))) := by ring
      have h3 : ((p : ℝ) - 1) * (‖R1 q a ω‖ * ‖T q a ω‖ ^ (2 * p - 2)) ≤ ((p : ℝ) - 1) * (A * ‖T q a ω‖ ^ (2 * p - 2)) := by
        have := (hR ω hω q a).1
        have h0 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
        gcongr
      have h4 : (p : ℝ) * (‖R2 q a ω‖ * ‖T q a ω‖ ^ (2 * p - 2)) ≤ (p : ℝ) * (A * ‖T q a ω‖ ^ (2 * p - 2)) := by
        have := (hR ω hω q a).2
        gcongr
      simp only [hFg]
      nlinarith [h1, h3, h4]
  -- integrability of the real building blocks
  have hI_q1 : Integrable (fun ω => ‖T q a ω‖ ^ (2 * p - 1)) μ :=
    Integrable.of_bound ((hnT q a).pow_const _).aestronglyMeasurable (E ^ (2 * p - 1))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hTE q a ω) _)
  have hI_q2 : Integrable (fun ω => ‖T q a ω‖ ^ (2 * p - 2)) μ :=
    Integrable.of_bound ((hnT q a).pow_const _).aestronglyMeasurable (E ^ (2 * p - 2))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hTE q a ω) _)
  have hI_pq : ∀ p', Integrable (fun ω => ‖T p' a ω‖ * ‖T q a ω‖ ^ (2 * p - 1)) μ := fun p' =>
    Integrable.of_bound ((hnT p' a).mul ((hnT q a).pow_const _)).aestronglyMeasurable (E * E ^ (2 * p - 1))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))]
        exact mul_le_mul (hTE p' a ω) (pow_le_pow_left₀ (norm_nonneg _) (hTE q a ω) _) (pow_nonneg (norm_nonneg _) _) hE0)
  -- the moment bounds (Lyapunov, Hölder)
  have hB1 : ∫ ω, ‖T q a ω‖ ^ (2 * p - 1) ∂μ ≤ X ^ (2 * p - 1) := by
    have h : ∫ ω, ‖T q a ω‖ ^ (2 * p - 1) ∂μ ≤ Xq q a ^ (2 * p - 1) :=
      TwistAvgA2_lyap1 μ p hp (g := fun ω => ‖T q a ω‖) (fun ω => norm_nonneg _) (hnT q a) (Cg := E) (hTE q a)
    rwa [hXqa] at h
  have hB2 : ∫ ω, ‖T q a ω‖ ^ (2 * p - 2) ∂μ ≤ X ^ (2 * p - 2) := by
    have h : ∫ ω, ‖T q a ω‖ ^ (2 * p - 2) ∂μ ≤ Xq q a ^ (2 * p - 2) :=
      TwistAvgA2_lyap2 μ p hp (g := fun ω => ‖T q a ω‖) (fun ω => norm_nonneg _) (hnT q a) (Cg := E) (hTE q a)
    rwa [hXqa] at h
  have hB3 : ∀ p', ∫ ω, ‖T p' a ω‖ * ‖T q a ω‖ ^ (2 * p - 1) ∂μ ≤ X * X ^ (2 * p - 1) := by
    intro p'
    have h : ∫ ω, ‖T p' a ω‖ * ‖T q a ω‖ ^ (2 * p - 1) ∂μ ≤ Xq p' a * Xq q a ^ (2 * p - 1) :=
      TwistAvgA2_holder_nat μ p hp (f := fun ω => ‖T p' a ω‖) (g := fun ω => ‖T q a ω‖) (fun ω => norm_nonneg _)
        (fun ω => norm_nonneg _) (hnT p' a) (hnT q a) (Cf := E) (Cg := E) (hTE p' a) (hTE q a)
    rw [hXqa] at h
    exact h.trans (mul_le_mul (hXle p' a) le_rfl (pow_nonneg hX0 _) hX0)
  -- integrability of the dominating function
  have hs : ∀ p', Integrable (fun ω => ‖Mb q p'‖ * (‖T q a ω‖ ^ (2 * p - 1) + ‖T p' a ω‖ * ‖T q a ω‖ ^ (2 * p - 1))) μ :=
    fun p' => (hI_q1.add (hI_pq p')).const_mul _
  have hFgeq : Fg = fun ω => ρΛ * ∑ p', ‖Mb q p'‖ * (‖T q a ω‖ ^ (2 * p - 1) + ‖T p' a ω‖ * ‖T q a ω‖ ^ (2 * p - 1)) +
      (2 * (p : ℝ) - 1) * A * ‖T q a ω‖ ^ (2 * p - 2) := by
    funext ω
    simp only [hFg]
    congr 2
    exact Finset.sum_congr rfl fun p' _ => by ring
  have hIFg : Integrable Fg μ := by
    rw [hFgeq]
    exact ((integrable_finsetSum _ fun p' _ => hs p').const_mul _).add (hI_q2.const_mul _)
  have hIind : Integrable (Tex.indicator fun _ => Fb) μ := (integrable_const _).indicator hTex
  have hFgInt : ∫ ω, Fg ω ∂μ = ρΛ * ∑ p', ‖Mb q p'‖ * (∫ ω, ‖T q a ω‖ ^ (2 * p - 1) ∂μ +
      ∫ ω, ‖T p' a ω‖ * ‖T q a ω‖ ^ (2 * p - 1) ∂μ) + (2 * (p : ℝ) - 1) * A * ∫ ω, ‖T q a ω‖ ^ (2 * p - 2) ∂μ := by
    rw [hFgeq, integral_add ((integrable_finsetSum _ fun p' _ => hs p').const_mul _) (hI_q2.const_mul _), integral_const_mul,
      integral_finsetSum _ (fun p' _ => hs p'), integral_const_mul]
    congr 2
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [integral_const_mul, integral_add hI_q1 (hI_pq p')]
  have hFgle : ∫ ω, Fg ω ∂μ ≤ CM * ρΛ * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) + (2 * (p : ℝ) - 1) * A * X ^ (2 * p - 2) := by
    rw [hFgInt]
    have h1 : ∑ p', ‖Mb q p'‖ * (∫ ω, ‖T q a ω‖ ^ (2 * p - 1) ∂μ + ∫ ω, ‖T p' a ω‖ * ‖T q a ω‖ ^ (2 * p - 1) ∂μ) ≤
        CM * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) := by
      calc _ ≤ ∑ p', ‖Mb q p'‖ * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) :=
            Finset.sum_le_sum fun p' _ => mul_le_mul_of_nonneg_left (add_le_add hB1 (hB3 p')) (norm_nonneg _)
        _ = (∑ p', ‖Mb q p'‖) * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) := (Finset.sum_mul _ _ _).symm
        _ ≤ CM * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) :=
            mul_le_mul_of_nonneg_right (hCM q) (by positivity)
    have h2 : (2 * (p : ℝ) - 1) * A * ∫ ω, ‖T q a ω‖ ^ (2 * p - 2) ∂μ ≤ (2 * (p : ℝ) - 1) * A * X ^ (2 * p - 2) :=
      mul_le_mul_of_nonneg_left hB2 (mul_nonneg (by linarith) hA)
    nlinarith [mul_le_mul_of_nonneg_left h1 hρΛ]
  -- the chain `Y ≤ ‖∫ P‖ ≤ ∫ ‖P‖ ≤ ∫ Fg + δ F_b`
  have hchain : Y q a ≤ ∫ ω, (Fg ω + Tex.indicator (fun _ => Fb) ω) ∂μ := by
    have h := hid q a
    rw [integral_complex_ofReal] at h
    have h1 : Y q a = ‖∫ ω, (∑ p', Mb q p' * (D p' ω * (Mb p' a + T p' a ω) * GUETwistBA_Phi p (T q a ω)) +
        ((p : ℂ) - 1) * (R1 q a ω * (T q a ω ^ (p - 2) * star (T q a ω) ^ p)) +
        (p : ℂ) * (R2 q a ω * (((‖T q a ω‖ ^ (2 * p - 2) : ℝ)) : ℂ))) ∂μ‖ := by
      rw [← h, Complex.norm_real, Real.norm_of_nonneg (hY0 q a)]
    rw [h1]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) (hIFg.add hIind)
      (Filter.Eventually.of_forall hpt)
  rw [integral_add hIFg hIind, integral_indicator_const _ hTex] at hchain
  simp only [smul_eq_mul, measureReal_def] at hchain
  have hδ' : (μ Tex).toReal * Fb ≤ δ * Fb := mul_le_mul_of_nonneg_right hδ hFb0
  rw [← hYqa]
  simp only [hFb] at hδ' ⊢
  linarith [hchain, hFgle, hδ']


/-- **The tail bound of the twisted trace** (Steps 4-5 of Lemma T.7, abstract form): the recursion of `GUETwistBA_moment_bound`, the real
bootstrap `TwistAvgB_S1`, and Markov: for `K w B` with `K w B ≤ 1/2`, `C_M ρΛ ≤ K w B`, `A ≤ K w B²`, `e ≤ B^{2p}`,
`μ{s < |T_{qa}|} ≤ (C' w B / s)^{2p}`, `C' = (4p+2) K + 2`. -/
theorem GUETwistBA_moment_tail {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ] [Nonempty ι]
    (Mb : ι → ι → ℂ) (T : ι → ι → Ω' → ℂ) (D : ι → Ω' → ℂ) (R1 R2 : ι → ι → Ω' → ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hTm : ∀ q a, Measurable (T q a))
    {E : ℝ} (hE1 : 1 ≤ E) (hTE : ∀ q a ω, ‖T q a ω‖ ≤ E) (hDE : ∀ q ω, ‖D q ω‖ ≤ E)
    (hRE : ∀ q a ω, ‖R1 q a ω‖ ≤ E ∧ ‖R2 q a ω‖ ≤ E)
    (hMb1 : ∀ q a, ‖Mb q a‖ ≤ 1) {CM : ℝ} (hCM : ∀ q, ∑ p', ‖Mb q p'‖ ≤ CM)
    (Tex : Set Ω') (hTex : MeasurableSet Tex) {δ : ℝ} (hδ : μ.real Tex ≤ δ)
    {ρΛ A : ℝ} (hρΛ : 0 ≤ ρΛ) (hA : 0 ≤ A) (hD : ∀ ω ∉ Tex, ∀ q, ‖D q ω‖ ≤ ρΛ)
    (hR : ∀ ω ∉ Tex, ∀ q a, ‖R1 q a ω‖ ≤ A ∧ ‖R2 q a ω‖ ≤ A)
    (hid : ∀ q a, ∫ ω, ((‖T q a ω‖ ^ (2 * p) : ℝ) : ℂ) ∂μ = ∫ ω, (∑ p', Mb q p' * (D p' ω * (Mb p' a + T p' a ω) *
        GUETwistBA_Phi p (T q a ω)) + ((p : ℂ) - 1) * (R1 q a ω * (T q a ω ^ (p - 2) * star (T q a ω) ^ p)) +
        (p : ℂ) * (R2 q a ω * (((‖T q a ω‖ ^ (2 * p - 2) : ℝ)) : ℂ))) ∂μ)
    {K w B : ℝ} (hK : 0 < K) (hw : 1 ≤ w) (hB : 0 < B) (ha : K * (w * B) ≤ 1 / 2) (hCMK : CM * ρΛ ≤ K * (w * B))
    (hAK : A ≤ K * (w * B ^ 2)) (he : (CM + 2 * p) * (E + 1) ^ (2 * p + 1) * δ ≤ B ^ (2 * p)) {s : ℝ} (hs : 0 < s) (q a : ι) :
    μ {ω | s < ‖T q a ω‖} ≤ ENNReal.ofReal ((((4 * p + 2) * K + 2) * (w * B) / s) ^ (2 * p)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨X, hX0, hXY, hXrec⟩ := GUETwistBA_moment_bound μ Mb T D R1 R2 p hp hTm hE1 hTE hDE hRE hMb1 hCM Tex hTex hδ
    hρΛ hA hD hR hid
  have hCM0 : 0 ≤ CM := by
    obtain ⟨i0⟩ := ‹Nonempty ι›
    exact (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hCM i0)
  have hXb : X ≤ ((4 * p + 2) * K + 2) * (w * B) := by
    refine TwistAvgB_S1 hp hK hw hB ha he ?_
    have h1 : CM * ρΛ * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) ≤ K * (w * B) * (X ^ (2 * p - 1) + X * X ^ (2 * p - 1)) :=
      mul_le_mul_of_nonneg_right hCMK (by positivity)
    have h2 : (2 * (p : ℝ) - 1) * A * X ^ (2 * p - 2) ≤ 2 * p * K * (w * B ^ 2) * X ^ (2 * p - 2) := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hX0 _)
      calc (2 * (p : ℝ) - 1) * A ≤ 2 * p * A := mul_le_mul_of_nonneg_right (by linarith) hA
        _ ≤ 2 * p * (K * (w * B ^ 2)) := mul_le_mul_of_nonneg_left hAK (by positivity)
        _ = _ := by ring
    linarith
  have hint : Integrable (fun ω => ‖T q a ω‖ ^ (2 * p)) μ :=
    Integrable.of_bound ((hTm q a).norm.pow_const _).aestronglyMeasurable (E ^ (2 * p))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hTE q a ω) _)
  have hmom : ∫ ω, ‖T q a ω‖ ^ (2 * p) ∂μ ≤ (((4 * p + 2) * K + 2) * (w * B)) ^ (2 * p) :=
    (hXY q a).trans (pow_le_pow_left₀ hX0 hXb _)
  exact TwistAvgB_markov μ (T := fun ω => ‖T q a ω‖) (fun ω => norm_nonneg _) hint hs hmom

end Abstract

section Time

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
-- the per-time core (Steps 1-5 of T.7 at one grid time) needs more than the default 200000 heartbeats
/-- **One grid time** (Steps 1-5 of Lemma T.7 at `(n, j)`): the one-time law of `gueHBA … j` is `law v` (`v_c = t₁ gvar_c + c₀ w_c`), the
moment identity `GUETwistBA_momentId`, the envelope, the good-event bounds off the exceptional set `B`, and the tail lemma give
`μ{s < |T_{qa}|} ≤ (C' ρ² Λ_j / s)^{2p}` for every pair of blocks.  `ρ = N^ε`; the numeric conditions `K ρ² Λ_j ≤ 1/2`,
`(C_M + 2p)(E+1)^{2p+1} δ ≤ Λ_j^{2p}` are hypotheses (discharged eventually in `n` in the theorem). -/
theorem GUETwistBA_time (sz : Sizes d) (hd : 3 ≤ d) {Λ κ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (n : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    (hg : 0 < g n ∧ g n ≤ Λ) (hr : BAReal d (sz.L n) (g n) κ (E n) (m n)) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (K : ℕ → ℕ) (hK : K n ≠ 0) (j : Fin (K n + 1)) {p : ℕ} (hp : 1 ≤ p) {ε : ℝ}
    (B : Set (PathΩ (sz.withLam 0))) (hBm : MeasurableSet B) {δ : ℝ} (hδ : (Pgue (sz.withLam 0)).real B ≤ δ)
    (hgood : ∀ ω ∉ B, GUETwistBA_Good sz g E t1 t0 m K ε n ω)
    (hΛ1 : (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ≤ 1)
    (hρ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ ε)
    (ha : (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) * (((sz.size n : ℕ) : ℝ) ^ ε) ^ 2 *
      (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ≤ 1 / 2)
    (he : (((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 2 * p) *
      (2 * ((sz.size n : ℕ) : ℝ) ^ 2 * (((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ 3 + 1) ^ (2 * p + 1) * δ ≤
      ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ (2 * p))
    {s : ℝ} (hs : 0 < s) (q a : Zd d (sz.L n)) :
    Pgue (sz.withLam 0) {ω | s < ‖GUETwistBA_Tm d (sz.L n) (sz.W n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) q a
        (Gres (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) true)‖} ≤
      ENNReal.ofReal (((((4 * p + 2) * (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) + 2) *
        ((((sz.size n : ℕ) : ℝ) ^ ε) ^ 2 * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹)) / s) ^ (2 * p)) := by
  classical
  have hL3 := sz.three_le_L n
  have hW0 := sz.W_pos n
  have hLpos : (0 : ℝ) < sz.L n := by exact_mod_cast (show 0 < sz.L n by omega)
  have hWpos : (0 : ℝ) < sz.W n := by exact_mod_cast hW0
  have hNeq : ((sz.size n : ℕ) : ℝ) = (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNeq]; positivity
  have hN1 : 1 ≤ N := by
    have h1 : 1 ≤ sz.size n := sz.one_le_size n
    rw [hNdef]
    exact_mod_cast h1
  -- the grid time
  set Δ := gridStep t1 t0 K n with hΔdef
  set u := gridTime t1 t0 K n j with hudef
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hKpos.le
  have hjK : ((j : ℕ) : ℝ) ≤ K n := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  have hkΔ : ((j : ℕ) : ℝ) * Δ ≤ t0 n - t1 n := by
    calc ((j : ℕ) : ℝ) * Δ ≤ K n * Δ := mul_le_mul_of_nonneg_right hjK hΔ0
      _ = t0 n - t1 n := by rw [hΔdef, gridStep]; field_simp
  have hu_eq : u = t1 n + ((j : ℕ) : ℝ) * Δ := rfl
  have hkΔ0 : 0 ≤ ((j : ℕ) : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg _) hΔ0
  have hu0 : 0 ≤ u := by rw [hu_eq]; linarith
  have hu1 : u < 1 := by rw [hu_eq]; linarith
  -- the flow data
  have hmim : κ ≤ (m n).im := hr.2
  have hm1 : ‖m n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) hr.1
  have him1 : (m n).im ≤ 1 := ((le_abs_self _).trans (Complex.abs_im_le_norm (m n))).trans hm1
  have hκ1 : κ ≤ 1 := hmim.trans him1
  set η := etaOf (m n) u with hηdef
  have hηpos : 0 < η := by
    rw [hηdef, etaOf]
    exact mul_pos (by linarith) (by linarith)
  have hηle : η ≤ 1 := by
    rw [hηdef, etaOf]
    calc (1 - u) * (m n).im ≤ 1 * 1 := mul_le_mul (by linarith) him1 (by linarith) zero_le_one
      _ = 1 := one_mul 1
  set Λu := (N * η)⁻¹ with hΛdef
  have hΛ0 : 0 < Λu := by positivity
  have hηinv : η⁻¹ = N * Λu := by rw [hΛdef]; field_simp
  -- the one-time law of step `j`
  set aa := Real.sqrt (t1 n) with haa
  set bb := Real.sqrt (Δ / N) with hbb
  have haa2 : aa ^ 2 = t1 n := Real.sq_sqrt ht1
  have hbb2 : bb ^ 2 = Δ / N := Real.sq_sqrt (div_nonneg hΔ0 hNpos.le)
  set c0 : ℝ := ((j : ℕ) : ℝ) * bb ^ 2 with hc0
  have hc00 : 0 ≤ c0 := by rw [hc0]; positivity
  set σ : ℝ := c0 * (sz.W n : ℝ) ^ d with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  have hsum : t1 n + (sz.L n : ℝ) ^ d * σ = u := by
    rw [hσdef, hc0, hbb2, hu_eq, hNeq]
    field_simp
  have hv : ∀ c : CoordF d (sz.L n) (sz.W n), (olVar (sz.withLam 0) aa bb j ⟨n, c⟩ : ℝ) =
      t1 n * (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2) := by
    intro c
    have hg' : ((Sizes.seqGvar (sz.withLam 0) ⟨n, c⟩ : ℝ≥0) : ℝ) = (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) := rfl
    simp only [olVar, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul, hg', haa2]
    by_cases hc : c.1 = c.2.1
    · have hc' : (⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.1 = (⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.2.1 := hc
      simp only [gueUnitVar, eq_true hc', eq_true hc, hc0, ↓reduceIte, NNReal.coe_one]
      push_cast
      ring
    · have hc' : ¬ ((⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.1 =
          (⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.2.1) := hc
      simp only [gueUnitVar, eq_false hc', eq_false hc, hc0, ↓reduceIte]
      push_cast
      ring
  set φ : PathΩ (sz.withLam 0) → Ω d (sz.L n) (sz.W n) :=
    fun ω => Sizes.slice (sz.withLam 0) n (olComb (sz.withLam 0) aa bb j ω) with hφdef
  have hmap : (Pgue (sz.withLam 0)).map φ =
      GaussianProduct.law (fun c : CoordF d (sz.L n) (sz.W n) => olVar (sz.withLam 0) aa bb j ⟨n, c⟩) :=
    ol_map_comb_slice (sz.withLam 0) aa bb j n
  have hφ : Measurable φ := (Sizes.measurable_slice (sz.withLam 0) n).comp (olComb_measurable (sz.withLam 0) aa bb j)
  -- the data of `M`
  set H₀b : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
    blockMat d (sz.L n) (sz.W n) (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) with hH₀b
  have hH₀bh : H₀b.IsHermitian := GUEOneLoop_H0_herm d (sz.L n) (sz.W n) (g n)
  set Mb : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
    blockMat d (sz.L n) (sz.W n) (Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) with hMb
  set z : ℂ := ztOf (m n) (E n) u with hzdef
  have hzim : z.im = η := ztOf_im (m n) (E n) u
  have hz : z.im ≠ 0 := by rw [hzim]; exact hηpos.ne'
  have hEm : ((E n : ℂ) + m n).im ≠ 0 := by
    have : ((E n : ℂ) + m n).im = (m n).im := by simp
    rw [this]
    exact (lt_of_lt_of_le hκ hmim).ne'
  have hblock : ∀ ω, blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω) = H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω) := by
    intro ω
    rw [ol_gueHBA_eq, hH₀b, ← OneLoop_blockMat_Xmat]
    rfl
  obtain ⟨hMM, hmm⟩ := GUEOneLoop_Mdata (L := sz.L n) (W := sz.W n) (u := u) (z := z) hκ hr
    (by simp only [hzdef, ztOf]; ring)
  have hMbl : ∀ (b b' : Zd d (sz.L n)) (o o' : Fin (sz.W n ^ d)), Mb (b, o) (b', o') =
      if o = o' then BAMB d (sz.L n) (g n) (E n : ℂ) (m n) b b' else 0 := fun b b' o o' =>
    GUETwistBA_Mres_entry (g n) (E n : ℂ) (m n) hEm b b' o o'
  -- the sample-space functions
  have hGc : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true :=
    ExpAvgGen_G_cont hH₀bh 1 hz
  have hGφ : Measurable fun ω : PathΩ (sz.withLam 0) => Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true :=
    hGc.measurable.comp hφ
  have hHerm : ∀ ω, (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)).IsHermitian := fun ω => ExpAvgGen_Hb_herm hH₀bh 1 (φ ω)
  have hrow := GUETwistBA_hrow (d := d) (L := sz.L n) hL3 hsum
  have hMb1 : ∀ q a : Zd d (sz.L n), ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) q a‖ ≤ 1 := by
    intro q a
    have hrw := BAMB_row_sq_real d (sz.L n) (g n) (E n) (m n) hr.1 q
    have : ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) q a‖ ^ 2 ≤ 1 := by
      rw [← hrw]
      exact Finset.single_le_sum (f := fun b => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) q b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ a)
    nlinarith [norm_nonneg (BAMB d (sz.L n) (g n) (E n : ℂ) (m n) q a)]
  have hCM : ∀ q : Zd d (sz.L n), ∑ p', ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) q p'‖ ≤
      (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) :=
    fun q => baM_row_l1 (by omega) hL3 Λ (g n) κ (E n) (m n) hΛ hg.1 hg.2 hκ hr q
  have hCM0 : 0 ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hCM 0)
  have hint : ∀ {F : Ω d (sz.L n) (sz.W n) → ℂ}, Continuous F →
      ∫ ω, F (φ ω) ∂(Pgue (sz.withLam 0)) = ∫ ω', F ω' ∂(GaussianProduct.law (fun c : CoordF d (sz.L n) (sz.W n) =>
        olVar (sz.withLam 0) aa bb j ⟨n, c⟩)) := by
    intro F hF
    have h := integral_map hφ.aemeasurable (hF.aestronglyMeasurable (μ := (Pgue (sz.withLam 0)).map φ))
    rw [hmap] at h
    exact h.symm
  set μ := Pgue (sz.withLam 0) with hμ
  set Mbl : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := BAMB d (sz.L n) (g n) (E n : ℂ) (m n) with hMbldef
  set CM : ℝ := (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) with hCMdef
  set ρ : ℝ := N ^ ε with hρdef
  -- the moment identity at `μ`
  have hid : ∀ q a : Zd d (sz.L n), ∫ ω, ((‖GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a
        (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ^ (2 * p) : ℝ) : ℂ) ∂μ =
      ∫ ω, (∑ p', Mbl q p' * (GUETwistBA_Dm d (sz.L n) (sz.W n) (t1 n) σ (m n) p'
          (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true) *
        (Mbl p' a + GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl p' a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)) *
        GUETwistBA_Phi p (GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true))) +
        ((p : ℂ) - 1) * (GUETwistBA_R1m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true) *
          (GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true) ^ (p - 2) *
            star (GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)) ^ p)) +
        (p : ℂ) * (GUETwistBA_R2m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true) *
          (((‖GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ^
            (2 * p - 2) : ℝ)) : ℂ))) ∂μ := by
    intro q a
    have hQ := GUETwistBA_momentId (t1 := t1 n) (c0 := c0) (σ := σ) (u := u) hσdef hsum hL3
      (fun c => olVar (sz.withLam 0) aa bb j ⟨n, c⟩) hv hH₀bh hz hMM hMbl p hp q a
    have hc1 : Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
        ((‖GUETwistBA_T d (sz.L n) (sz.W n) H₀b z Mbl q a ω'‖ ^ (2 * p) : ℝ) : ℂ) := by
      have h := Complex.continuous_ofReal.comp ((continuous_norm.comp ((GUETwistBA_Tm_cont Mbl q a).comp hGc)).pow (2 * p))
      exact h
    have hc2 : Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
        (GUETwistBA_g1 d (sz.L n) (sz.W n) (t1 n) σ (m n) Mbl p q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true) +
          ((p : ℂ) - 1) * GUETwistBA_g2 d (sz.L n) (sz.W n) (t1 n) σ Mbl p q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true) +
          (p : ℂ) * GUETwistBA_g3 d (sz.L n) (sz.W n) (t1 n) σ Mbl p q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true)) := by
      have c1 := (GUETwistBA_g1_cont (t1 n) σ (m n) Mbl p q a).comp hGc
      have c2 := (continuous_const (y := ((p : ℂ) - 1))).mul ((GUETwistBA_g2_cont (t1 n) σ Mbl p q a).comp hGc)
      have c3 := (continuous_const (y := (p : ℂ))).mul ((GUETwistBA_g3_cont (t1 n) σ Mbl p q a).comp hGc)
      exact (c1.add c2).add c3
    rw [← hint hc1, ← hint hc2] at hQ
    exact hQ
  -- the envelope
  have hηz : η ≤ |z.im| := by rw [hzim, abs_of_pos hηpos]
  have hNLW : (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) = N := by rw [hNeq]; push_cast; ring
  have hEnv : ∀ (ω : PathΩ (sz.withLam 0)) (q a p' : Zd d (sz.L n)),
      ‖GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ≤ 2 * N ^ 2 * (N * Λu) ^ 3 ∧
      ‖GUETwistBA_Dm d (sz.L n) (sz.W n) (t1 n) σ (m n) p' (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ≤
        2 * N ^ 2 * (N * Λu) ^ 3 ∧
      ‖GUETwistBA_R1m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ≤
        2 * N ^ 2 * (N * Λu) ^ 3 ∧
      ‖GUETwistBA_R2m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ≤
        2 * N ^ 2 * (N * Λu) ^ 3 := by
    intro ω q a p'
    have h := GUETwistBA_env (hHerm ω) hηpos hηz hηle ht1 hσ0 hu1.le hrow hm1 Mbl hMb1 p' q a
    rw [hNLW, hηinv] at h
    exact h
  have hE1 : 1 ≤ 2 * N ^ 2 * (N * Λu) ^ 3 := by
    have : 1 ≤ N * Λu := by rw [← hηinv]; exact (one_le_inv₀ hηpos).2 hηle
    have h2 : 1 ≤ N ^ 2 * (N * Λu) ^ 3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) (one_le_pow₀ this)
    linarith
  -- the good event
  have hDgood : ∀ ω ∉ B, ∀ q' : Zd d (sz.L n),
      ‖GUETwistBA_Dm d (sz.L n) (sz.W n) (t1 n) σ (m n) q' (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ≤ ρ * Λu := by
    intro ω hω q'
    have hg1 : ∀ b : Zd d (sz.L n), ‖Matrix.trace (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true *
        Eblk d (sz.L n) (sz.W n) b) - m n‖ ≤ ρ * Λu := by
      intro b
      have h := (hgood ω hω j).1 b
      rw [hblock ω, OneLoop_gloop_one] at h
      exact h
    refine (GUETwistBA_Dm_le ht1 hσ0 hrow (m n) q' _ hg1).trans ?_
    exact mul_le_of_le_one_left (by positivity) hu1.le
  have hsq : Real.sqrt (2 * (ρ * Λu) * (2 * (ρ * Λu ^ 3))) = 2 * ρ * Λu ^ 2 := by
    rw [show 2 * (ρ * Λu) * (2 * (ρ * Λu ^ 3)) = (2 * ρ * Λu ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hRgood : ∀ ω ∉ B, ∀ q a : Zd d (sz.L n),
      ‖GUETwistBA_R1m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ≤
        2 * CM * ρ * Λu ^ 2 ∧
      ‖GUETwistBA_R2m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖ ≤
        2 * CM * ρ * Λu ^ 2 := by
    intro ω hω q a
    obtain ⟨h2, h4⟩ := (hgood ω hω j).2.1 hΛ1
    rw [hblock ω] at h2 h4
    have hfin : (∑ p', ‖Mbl q p'‖) * u * (2 * ρ * Λu ^ 2) ≤ 2 * CM * ρ * Λu ^ 2 := by
      have h0 : 0 ≤ 2 * ρ * Λu ^ 2 := by positivity
      calc (∑ p', ‖Mbl q p'‖) * u * (2 * ρ * Λu ^ 2) ≤ CM * 1 * (2 * ρ * Λu ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (hCM q) hu1.le hu0 hCM0) h0
        _ = _ := by ring
    refine ⟨?_, ?_⟩
    · have h := GUETwistBA_R1m_le (hHerm ω) z ht1 hσ0 hrow Mbl q a (B2 := 2 * (ρ * Λu)) (B4 := 2 * (ρ * Λu ^ 3))
        (fun p' => h2 true false a p') (fun s => h4 false false true true s q s a)
      rw [hsq] at h
      exact h.trans hfin
    · have h := GUETwistBA_R2m_le (hHerm ω) z ht1 hσ0 hrow Mbl q a (B2 := 2 * (ρ * Λu)) (B4 := 2 * (ρ * Λu ^ 3))
        (fun p' => h2 false true q p') (fun s => h4 false true false true s a s a)
      rw [hsq] at h
      exact h.trans hfin
  -- measurability and the tail lemma
  have hTm' : ∀ q a : Zd d (sz.L n), Measurable fun ω => GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a
      (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true) := fun q a => (GUETwistBA_Tm_cont Mbl q a).measurable.comp hGφ
  have hρ0 : 0 < ρ := by linarith
  have hres := GUETwistBA_moment_tail μ (ι := Zd d (sz.L n)) Mbl
    (fun q a ω => GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true))
    (fun p' ω => GUETwistBA_Dm d (sz.L n) (sz.W n) (t1 n) σ (m n) p' (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true))
    (fun q a ω => GUETwistBA_R1m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true))
    (fun q a ω => GUETwistBA_R2m d (sz.L n) (sz.W n) (t1 n) σ Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true))
    p hp hTm' (E := 2 * N ^ 2 * (N * Λu) ^ 3) hE1 (fun q a ω => (hEnv ω q a 0).1) (fun q' ω => (hEnv ω 0 0 q').2.1)
    (fun q a ω => ⟨(hEnv ω q a 0).2.2.1, (hEnv ω q a 0).2.2.2⟩) hMb1 hCM B hBm hδ (ρΛ := ρ * Λu) (A := 2 * CM * ρ * Λu ^ 2)
    (by positivity) (by positivity) hDgood hRgood hid (K := 2 * CM + 1) (w := ρ ^ 2) (B := Λu) (by linarith) (one_le_pow₀ hρ) hΛ0
    (by rw [← mul_assoc]; exact ha)
    (by nlinarith [mul_pos hρ0 hΛ0, mul_nonneg hCM0 (mul_pos hρ0 hΛ0).le, mul_nonneg hCM0 (mul_nonneg (sub_nonneg.2 hρ) (mul_pos hρ0 hΛ0).le)])
    (by nlinarith [mul_nonneg hCM0 (mul_nonneg (sub_nonneg.2 hρ) (mul_nonneg hρ0.le (sq_nonneg Λu))), mul_nonneg (sq_nonneg Λu) (sq_nonneg ρ),
      mul_nonneg (sq_nonneg Λu) hρ0.le])
    he hs q a
  have hset : {ω | s < ‖GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a
        (Gres (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) true)‖} =
      {ω | s < ‖GUETwistBA_Tm d (sz.L n) (sz.W n) Mbl q a (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true)‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hblock]
    exact Iff.rfl
  rw [hset]
  exact hres

end Time

section PerN

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

theorem GUETwistBA_gridTime_mem {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (ht10 : t1 n ≤ t0 n) (hK : K n ≠ 0) {k : ℕ} (hk : k ≤ K n) :
    gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n) := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ0 : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) hKpos.le
  have hkK : (k : ℝ) ≤ K n := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · have : 0 ≤ (k : ℝ) * gridStep t1 t0 K n := mul_nonneg (Nat.cast_nonneg _) hΔ0
    change t1 n ≤ t1 n + k * gridStep t1 t0 K n
    linarith
  · calc gridTime t1 t0 K n k = t1 n + (k : ℝ) * gridStep t1 t0 K n := rfl
      _ ≤ t1 n + K n * gridStep t1 t0 K n := by gcongr
      _ = t0 n := by rw [gridStep]; field_simp; ring

theorem GUETwistBA_eta_pos_le {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hκ : 0 < κ) (hr : BAReal d L g κ E m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 < etaOf m u ∧ etaOf m u ≤ 1 := by
  have hmim : κ ≤ m.im := hr.2
  have hm1 : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  have him1 : m.im ≤ 1 := ((le_abs_self _).trans (Complex.abs_im_le_norm m)).trans hm1
  refine ⟨?_, ?_⟩
  · rw [etaOf]; exact mul_pos (by linarith) (by linarith)
  · rw [etaOf]
    calc (1 - u) * m.im ≤ 1 * 1 := mul_le_mul (by linarith) him1 (by linarith) zero_le_one
      _ = 1 := one_mul 1

end PerN

section Num

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

theorem GUETwistBA_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, Matrix.nonsing_inv_eq_ringInverse, ite_true]

theorem GUETwistBA_Ld_le (sz : Sizes d) (n : ℕ) : (sz.L n) ^ d ≤ sz.size n := by
  rw [Sizes.size]; exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

/-- The number of the indices `(j, a, q)` (grid time, pair of blocks) is at most `(K + 1) N²`. -/
theorem GUETwistBA_card_idx (sz : Sizes d) (n k : ℕ) :
    Fintype.card (Fin (k + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ≤ (k + 1) * sz.size n ^ 2 := by
  have hL := GUETwistBA_Ld_le sz n
  rw [Fintype.card_prod, Fintype.card_prod, card_Zd, Fintype.card_fin]
  calc (k + 1) * ((sz.L n) ^ d * (sz.L n) ^ d) ≤ (k + 1) * (sz.size n * sz.size n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hL hL)
    _ = _ := by ring

/-- The trivial regime: `Λ ≥ N^{-τ}` gives `N^{τ/4} Λ^{1/2} ≤ N^τ Λ`. -/
theorem GUETwistBA_triv {N τ x : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) (hx : N ^ (-τ) ≤ x) :
    N ^ (τ / 4) * x ^ ((1 : ℝ) / 2) ≤ N ^ τ * x := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hx
  rw [← Real.sqrt_eq_rpow]
  have hy0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hyy : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  set y := Real.sqrt x with hy
  have h1 : N ^ (-(τ / 2)) ≤ y := by
    have h0 : N ^ (-(τ / 2)) * N ^ (-(τ / 2)) = N ^ (-τ) := by rw [← Real.rpow_add hN0]; congr 1; ring
    by_contra hlt
    rw [not_le] at hlt
    have := mul_self_lt_mul_self hy0.le hlt
    linarith
  have h2 : N ^ (τ / 2) ≤ N ^ τ * y := by
    calc N ^ (τ / 2) = N ^ τ * N ^ (-(τ / 2)) := by rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ N ^ τ * y := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hN0.le _)
  have h3 : N ^ (τ / 4) ≤ N ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  calc N ^ (τ / 4) * y ≤ (N ^ τ * y) * y := mul_le_mul_of_nonneg_right (h3.trans h2) hy0.le
    _ = N ^ τ * x := by rw [mul_assoc, hyy]

/-- The final count: `N^{-D'} + (K + 1) N² N^{-(D + e + 5)} ≤ N^{-D}` for `K = (N + 1)^e`, `N ≥ 2^e + 2`, `D' ≥ D + 3`. -/
theorem GUETwistBA_final_num {N : ℝ} {K e : ℕ} (hK : (K : ℝ) = (N + 1) ^ e) (hN : 2 ^ e + 2 ≤ N) {D D' : ℝ} (hD' : D + 3 ≤ D') :
    N ^ (-D') + ((K : ℝ) + 1) * N ^ 2 * N ^ (-(D + e + 3 + 2)) ≤ N ^ (-D) := by
  have h2e : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : (K : ℝ) + 1 ≤ (2 ^ e + 1) * N ^ e := by
    rw [hK]
    have h : (N + 1) ^ e ≤ (2 * N) ^ e := pow_le_pow_left₀ (by linarith) (by linarith) e
    rw [mul_pow] at h
    have h1e : 1 ≤ N ^ e := one_le_pow₀ hN1
    nlinarith
  have h2 : ((K : ℝ) + 1) * N ^ 2 * N ^ (-(D + e + 3 + 2)) ≤ (2 ^ e + 1) * N ^ (-(D + 3)) := by
    have hpos : 0 ≤ N ^ 2 * N ^ (-(D + e + 3 + 2)) := by positivity
    calc ((K : ℝ) + 1) * N ^ 2 * N ^ (-(D + e + 3 + 2)) = ((K : ℝ) + 1) * (N ^ 2 * N ^ (-(D + e + 3 + 2))) := by ring
      _ ≤ ((2 ^ e + 1) * N ^ e) * (N ^ 2 * N ^ (-(D + e + 3 + 2))) := mul_le_mul_of_nonneg_right h1 hpos
      _ = (2 ^ e + 1) * (N ^ e * (N ^ 2 * N ^ (-(D + e + 3 + 2)))) := by ring
      _ = (2 ^ e + 1) * N ^ (-(D + 3)) := by
          have h : N ^ e * (N ^ 2 * N ^ (-(D + e + 3 + 2))) = N ^ (-(D + 3)) := by
            rw [← Real.rpow_natCast N e, ← Real.rpow_natCast N 2, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
            congr 1; push_cast; ring
          rw [h]
  have h3 : N ^ (-D) = N ^ 3 * N ^ (-(D + 3)) := by
    rw [← Real.rpow_natCast N 3, ← Real.rpow_add hN0]; congr 1; push_cast; ring
  have h4 : N ≤ N ^ 3 := le_self_pow₀ hN1 (by norm_num)
  have h5 : N ^ (-D') ≤ N ^ (-(D + 3)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc N ^ (-D') + ((K : ℝ) + 1) * N ^ 2 * N ^ (-(D + e + 3 + 2)) ≤ N ^ (-(D + 3)) + (2 ^ e + 1) * N ^ (-(D + 3)) := add_le_add h5 h2
    _ = (2 ^ e + 2) * N ^ (-(D + 3)) := by ring
    _ ≤ N ^ 3 * N ^ (-(D + 3)) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN0.le _)
    _ = N ^ (-D) := h3.symm

end Num

section Step

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **One size `n`** (Steps 4-5 of T.7, the union): off the exceptional set `B`, the bad event of `StochDomAt` at `(τ, D)` is contained in the
union over the grid times `j ≤ K n` and the pairs of blocks of `{N^τ Λ_j < |T_{qa}|}` (identity `t_{aq} - M^{(++)}_{aq} = M^{(B)}_{aq} T_{qa}`),
each contained in the trivial regime (`Λ_j ≥ N^{-τ}`, the entrywise local law, `GUETwistBA_Tm_le_entries`) or bounded by `GUETwistBA_time`
(`ε = τ/4`, `ρ² = N^{τ/2}`, `TwistAvgB_expo`); the numeric conditions `hNa`, `hNC`, `hNe`, `hpτ`, `hfin` are discharged eventually in `n`. -/
theorem GUETwistBA_step (sz : Sizes d) (hd : 3 ≤ d) {Λ κ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (n : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    (hg : 0 < g n ∧ g n ≤ Λ) (hr : BAReal d (sz.L n) (g n) κ (E n) (m n)) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (K : ℕ → ℕ) (hK : K n ≠ 0) {p : ℕ} (hp : 1 ≤ p) {τ D D' D₁ CM : ℝ} (hτ : 0 < τ)
    (hCM : CM = (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ))
    (B : Set (PathΩ (sz.withLam 0))) (hBm : MeasurableSet B)
    (hBP : Pgue (sz.withLam 0) B ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D')))
    (hgood : ∀ ω ∉ B, GUETwistBA_Good sz g E t1 t0 m K (τ / 4) n ω)
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (hNa : 2 * (2 * CM + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hNC : ((4 * p + 2) * (2 * CM + 1) + 2) ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ 2)
    (hNe : (CM + 2 * p) * 3 ^ (2 * p + 1) * (((sz.size n : ℕ) : ℝ) ^ (12 * p + 5) * ((sz.size n : ℕ) : ℝ) ^ (-D')) ≤ 1)
    (hpτ : D₁ + 4 ≤ p * τ)
    (hfin : ((sz.size n : ℕ) : ℝ) ^ (-D') + (((K n : ℕ) : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 2)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D)) :
    Pgue (sz.withLam 0) {ω | ∃ u : Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n),
      ((sz.size n : ℕ) : ℝ) ^ τ * (‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) u.2.1 u.2.2‖ *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n u.1))⁻¹) <
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) u.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) u.2.2,
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
            Gres (gueHBA sz g t1 t0 K n u.1 ω) (ztOf (m n) (E n) (gridTime t1 t0 K n u.1)) true y x -
        BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true u.2.1 u.2.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  classical
  subst hCM
  have hτ4 : 0 < τ / 4 := by positivity
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hL3 := sz.three_le_L n
  have hw : ((E n : ℂ) + m n).im ≠ 0 := by
    have : κ ≤ (m n).im := hr.2
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    linarith
  have hη : ∀ j : Fin (K n + 1), 0 < etaOf (m n) (gridTime t1 t0 K n j) ∧ etaOf (m n) (gridTime t1 t0 K n j) ≤ 1 := fun j => by
    have hs := GUETwistBA_gridTime_mem ht10 hK (Nat.lt_succ_iff.1 j.isLt)
    exact GUETwistBA_eta_pos_le hκ hr (ht1.trans hs.1) (hs.2.trans_lt ht0)
  have hΛj0 : ∀ j : Fin (K n + 1), 0 < (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ := fun j => inv_pos.2 (mul_pos hN0 (hη j).1)
  have hΛj_ge : ∀ j : Fin (K n + 1), N⁻¹ ≤ (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ := fun j =>
    inv_anti₀ (mul_pos hN0 (hη j).1) (by nlinarith [(hη j).2])
  set S : Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n) → Set (PathΩ (sz.withLam 0)) := fun u =>
    {ω | (N * etaOf (m n) (gridTime t1 t0 K n u.1))⁻¹ < N ^ (-τ) ∧
      N ^ τ * (N * etaOf (m n) (gridTime t1 t0 K n u.1))⁻¹ <
        ‖GUETwistBA_Tm d (sz.L n) (sz.W n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) u.2.2 u.2.1
          (Gres (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n u.1 ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n u.1)) true)‖} with hSdef
  -- the bad event is contained in `B ∪ ⋃ S`
  have hsub : {ω | ∃ u : Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n),
      N ^ τ * (‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) u.2.1 u.2.2‖ * (N * etaOf (m n) (gridTime t1 t0 K n u.1))⁻¹) <
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) u.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) u.2.2,
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
            Gres (gueHBA sz g t1 t0 K n u.1 ω) (ztOf (m n) (E n) (gridTime t1 t0 K n u.1)) true y x -
        BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true u.2.1 u.2.2‖} ⊆ B ∪ ⋃ u, S u := by
    intro ω hω
    by_cases hωB : ω ∈ B
    · exact Or.inl hωB
    · right
      obtain ⟨⟨j, a, q⟩, hlt⟩ := hω
      refine Set.mem_iUnion.2 ⟨(j, a, q), ?_⟩
      have hid := GUETwistBA_ident (d := d) (L := sz.L n) (W := sz.W n) (g n) (E n : ℂ) (m n) hw
        (Gres (gueHBA sz g t1 t0 K n j ω) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) true) a q
      have hGb : blockMat d (sz.L n) (sz.W n) (Gres (gueHBA sz g t1 t0 K n j ω) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) true) =
          Gres (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) true :=
        (ExpAvgGen_Gres_blockMat _ _).symm
      rw [hGb] at hid
      simp only at hlt
      rw [hid, norm_mul] at hlt
      have hTlt : N ^ τ * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ <
          ‖GUETwistBA_Tm d (sz.L n) (sz.W n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) q a
            (Gres (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) true)‖ := by
        refine lt_of_mul_lt_mul_left (a := ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a q‖) ?_ (norm_nonneg _)
        calc ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a q‖ * (N ^ τ * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) =
              N ^ τ * (‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a q‖ * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) := by ring
          _ < _ := hlt
      refine ⟨?_, hTlt⟩
      by_contra hA
      rw [not_lt] at hA
      have hG := (hgood ω hωB j).2.2
      have hb := GUETwistBA_Tm_le_entries (d := d) (L := sz.L n) (W := sz.W n) (g n) (E n : ℂ) (m n) hw
        (Gres (gueHBA sz g t1 t0 K n j ω) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) true) q a
        (b := N ^ (τ / 4) * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ ((1 : ℝ) / 2))
        (fun x y => by rw [GUETwistBA_Gres_true]; exact hG x y)
      rw [hGb] at hb
      exact absurd (hTlt.trans_le hb) (not_lt.2 (GUETwistBA_triv hN1 hτ hA))
  have hCM0 : 0 ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (baM_row_l1 (by omega) hL3 Λ (g n) κ (E n) (m n) hΛ hg.1 hg.2 hκ hr (0 : Zd d (sz.L n)))
  have hδ : (Pgue (sz.withLam 0)).real B ≤ N ^ (-D') := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) hBP
  have hρ2 : (N ^ (τ / 4)) ^ 2 = N ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hNτ0 : 0 < N ^ τ := Real.rpow_pos_of_pos hN0 _
  have hNτ2 : 0 < N ^ (τ / 2) := Real.rpow_pos_of_pos hN0 _
  have hC' : 0 < (4 * (p : ℝ) + 2) * (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) + 2 := by positivity
  -- the per-index bound
  have hS : ∀ u : Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n),
      Pgue (sz.withLam 0) (S u) ≤ ENNReal.ofReal (N ^ (-(D₁ + 2))) := by
    rintro ⟨j, a, q⟩
    by_cases hB : (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ < N ^ (-τ)
    · have hx0 : 0 < (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ := hΛj0 j
      have hx1 : (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ≤ 1 :=
        hB.le.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
      have hρ : 1 ≤ N ^ (τ / 4) := Real.one_le_rpow hN1 hτ4.le
      have ha : (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) * (N ^ (τ / 4)) ^ 2 *
          (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ≤ 1 / 2 := by
        rw [hρ2]
        have h1 : N ^ (τ / 2) * N ^ (-τ) = (N ^ (τ / 2))⁻¹ := by
          rw [← Real.rpow_add hN0, show τ / 2 + -τ = -(τ / 2) by ring, Real.rpow_neg hN0.le]
        calc (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) * N ^ (τ / 2) * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ≤
              (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) * N ^ (τ / 2) * N ^ (-τ) :=
              mul_le_mul_of_nonneg_left hB.le (mul_nonneg (by linarith) hNτ2.le)
          _ = (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) * (N ^ (τ / 2))⁻¹ := by rw [mul_assoc, h1]
          _ ≤ 1 / 2 := by rw [← div_eq_mul_inv, div_le_iff₀ hNτ2]; linarith
      have he : (((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 2 * p) *
          (2 * N ^ 2 * (N * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ 3 + 1) ^ (2 * p + 1) * N ^ (-D') ≤
          ((N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ (2 * p) := by
        have hxN := hΛj_ge j
        have h1 : 2 * N ^ 2 * (N * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ 3 + 1 ≤ 3 * N ^ 5 := by
          have hNx : N * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ≤ N := by nlinarith
          have h3 : (N * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by positivity) hNx 3
          have h5 : 1 ≤ N ^ 5 := one_le_pow₀ hN1
          have h6 : N ^ 2 * N ^ 3 = N ^ 5 := by ring
          nlinarith [pow_pos hN0 2, mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * N ^ 2)]
        have h2 : (2 * N ^ 2 * (N * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ 3 + 1) ^ (2 * p + 1) ≤ (3 * N ^ 5) ^ (2 * p + 1) :=
          pow_le_pow_left₀ (by positivity) h1 _
        have h3 : (3 * N ^ 5) ^ (2 * p + 1) = 3 ^ (2 * p + 1) * N ^ (10 * p + 5) := by
          rw [mul_pow, ← pow_mul]; congr 2; ring
        have h4 : (N⁻¹) ^ (2 * p) ≤ ((N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ (2 * p) := pow_le_pow_left₀ (by positivity) hxN _
        have hδ0 : 0 ≤ N ^ (-D') := Real.rpow_nonneg hN0.le _
        have hc0 : 0 ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) + 2 * p := by positivity
        refine le_trans ?_ h4
        calc ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) + 2 * p) *
              (2 * N ^ 2 * (N * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) ^ 3 + 1) ^ (2 * p + 1) * N ^ (-D') ≤
              ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) + 2 * p) * (3 ^ (2 * p + 1) * N ^ (10 * p + 5)) * N ^ (-D') := by
              rw [← h3]; gcongr
          _ ≤ (N⁻¹) ^ (2 * p) := by
              rw [inv_pow, ← one_div (N ^ (2 * p)), le_div_iff₀ (pow_pos hN0 _)]
              calc ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) + 2 * p) * (3 ^ (2 * p + 1) * N ^ (10 * p + 5)) * N ^ (-D') * N ^ (2 * p) =
                    ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) + 2 * p) * 3 ^ (2 * p + 1) * (N ^ (12 * p + 5) * N ^ (-D')) := by
                      rw [show 12 * p + 5 = (10 * p + 5) + 2 * p by ring, pow_add]; ring
                _ ≤ 1 := hNe
      have hT := GUETwistBA_time sz hd hκ hΛ n hg hr ht1 ht10 ht0 K hK j hp B hBm hδ hgood hx1 hρ ha he
        (s := N ^ τ * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) (mul_pos hNτ0 hx0) q a
      refine le_trans (measure_mono ?_) (hT.trans (ENNReal.ofReal_le_ofReal ?_))
      · intro ω hω; exact hω.2
      · have hq : ((4 * (p : ℝ) + 2) * (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) + 2) *
            ((N ^ (τ / 4)) ^ 2 * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) / (N ^ τ * (N * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) =
            ((4 * (p : ℝ) + 2) * (2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 1) + 2) * (N ^ (τ / 4)) ^ 2 / N ^ τ := by
          rw [← mul_assoc]; exact mul_div_mul_right _ _ hx0.ne'
        rw [hq]
        exact TwistAvgB_expo hN1 (by positivity) hC' (by rw [hρ2]) hpτ hNC
    · have : S (j, a, q) = ∅ := Set.eq_empty_of_forall_notMem fun ω hω => hB hω.1
      rw [this, measure_empty]; exact zero_le
  have hcard : (Fintype.card (Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) ≤ ((K n : ℝ) + 1) * N ^ 2 := by
    have h := Nat.cast_le (α := ℝ) |>.2 (GUETwistBA_card_idx sz n (K n))
    refine h.trans (le_of_eq ?_)
    rw [hNdef]; push_cast; ring
  calc Pgue (sz.withLam 0) _ ≤ Pgue (sz.withLam 0) (B ∪ ⋃ u, S u) := measure_mono hsub
    _ ≤ Pgue (sz.withLam 0) B + Pgue (sz.withLam 0) (⋃ u, S u) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (N ^ (-D')) + ENNReal.ofReal ((Fintype.card (Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) *
          N ^ (-(D₁ + 2))) := add_le_add hBP (TwistAvgB_union _ S hS)
    _ = ENNReal.ofReal (N ^ (-D') + (Fintype.card (Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) * N ^ (-(D₁ + 2))) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _))).symm
    _ ≤ ENNReal.ofReal (N ^ (-D)) :=
        ENNReal.ofReal_le_ofReal ((add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _))).trans hfin)

end Step

section Main

open scoped Matrix.Norms.L2Operator

/-- The numeric condition `hNe` of `GUETwistBA_step` for `D' = D + 12 p + 7`: `c N^{12p+5} N^{-D'} = c N^{-(D+2)} ≤ 1` once `c ≤ N`. -/
theorem GUETwistBA_hNe {N c D : ℝ} {p : ℕ} (hN : 1 ≤ N) (hc : c ≤ N) (hD : 0 ≤ D) :
    c * (N ^ (12 * p + 5) * N ^ (-(D + 12 * p + 7))) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ (12 * p + 5) * N ^ (-(D + 12 * p + 7)) = (N ^ (D + 2))⁻¹ := by
    rw [← Real.rpow_natCast N (12 * p + 5), ← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]; congr 1; push_cast; ring
  have h2 : N ≤ N ^ (D + 2) := Real.self_le_rpow_of_one_le hN (by linarith)
  have h3 : 0 < N ^ (D + 2) := Real.rpow_pos_of_pos hN0 _
  rw [h1]
  calc c * (N ^ (D + 2))⁻¹ ≤ N ^ (D + 2) * (N ^ (D + 2))⁻¹ := mul_le_mul_of_nonneg_right (hc.trans h2) (inv_nonneg.2 h3.le)
    _ = 1 := mul_inv_cancel₀ h3.ne'

/-- **Target 7, `gueGrid_twistBA`** (text `T2519_HoffBA` of the probe `t/T2519` b992c2e7:`RBM3D/Probe/T2519Pins.lean:79-98`, with
`GUEPathBoundsBA` in place of `T2519_PathBoundsBA`): the twisted 1-loop law on the GUE-phase grid at block Anderson (the `hoff` premise
of `gueGrid_expect_oneLoopBA` at `K = gueGridK sz n0`, `n0 ≥ 4`).  For `d ≥ 3` and the grid `gueHBA` at the grid times, given PB
(`GUEPathBoundsBA`: loops of length `≤ n0`, `localLaw`) against a primitive family `Kt` with `Kt = m` on 1-loops and the K-bound,
`|⟨M G⟩_{aa'}-block twisted trace - M^{(++)}_{aa'}| ≺ |M^{(B)}_{aa'}| (N η_u)⁻¹` simultaneously in the grid times `u` and the pairs of blocks.
The proof is Lemma T.7 (`docs/tickets/T2398-TL-proofs.md:64-78`) at the one-time law of the grid: `GUETwistBA_momentId` (Steps 1-2),
`GUETwistBA_RB1`/`_RB2` (Step 3), `GUETwistBA_good` (the PB interface), `GUETwistBA_time` (Steps 4-5: recursion, bootstrap, Markov),
`GUETwistBA_step` (the union and the trivial regime). -/
theorem gueGrid_twistBA (d : ℕ) : 3 ≤ d → ∀ (sz : Sizes d) (κ Λ : ℝ), 0 < κ → 0 < Λ →
    ∀ (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (n0 : ℕ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ),
    Tendsto (fun n => sz.size n) atTop atTop → 4 ≤ n0 →
    (∀ᶠ n in atTop, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
    (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) →
    (∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ) →
    (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)),
      I.WF → 2 ≤ I.length → I.length ≤ 4 →
      ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1)) →
    GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz n0) n0 Kt →
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ω =>
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) p.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p.2.2,
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
              Gres (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω)
                (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) true y x -
          BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true p.2.1 p.2.2‖)
      (fun n p _ => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) p.2.1 p.2.2‖ *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹) := by
  intro hd sz κ Λ hκ hΛ g E t1 t0 m n0 Kt hsize hn0 hlam hr ht1 ht10 ht0 hKm hKb hPB τ hτ D hD
  classical
  obtain ⟨CM, hCMdef⟩ : ∃ CM : ℝ, CM = (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈(D + ((32 * n0 + 64 : ℕ) : ℝ) + 3 + 4) / τ⌉₊ := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hpdef]; exact Nat.ceil_pos.2 (by positivity)
  have hpτ : D + ((32 * n0 + 64 : ℕ) : ℝ) + 3 + 4 ≤ (p : ℝ) * τ := by
    have h := Nat.le_ceil ((D + ((32 * n0 + 64 : ℕ) : ℝ) + 3 + 4) / τ)
    rw [← hpdef, div_le_iff₀ hτ] at h
    exact h
  have hgood := GUETwistBA_good sz hsize hn0 hPB hKm hKb
    (fun n k hk => GUETwistBA_gridTime_mem (ht10 n) (gueGridK_ne_zero sz n0 n) hk) (ε := τ / 4) (D := D + 12 * p + 7)
    (by positivity) (by positivity)
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_iff.mpr hsize
  have hNa : ∀ᶠ n in atTop, 2 * (2 * CM + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp hsz).eventually (eventually_ge_atTop _)
  have hbig := hsz.eventually (eventually_ge_atTop (max (max 1 (((4 * (p : ℝ) + 2) * (2 * CM + 1) + 2) ^ (2 * p)))
    (max ((CM + 2 * p) * 3 ^ (2 * p + 1)) (2 ^ (32 * n0 + 64) + 2))))
  filter_upwards [hgood, hlam, hNa, hbig] with n hgn hlamn hNan hbn
  obtain ⟨B, hBm, hBP, hBgood⟩ := hgn hlamn.1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hb1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hbn)
  have hbC : ((4 * (p : ℝ) + 2) * (2 * CM + 1) + 2) ^ (2 * p) ≤ N :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hbn)
  have hbe : (CM + 2 * p) * 3 ^ (2 * p + 1) ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hbn)
  have hb2 : 2 ^ (32 * n0 + 64) + 2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hbn)
  have hK : ((gueGridK sz n0 n : ℕ) : ℝ) = (N + 1) ^ (32 * n0 + 64) := by
    unfold gueGridK; push_cast; rfl
  exact GUETwistBA_step sz hd hκ hΛ n hlamn (hr n) (ht1 n) (ht10 n) (ht0 n) (gueGridK sz n0) (gueGridK_ne_zero sz n0 n) hp1 hτ hCMdef
    B hBm hBP hBgood hb1 hNan (hbC.trans (by nlinarith)) (GUETwistBA_hNe hb1 hbe hD.le) hpτ
    (GUETwistBA_final_num hK hb2 (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]))

end Main

/-! ## 5. Compiled nonempty instance (target 7) of `gueGrid_twistBA`

Namespace `RBM.BA.GUETwistBAInst`.  Data: `d = 3`, `sz0` (`L_n = 4 (n + 1)`, `W_n = (2 (n + 1))^5`, `N_0 = 2^21`, `Defs/Sizes.lean`), the BA flow
datum `(g_n, E_n, m_n)` of `sz0` at every `n` (`BAReal` at `κ = 1/2`, `0 < g_n ≤ 10` eventually: `BAflow_lam0_window`), the GUE-phase
window `1 - t₀ = x_n = λ_n² / (4 L_n³)`, `t₀ - t₁ = x_n / (2 N_n)` (row a's window, `GUEHypABA` §3), `n₀ = 4` (the grid `gueGridK sz0 4`),
`Kt` the BA primitive family of `gueK_existsBA` (chosen per `n`, loops of length `≤ 4 * 4`).  Every deterministic hypothesis is discharged,
including `Kt = m` on the 1-loops (`GUETwistBA_Kt_one`); PB (`GUEPathBoundsBA`, the output of the §7.2 random layer, another gate) and the
K-bound stay as hypotheses of the instance.  The K-bound is the conclusion of `Hyp_Kt_detDomBA` (row a, `τ_U = 1/20`, `n₀ = 4`, cut from
`≤ 2 * 4` to `≤ 4`); its deterministic premises `h730` and `hell` are checked at this data (`GUETwistBAInst_h730`, `GUETwistBAInst_hell`). -/

section KtOne

variable {d : ℕ}

/-- `K̃ = m_σ` on the 1-loops from the initial value `BAKsol` at `t₁` (`baKsol_one`) and the ODE `primRhsGUE` (zero right side at length 1;
twin of `Hyp_Kt_one`, `GUEPhase/HypA:712`; probe `t/T2519` b992c2e7, `probe_Kt_one`). -/
theorem GUETwistBA_Kt_one (sz : Sizes d) {κ : ℝ} (hκ : 0 < κ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    {Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ}
    (hKinit : ∀ n, 0 < g n → ∀ I, Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n)
      (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n))) (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * 4 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s)
    (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) :
    ∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ := by
  intro n hg u hu σ a
  have hI : (⟨[σ], [a]⟩ : LoopIdx (Zd d (sz.L n))).length = 1 := rfl
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r => Kt n r ⟨[σ], [a]⟩)
    (f' := fun r => primRhsGUE d (sz.L n) (sz.W n) (Kt n r) ⟨[σ], [a]⟩) (C := 0)
    (fun r hr' => hK n hg r hr' _ rfl (by rw [hI]) (by rw [hI]; omega))
    (fun r _ => by rw [Hyp_primRhs_one _ _ hI, norm_zero]) u hu
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hmvt
  have h1 := baKsol_one d hκ hg (sz.three_le_L n) (sz.W n) (hr n) (t := t1 n)
    ⟨ht1 n, lt_of_le_of_lt (ht10 n) (ht0 n)⟩ (fun _ : Fin 1 => σ) (fun _ => a)
  have hloop : KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => a) = ⟨[σ], [a]⟩ := by simp [KLloopOf, List.ofFn_succ]
  rw [hloop] at h1
  rw [hmvt, hKinit n hg, h1]
  rfl

end KtOne

namespace GUETwistBAInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- The flow datum of `sz0` (`BAflowLam0`, `BAflowEs`, `BAmF`) and the GUE-phase window `1 - t₀ = x_n`, `t₀ - t₁ = x_n / (2 N_n)`,
`x_n = λ_n² / (4 L_n³)` (row a's window, `GUEHypABA` §3). -/
abbrev gI : ℕ → ℝ := BAflowLam0 sz0 zSeq
abbrev EI : ℕ → ℝ := BAflowEs sz0 zSeq
abbrev mI : ℕ → ℂ := BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)
private abbrev NI (n : ℕ) : ℝ := ((sz0.size n : ℕ) : ℝ)
private abbrev xI (n : ℕ) : ℝ := sz0.lam n ^ 2 / (4 * ((sz0.L n : ℕ) : ℝ) ^ 3)
abbrev t0I (n : ℕ) : ℝ := 1 - xI n
abbrev t1I (n : ℕ) : ℝ := t0I n - xI n / (2 * NI n)

theorem real_I (n : ℕ) : BAReal 3 (sz0.L n) (gI n) (1 / 2) (EI n) (mI n) :=
  BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n

private theorem GUETwistBAInst_L (n : ℕ) : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
  change (4 : ℝ) ≤ ((4 * (n + 1) : ℕ) : ℝ)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem GUETwistBAInst_N (n : ℕ) : (1 : ℝ) ≤ NI n :=
  le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (size_ge n)

private theorem GUETwistBAInst_x_pos (n : ℕ) : 0 < xI n := by
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) := by linarith [GUETwistBAInst_L n]
  have := sz0_lam_pos n
  unfold xI; positivity

private theorem GUETwistBAInst_x_le (n : ℕ) : xI n ≤ 1 / 4 := by
  have hL : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := GUETwistBAInst_L n
  have h1 := sz0_lam_L n
  have h3 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hcast : ((((sz0.L n) ^ 3 : ℕ) : ℝ)) = ((sz0.L n : ℕ) : ℝ) ^ 3 := by push_cast; ring
  rw [hcast] at h1
  have h2 : sz0.lam n ^ 2 ≤ 1 / 64 := by nlinarith [sq_nonneg (sz0.lam n)]
  unfold xI
  rw [div_le_iff₀ (by positivity)]
  nlinarith

private theorem GUETwistBAInst_t0 (n : ℕ) : 1 / 4 ≤ BAflowT0 sz0 zSeq n := by
  have h1 := mS_im_half (sz0.L n) (sz0.lam n) (sz0_lam_L n)
  have h2 := zSeq_im_le n
  have h3 := zSeq_im_pos n
  unfold BAflowT0 BAt0
  rw [BAm_zSeq n, le_div_iff₀ (by linarith)]
  linarith

private theorem GUETwistBAInst_t1_nonneg (n : ℕ) : 0 ≤ t1I n := by
  have h1 := GUETwistBAInst_x_le n
  have h2 := GUETwistBAInst_x_pos n
  have hN := GUETwistBAInst_N n
  have : xI n / (2 * NI n) ≤ xI n := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  unfold t1I t0I; linarith

private theorem GUETwistBAInst_t10 (n : ℕ) : t1I n ≤ t0I n := by
  have h2 := GUETwistBAInst_x_pos n
  have hN := GUETwistBAInst_N n
  have : 0 ≤ xI n / (2 * NI n) := by positivity
  unfold t1I; linarith

private theorem GUETwistBAInst_t0_lt (n : ℕ) : t0I n < 1 := by
  have := GUETwistBAInst_x_pos n; unfold t0I; linarith

/-- `g_n > 0` at every `n` (`g_n = √t₀ λ_n`, `0 < t₀`). -/
private theorem GUETwistBAInst_g_pos (n : ℕ) : 0 < gI n := by
  have hm : 0 < (BAm 3 (sz0.L n) (sz0.lam n) (zSeq n)).im := by
    rw [BAm_zSeq n]; linarith [mS_im_half (sz0.L n) (sz0.lam n) (sz0_lam_L n)]
  exact mul_pos (Real.sqrt_pos.mpr (BAt0_pos (zSeq_im_pos n) hm)) (sz0_lam_pos n)

/-- `hell` of `Hyp_Kt_detDomBA` at the instance: `L_n³ (1 - t₁) ≤ 2 g_n²` (port of `GUEHypABAInst_hell`, row a `BA/GUEHypABA.lean`). -/
private theorem GUETwistBAInst_hell :
    ∀ᶠ n : ℕ in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - t1I n) ≤ 2 * gI n ^ 2 := by
  refine Eventually.of_forall fun n => ?_
  have hx := GUETwistBAInst_x_pos n
  have hN := GUETwistBAInst_N n
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) ^ 3 := by have := GUETwistBAInst_L n; positivity
  have hg2 : gI n ^ 2 = BAflowT0 sz0 zSeq n * sz0.lam n ^ 2 := by
    unfold gI BAflowLam0
    rw [mul_pow, Real.sq_sqrt]
    have := GUETwistBAInst_t0 n
    linarith
  have hxN : xI n / (2 * NI n) ≤ xI n := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h1 : 1 - t1I n ≤ 2 * xI n := by unfold t1I t0I; linarith
  have hL0 : ((sz0.L n : ℕ) : ℝ) ≠ 0 := by have := GUETwistBAInst_L n; intro h; linarith
  have h2 : ((sz0.L n : ℕ) : ℝ) ^ 3 * xI n = sz0.lam n ^ 2 / 4 := by
    unfold xI; field_simp
  have h3 := GUETwistBAInst_t0 n
  calc ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - t1I n) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 * (2 * xI n) :=
        mul_le_mul_of_nonneg_left h1 hL.le
    _ = sz0.lam n ^ 2 / 2 := by rw [← mul_assoc, mul_comm _ 2, mul_assoc, h2]; ring
    _ ≤ 2 * gI n ^ 2 := by rw [hg2]; nlinarith [sq_nonneg (sz0.lam n)]

/-- `h730` of `Hyp_Kt_detDomBA` at the instance, `τ_U = 1/20`: `t₀ - t₁ ≤ N^{-1/20} η_{t₀}` (port of `GUEHypABAInst_h730`, row a
`BA/GUEHypABA.lean`). -/
private theorem GUETwistBAInst_h730 :
    ∀ᶠ n : ℕ in atTop, t0I n - t1I n ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)) * etaOf (mI n) (t0I n) := by
  refine Eventually.of_forall fun n => ?_
  have hx := GUETwistBAInst_x_pos n
  have hN := GUETwistBAInst_N n
  have hm := (real_I n).2
  have hpow : NI n ^ (-1 : ℝ) ≤ NI n ^ (-(1 / 20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  rw [Real.rpow_neg_one] at hpow
  have heta : etaOf (mI n) (t0I n) = xI n * (mI n).im := by unfold etaOf t0I; ring
  have h1 : t0I n - t1I n = xI n / (2 * NI n) := by unfold t1I; ring
  change t0I n - t1I n ≤ NI n ^ (-(1 / 20 : ℝ)) * etaOf (mI n) (t0I n)
  rw [h1, heta]
  have hN0 : 0 < NI n := by linarith
  calc xI n / (2 * NI n) = (NI n)⁻¹ * (xI n * (1 / 2)) := by field_simp
    _ ≤ NI n ^ (-(1 / 20 : ℝ)) * (xI n * (mI n).im) := by
        apply mul_le_mul hpow (mul_le_mul_of_nonneg_left hm hx.le) (by positivity) (by positivity)

/-- The BA primitive family of the instance: `gueK_existsBA` at the flow datum and the window, loops of length `≤ 4 * 4`, chosen per `n`. -/
def KtI (n : ℕ) : ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ :=
  Classical.choose (gueK_existsBA 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) (GUETwistBAInst_g_pos n)
    (show (0 : ℝ) < 1 / 2 by norm_num) (real_I n) (GUETwistBAInst_t1_nonneg n) (GUETwistBAInst_t10 n) (GUETwistBAInst_t0_lt n) (4 * 4))

/-- The clauses of the primitive family `KtI` (`gueK_existsBA`): the initial value `BAKsol` at `t₁` and the ODE `primRhsGUE`. -/
private theorem GUETwistBAInst_KtI_spec (n : ℕ) :
    (∀ I, KtI n (t1I n) I = BAKsol 3 (sz0.L n) (sz0.W n) (BAMsigma 3 (sz0.L n) (BAMB 3 (sz0.L n) (gI n) (EI n : ℂ) (mI n)))
      (PropSpin (mI n)) (t1I n) I) ∧
    (∀ s ∈ Set.Icc (t1I n) (t0I n), ∀ I : LoopIdx (Zd 3 (sz0.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * 4 →
      HasDerivWithinAt (fun u => KtI n u I) (primRhsGUE 3 (sz0.L n) (sz0.W n) (KtI n s) I) (Set.Icc (t1I n) (t0I n)) s) :=
  (Classical.choose_spec (gueK_existsBA 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) (GUETwistBAInst_g_pos n)
    (show (0 : ℝ) < 1 / 2 by norm_num) (real_I n) (GUETwistBAInst_t1_nonneg n) (GUETwistBAInst_t10 n) (GUETwistBAInst_t0_lt n) (4 * 4))).imp
    (fun h => h) (fun h => h.1)

/-- **`gueGrid_twistBA` at the instance** (`d = 3`, `sz0`, the BA flow datum, the GUE-phase window `1 - t₀ = x_n`, `t₀ - t₁ = x_n / (2 N_n)`,
`n₀ = 4`, `Kt = KtI`): every deterministic hypothesis is discharged (`Tendsto size` from `sz0_tendsto`, `4 ≤ n₀`, `0 < g_n ≤ 10` eventually from
`BAflow_lam0_window`, `BAReal` at `κ = 1/2` for every `n`, the window, and `Kt = m` on the 1-loops from the clauses of `gueK_existsBA`); PB and
the K-bound stay as hypotheses (the K-bound is `Hyp_Kt_detDomBA`'s conclusion, whose premises `h730`, `hell` hold here). -/
theorem twist_sz0
    (hKb : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1I n) (t0I n), ∀ I : LoopIdx (Zd 3 (sz0.L n)),
      I.WF → 2 ≤ I.length → I.length ≤ 4 →
      ‖KtI n s I‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ ε * (((sz0.size n : ℕ) : ℝ) * etaOf (mI n) s)⁻¹ ^ (I.length - 1))
    (hPB : GUEPathBoundsBA sz0 gI EI t1I t0I mI (gueGridK sz0 4) 4 KtI) :
    StochDomAt (Pgue (sz0.withLam 0)) sz0.size
      (fun n (p : Fin (gueGridK sz0 4 n + 1) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) ω =>
        ‖(((sz0.W n : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (sz0.L n) (sz0.W n) p.2.1, ∑ y ∈ Iblk 3 (sz0.L n) (sz0.W n) p.2.2,
            Mres (((gI n : ℝ) : ℂ) • PsiI 3 (sz0.L n) (sz0.W n)) (EI n : ℂ) (mI n) x y *
              Gres (gueHBA sz0 gI t1I t0I (gueGridK sz0 4) n p.1 ω)
                (ztOf (mI n) (EI n) (gridTime t1I t0I (gueGridK sz0 4) n p.1)) true y x -
          BAMss 3 (sz0.L n) (BAMB 3 (sz0.L n) (gI n) (EI n : ℂ) (mI n)) true true p.2.1 p.2.2‖)
      (fun n p _ => ‖BAMB 3 (sz0.L n) (gI n) (EI n : ℂ) (mI n) p.2.1 p.2.2‖ *
        (((sz0.size n : ℕ) : ℝ) * etaOf (mI n) (gridTime t1I t0I (gueGridK sz0 4) n p.1))⁻¹) :=
  gueGrid_twistBA 3 le_rfl sz0 (1 / 2) ((1 / 10 : ℝ)⁻¹) (by norm_num) (by norm_num) gI EI t1I t0I mI 4 KtI
    (tendsto_natCast_atTop_iff.mp sz0_tendsto) le_rfl (BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0) real_I
    GUETwistBAInst_t1_nonneg GUETwistBAInst_t10 GUETwistBAInst_t0_lt
    (GUETwistBA_Kt_one sz0 (by norm_num) (fun n _ I => (GUETwistBAInst_KtI_spec n).1 I)
      (fun n _ s hs I hI h1 h2 => (GUETwistBAInst_KtI_spec n).2 s hs I hI h1 h2) real_I
      GUETwistBAInst_t1_nonneg GUETwistBAInst_t10 GUETwistBAInst_t0_lt)
    hKb hPB

end GUETwistBAInst

end RBM.BA

end
