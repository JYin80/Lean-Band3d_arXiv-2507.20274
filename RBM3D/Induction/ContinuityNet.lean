/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.FlowCalculus
import RBM3D.Gauss.Domination
import RBM3D.Defs.StochDomAt
import RBM3D.Green.EntryCore
import Mathlib.Probability.Moments.SubGaussian

/-!
# Continuity of the Green function in time, part 1: the net lift and its deterministic inputs
(ST-1, ticket S1-33 = T2047)

Port of the first part (lines 1-764) of `RBM2D/Induction/Continuity.lean` at commit `c9a24cf`
(cited `Continuity:line`), onto the merged MD layer and the merged ST-1 files.  The cut is the
section boundary before `## 4. Deterministic estimates along the flow` (`Continuity:765`); the
second part (S1-34: `Flow`, `Ratio2`, `Close`, `Main`: `cont_entry_diff` ... `gopbound`,
`Step1NetLift`, `step1NetLift`) imports this file.

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L` becomes
`Zd d L`, `Idx L W` becomes `Idx d L W`, `W^2`, `(W L)^2` become `W^d`, `(W L)^d = sz.size n`,
`Coord`, `svar`, `P` become `CoordF`, `svarF`, `PF`, `spectralM`, `spectralZ` become `mE`, `zt`,
`Gsig` is `Gres`, `BlockIndex` is `Vtx`, `Xmat`, `Hflow`, `blockMat` carry `d`.  The `d = 2` scales
`scaleM`, `ellT` of `Continuity:604-694` do not exist in the `d ≥ 3` vocabulary: the controls of
`STStep1Loop`, `STStep1Weak` are `((1-s)/(1-u))^{k-1} (W^{-d} B_{s,0})^{k-1}` and
`(W^{-d} B_{u,0})^{1/4}` (`Sizes.Bctl`), and section 4 states the scalar facts about `Bctl` that
replace `cont_scaleM_*`, `cont_ellT_diff`: the lower bound `N^{-1} ≤ Bctl n s`
(`cont_inv_size_le_Bctl`), the ratio of `Bctl` at two times (`cont_Bctl_ratio`) and the ratio of
`(γ + 1 - u)⁻¹` (`cont_inv_add_one_sub_ratio`, which also gives `(1-s)/(1-u')` against
`(1-s)/(1-u)`).  Section 5 holds the compiled instances at the merged size data `sz0` (`d = 3`).

Every public declaration of this file lives in `RBM.Ind.ContinuityNet` (the file stem), except the
pin `RBM.Ind.GopboundPin`.  What S1-34 uses is public; helpers that no later ticket needs are
`private`.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

set_option linter.style.longLine false

/-! ## 0. The pin -/

/-- **Pin (`Gopboundu`, 5-6:13-16 of the `d = 2` paper; no statement in the `d ≥ 3` paper, paper-delta
T2015e)**: for every `C > 0` there is `C' > 0` such that, for every `D > 0`, eventually, outside an
event of probability `≤ N^{-D}`, `max_{0 ≤ u,u' ≤ 1 - N^{-1}, |u-u'| ≤ N^{-C'}} ‖G_u - G_{u'}‖_max ≤
N^{-C}`, at the energy `E n`; `N = sz.size n = (W L)^d`.  `RBM2D/Induction/Continuity.lean:65`
(`GopboundPin`), rule R1; `0 < κ →` is the RBM2D insertion (paper-delta candidate `T2070a` there). -/
def GopboundPin {d : ℕ} (sz : Sizes d) (κ : ℝ) (E : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → sz.SizeTendsto →
  ∀ C > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    sz.seqP {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
        u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
        |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
        ∃ i j : Idx d (sz.L n) (sz.W n),
          ((sz.size n : ℕ) : ℝ) ^ (-C) <
            ‖(sz.seqHflow n u ω - zt (E n) u • 1)⁻¹ i j -
              (sz.seqHflow n u' ω - zt (E n) u' • 1)⁻¹ i j‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

namespace ContinuityNet

/-! ## 1. The abstract net lift -/

section Core

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Continuity:85` (`cont_stochDomAt_of_subset`). -/
private theorem cont_stochDomAt_of_subset {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U V : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ' ζ' : ∀ l, V l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (h : StochDomAt P size ξ' ζ') (hΞ : HighProbAt P size Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ∩ Ξ l ⊆ badSetAt size ξ' ζ' τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' (D + 1) (by linarith), hΞ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcover : badSetAt size ξ ζ τ l ⊆ (badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ := by
    intro ω hω
    by_cases hΞω : ω ∈ Ξ l
    · exact Or.inl ⟨hω, hΞω⟩
    · exact Or.inr hΞω
  calc P (badSetAt size ξ ζ τ l) ≤ P ((badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ) :=
        measure_mono hcover
    _ ≤ P (badSetAt size ξ ζ τ l ∩ Ξ l) + P (Ξ l)ᶜ := measure_union_le _ _
    _ ≤ P (badSetAt size ξ' ζ' τ' l) + P (Ξ l)ᶜ := add_le_add (measure_mono h0) le_rfl
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- The clamped net of `[s n, t n]` at scale `size^{-A-1}` (port of RBM1D `netTime_mem`,
`Gauss/DominationHolder.lean:151`, and `exists_netTime_close`, `:158`, commit `86573b9`).
`Continuity:114` (`contTime`). -/
private def contTime (s t : ℕ → ℝ) (A : ℝ) (N n : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t n) (s n + netPt 1 A N k)

/-- `Continuity:117` (`contTime_mem`). -/
private theorem contTime_mem {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (A : ℝ) (N n : ℕ)
    (k : Fin (netSize A N + 1)) : contTime s t A N n k ∈ Set.Icc (s n) (t n) := by
  refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc zero_le_one A N k).1
  linarith

/-- `Continuity:123` (`cont_exists_close`). -/
private theorem cont_exists_close {s t : ℕ → ℝ} (hlen : ∀ n, t n - s n ≤ 1) (A : ℝ) (N n : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (s n) (t n)) :
    ∃ k, |u - contTime s t A N n k| ≤ 1 / (netSize A N : ℝ) := by
  have hmem : u - s n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen n]⟩
  obtain ⟨k, hk⟩ := exists_netPt_close one_pos A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s n + netPt 1 A N k)| ≤ 1 / (netSize A N : ℝ) := by
    have h : u - (s n + netPt 1 A N k) = u - s n - netPt 1 A N k := by ring
    rw [h]; exact hk
  unfold contTime
  rcases le_or_gt (s n + netPt 1 A N k) (t n) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

/-- **The abstract net lift** (port of RBM1D `netLift_of_relaxed`, `Gauss/Step1Hyp.lean:404`, and
`stochDom_of_subset_highProb`, `Gauss/DominationHolder.lean:115`, commit `86573b9`).
A per-time domination on `TimeIcc s t n × V n`, a polynomial bound
on `#V n`, a good event `Ξ` of high probability on which `ξ` moves by at most `ε n` and `ζ`
by a factor `2` under a time change of size `size^{-A}`, and the lower bound `ε ≤ ζ`, give the
uniform domination.  `Continuity:147` (`cont_core`); the scale `size` is arbitrary, nothing in the
statement depends on the dimension. -/
theorem cont_core {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop)
    {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (hlen : ∀ n, t n - s n ≤ 1)
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    {ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ} {A Cv : ℝ} (hA : 0 ≤ A) (hCv : 0 ≤ Cv)
    (hcard : ∀ᶠ n : ℕ in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ Cv)
    (hpt : PerTimeDomAt P size ξ ζ) {Ξ : ℕ → Set Ω} (hΞ : HighProbAt P size Ξ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hlow : ∀ᶠ n : ℕ in atTop, ∀ (p : TimeIcc s t n × V n) (ω : Ω), ε n ≤ ζ n p ω)
    (hclose : ∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ (size n : ℝ) ^ (-A) → ∀ v : V n,
        ξ n (u, v) ω ≤ ξ n (u', v) ω + ε n ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) :
    StochDomAt P size ξ ζ := by
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
  let θ : ∀ n, Fin (netSize (A + 1) (size n) + 1) → TimeIcc s t n := fun n k =>
    ⟨contTime s t (A + 1) (size n) n k, contTime_mem hst _ _ n k⟩
  let ξ' : ∀ n, (Fin (netSize (A + 1) (size n) + 1) × V n) → Ω → ℝ :=
    fun n p ω => ξ n (θ n p.1, p.2) ω
  let ζ' : ∀ n, (Fin (netSize (A + 1) (size n) + 1) × V n) → Ω → ℝ :=
    fun n p ω => ζ n (θ n p.1, p.2) ω
  have hpt' : PerTimeDomAt P size ξ' ζ' := by
    intro τ hτ D hD
    filter_upwards [hpt τ hτ D hD] with l hl p
    exact hl (θ l p.1, p.2)
  have hcard' : ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Fin (netSize (A + 1) (size n) + 1) × V n) : ℝ) ≤
        (size n : ℝ) ^ (A + 1 + 1 + Cv) := by
    filter_upwards [hcard, hsize.eventually (card_net_le hA1),
      hsize.eventually (eventually_ge_atTop 1)] with n h1 h2 h3
    have hpos : (0 : ℝ) < (size n : ℝ) := by exact_mod_cast h3
    rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_add hpos]
    exact mul_le_mul h2 h1 (Nat.cast_nonneg _) (Real.rpow_nonneg hpos.le _)
  have hnet : StochDomAt P size ξ' ζ' :=
    stochDomAt_of_perTimeDomAt P size (C := A + 1 + 1 + Cv) (by linarith) hcard' hpt'
  refine cont_stochDomAt_of_subset hsize hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hclose, hlow, hsize.eventually (eventually_ge_atTop 2),
    hsize.eventually (eventually_le_rpow 3 hτ2)] with n hcloseN hlowN hN2 hN3
  rintro ω ⟨⟨⟨u, v⟩, hbad⟩, hωΞ⟩
  have hN2' : (2 : ℝ) ≤ (size n : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (size n : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (netSize (A + 1) (size n) : ℝ) := by
    exact_mod_cast netSize_pos (A + 1) (size n)
  have hmge : (size n : ℝ) ^ (A + 1) ≤ (netSize (A + 1) (size n) : ℝ) :=
    rpow_le_netSize _ _
  have hNA1 : (0 : ℝ) < (size n : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos hNpos _
  obtain ⟨k, hk⟩ := cont_exists_close hlen (A + 1) (size n) n u.2
  have hdist : |(u : ℝ) - ((θ n k : TimeIcc s t n) : ℝ)| ≤ (size n : ℝ) ^ (-A) := by
    refine hk.trans ?_
    have h1 : 1 / (netSize (A + 1) (size n) : ℝ) ≤ 1 / (size n : ℝ) ^ (A + 1) := by
      gcongr
    refine h1.trans ?_
    rw [div_le_iff₀ hNA1]
    have hmul : (size n : ℝ) ^ (-A) * (size n : ℝ) ^ (A + 1) = (size n : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    rw [hmul, Real.rpow_one]
    linarith
  obtain ⟨hξ, hζ⟩ := hcloseN ω hωΞ u (θ n k) hdist v
  have hzlow : ε n ≤ ζ n (u, v) ω := hlowN (u, v) ω
  have hε0 := hε n
  have hz0 : (0 : ℝ) ≤ ζ n (u, v) ω := le_trans hε0 hzlow
  have hhalf : (size n : ℝ) ^ (τ / 2) * (size n : ℝ) ^ (τ / 2) = (size n : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hbig : (0 : ℝ) ≤ (size n : ℝ) ^ τ - 2 * (size n : ℝ) ^ (τ / 2) - 1 := by
    nlinarith [hhalf, hN3]
  have hprod : (0 : ℝ) ≤ ((size n : ℝ) ^ τ - 2 * (size n : ℝ) ^ (τ / 2) - 1) * ζ n (u, v) ω :=
    mul_nonneg hbig hz0
  have hhalf0 : (0 : ℝ) ≤ (size n : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hz'le : (size n : ℝ) ^ (τ / 2) * ζ n (θ n k, v) ω ≤
      (size n : ℝ) ^ (τ / 2) * (2 * ζ n (u, v) ω) :=
    mul_le_mul_of_nonneg_left hζ hhalf0
  refine ⟨(k, v), ?_⟩
  change (size n : ℝ) ^ (τ / 2) * ζ n (θ n k, v) ω < ξ n (θ n k, v) ω
  nlinarith [hbad, hξ, hprod, hzlow, hz'le]

end Core

/-! ## 2. The good event: every Gaussian coordinate is at most `N` -/

section Good

/-- The good event at size index `n`: every real Gaussian coordinate of size `n` is at most
`size n` in absolute value.  `Continuity:230` (`contGood`), rule R4 (`Coord` is `CoordF`). -/
def contGood {d : ℕ} (sz : Sizes d) (n : ℕ) : Set sz.SeqΩ :=
  {ω | ∀ c : CoordF d (sz.L n) (sz.W n), |ω ⟨n, c⟩| ≤ ((sz.size n : ℕ) : ℝ)}

/-- Every coordinate has variance at most `1`: `S_xy = W^{-d} S^{(B)}_{ab}` with `S^{(B)}` a
stochastic kernel (`sum_SBR_row`, `L ≥ 3`) and `W ≥ 1`.  `Continuity:233` (`cont_seqGvar_le_one`);
RBM2D bounds the five-point profile by cases, here the row sum `1` bounds every entry, and no
hypothesis on the coupling `sz.lam n` is needed. -/
private theorem cont_seqGvar_le_one {d : ℕ} (sz : Sizes d) (c : sz.SeqCoord) :
    (sz.seqGvar c : ℝ) ≤ 1 := by
  obtain ⟨n, i, j, b⟩ := c
  have hW : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
  have hs : svarF d (sz.L n) (sz.W n) (sz.lam n) i j ≤ 1 := by
    unfold svarF
    have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW)
    have h0 : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    have hS : SBR d (sz.L n) (sz.lam n) (split d (sz.L n) (sz.W n) i).1
        (split d (sz.L n) (sz.W n) j).1 ≤ 1 := by
      have h := sum_sbKernelR d (sz.L n) (sz.lam n) (sz.three_le_L n)
      have h' : sbKernelR d (sz.L n) (sz.lam n)
          ((split d (sz.L n) (sz.W n) i).1 - (split d (sz.L n) (sz.W n) j).1) ≤ 1 := by
        rw [← h]
        exact Finset.single_le_sum (f := sbKernelR d (sz.L n) (sz.lam n))
          (fun x _ => sbKernelR_nonneg d (sz.L n) (sz.lam n) x) (Finset.mem_univ _)
      simpa [SBR] using h'
    have hS0 : (0 : ℝ) ≤ SBR d (sz.L n) (sz.lam n) (split d (sz.L n) (sz.W n) i).1
        (split d (sz.L n) (sz.W n) j).1 := by
      simpa [SBR] using sbKernelR_nonneg d (sz.L n) (sz.lam n) _
    nlinarith
  have h0 := svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) i j
  change (if i = j then svarF d (sz.L n) (sz.W n) (sz.lam n) i j
    else svarF d (sz.L n) (sz.W n) (sz.lam n) i j / 2) ≤ 1
  split_ifs <;> linarith

/-- The Gaussian tail of one coordinate: `P(|Z| ≥ B) ≤ 2 exp(-B²/2)` (variance at most `1`).
`Continuity:249` (`cont_coord_tail`). -/
private theorem cont_coord_tail {d : ℕ} (sz : Sizes d) (c : sz.SeqCoord) {B : ℝ} (hB : 0 ≤ B) :
    sz.seqP {ω | B < |ω c|} ≤ ENNReal.ofReal (2 * Real.exp (-B ^ 2 / 2)) := by
  have hmeas : Measurable (fun ω : sz.SeqΩ => ω c) := measurable_pi_apply c
  have hsg : HasSubgaussianMGF (fun ω : sz.SeqΩ => ω c) 1 sz.seqP := by
    rw [← HasSubgaussianMGF.id_map_iff hmeas.aemeasurable, Sizes.seqP_map_eval]
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
    rw [mgf_id_gaussianReal]
    apply Real.exp_le_exp.2
    have h1 := cont_seqGvar_le_one sz c
    have h2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    simp only [NNReal.coe_one, zero_mul, zero_add]
    nlinarith
  have h1 := hsg.measure_ge_le hB
  have h2 := hsg.neg.measure_ge_le hB
  simp only [NNReal.coe_one, mul_one] at h1 h2
  have hsub : {ω : sz.SeqΩ | B < |ω c|} ⊆
      {ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : sz.SeqΩ => ω c)) ω} := by
    intro ω hω
    have hω' : B < |ω c| := hω
    rcases le_abs.1 (le_of_lt hω') with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hf1 : sz.seqP {ω | B ≤ ω c} ≤ ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h1
  have hf2 : sz.seqP {ω | B ≤ (-(fun ω : sz.SeqΩ => ω c)) ω} ≤
      ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h2
  have hp : (0 : ℝ) ≤ Real.exp (-B ^ 2 / 2) := (Real.exp_pos _).le
  calc sz.seqP {ω | B < |ω c|}
      ≤ sz.seqP ({ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : sz.SeqΩ => ω c)) ω}) :=
        measure_mono hsub
    _ ≤ sz.seqP {ω | B ≤ ω c} + sz.seqP {ω | B ≤ (-(fun ω : sz.SeqΩ => ω c)) ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-B ^ 2 / 2)) :=
        add_le_add hf1 hf2
    _ = ENNReal.ofReal (2 * Real.exp (-B ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf

/-- The number of real coordinates at size `n` is `2 N²` (`N = (W L)^d = #Idx`).
`Continuity:292` (`cont_card_coord`), with `cont_card_Z2` replaced by the merged `Sizes.card_Idx`
(`#Z_{WL}^d = (W L)^d`). -/
private theorem cont_card_coord {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (Fintype.card (CoordF d (sz.L n) (sz.W n)) : ℝ) = 2 * ((sz.size n : ℕ) : ℝ) ^ 2 := by
  have h : Fintype.card (CoordF d (sz.L n) (sz.W n)) =
      Fintype.card (Idx d (sz.L n) (sz.W n)) * (Fintype.card (Idx d (sz.L n) (sz.W n)) * 2) := by
    simp [CoordF, Fintype.card_prod, Fintype.card_bool]
  rw [h]
  push_cast
  rw [sz.card_Idx n]; ring

/-- `P(Ξ_nᶜ) ≤ 4 N² e^{-N²/2}`.  `Continuity:305` (`cont_good_compl`). -/
theorem cont_good_compl {d : ℕ} (sz : Sizes d) (n : ℕ) :
    sz.seqP (contGood sz n)ᶜ ≤
      ENNReal.ofReal (2 * ((sz.size n : ℕ) : ℝ) ^ 2 *
        (2 * Real.exp (-((sz.size n : ℕ) : ℝ) ^ 2 / 2))) := by
  have hB : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsub : (contGood sz n)ᶜ ⊆
      ⋃ c : CoordF d (sz.L n) (sz.W n),
        {ω : sz.SeqΩ | ((sz.size n : ℕ) : ℝ) < |ω ⟨n, c⟩|} := by
    intro ω hω
    simp only [contGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨c, hc⟩ := hω
    exact Set.mem_iUnion.2 ⟨c, hc⟩
  calc sz.seqP (contGood sz n)ᶜ
      ≤ sz.seqP (⋃ c : CoordF d (sz.L n) (sz.W n),
          {ω : sz.SeqΩ | ((sz.size n : ℕ) : ℝ) < |ω ⟨n, c⟩|}) := measure_mono hsub
    _ ≤ ∑ c : CoordF d (sz.L n) (sz.W n),
          sz.seqP {ω : sz.SeqΩ | ((sz.size n : ℕ) : ℝ) < |ω ⟨n, c⟩|} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c : CoordF d (sz.L n) (sz.W n),
          ENNReal.ofReal (2 * Real.exp (-((sz.size n : ℕ) : ℝ) ^ 2 / 2)) :=
        Finset.sum_le_sum fun c _ => cont_coord_tail sz ⟨n, c⟩ hB
    _ = ENNReal.ofReal (Fintype.card (CoordF d (sz.L n) (sz.W n)) *
          (2 * Real.exp (-((sz.size n : ℕ) : ℝ) ^ 2 / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (2 * ((sz.size n : ℕ) : ℝ) ^ 2 *
          (2 * Real.exp (-((sz.size n : ℕ) : ℝ) ^ 2 / 2))) := by
        rw [cont_card_coord]

/-- `4 x² exp(-x²/2) ≤ x^{-D}` for large `x`.  `Continuity:334` (`cont_eventually_tail`). -/
theorem cont_eventually_tail (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, 2 * x ^ 2 * (2 * Real.exp (-x ^ 2 / 2)) ≤ x ^ (-D) := by
  have h1 : Tendsto (fun x : ℝ => x ^ (D + 2) * Real.exp (-(1 / 2) * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D + 2) (1 / 2) (by norm_num)
  filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hexp : Real.exp (-x ^ 2 / 2) ≤ Real.exp (-(1 / 2) * x) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hxD : 0 < x ^ (-D) := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ (D + 2) * x ^ (-D) = x ^ 2 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have h2 : x ^ 2 * Real.exp (-(1 / 2) * x) < x ^ (-D) / 4 := by
    have := mul_lt_mul_of_pos_right hx hxD
    rw [← hsplit]
    nlinarith [this]
  calc 2 * x ^ 2 * (2 * Real.exp (-x ^ 2 / 2))
      = 4 * (x ^ 2 * Real.exp (-x ^ 2 / 2)) := by ring
    _ ≤ 4 * (x ^ 2 * Real.exp (-(1 / 2) * x)) := by
        gcongr
    _ ≤ x ^ (-D) := by linarith

/-- The good event `Ξ_n` holds w.h.p. at the scale `N = (W L)^d`.  `Continuity:358`
(`cont_highProbAt_good`). -/
theorem cont_highProbAt_good {d : ℕ} (sz : Sizes d) (hsize : Tendsto sz.size atTop atTop) :
    HighProbAt sz.seqP sz.size (contGood sz) := by
  intro D hD
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  filter_upwards [hcast.eventually (cont_eventually_tail D)] with n hn
  exact (cont_good_compl sz n).trans (ENNReal.ofReal_le_ofReal hn)

end Good

/-! ## 3. Deterministic estimates in the `L²` operator norm -/

section Resolvent

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Port of RBM1D `l2_opNorm_sq_le_frobSq` (`Gauss/OpNorm.lean:107`, commit `86573b9`):
`‖A‖² ≤ ∑ |A_ij|²`.  `Continuity:378` (`cont_opNorm_sq_le_frob`). -/
private theorem cont_opNorm_sq_le_frob (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  set F : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2 with hF
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hbd : ‖A‖ ≤ Real.sqrt F := by
    rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hsq : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x‖ ^ 2 ≤ F * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, hF, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hrow : ‖((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x).ofLp i‖
          ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hrow 2) ?_
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    nlinarith [Real.sq_sqrt hF0, norm_nonneg ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) x),
      norm_nonneg x, Real.sqrt_nonneg F, mul_nonneg (Real.sqrt_nonneg F) (norm_nonneg x)]
  nlinarith [Real.sq_sqrt hF0, norm_nonneg A, Real.sqrt_nonneg F]

/-- `‖A‖ ≤ (#n) B` for a matrix with entries bounded by `B`.  `Continuity:399`
(`cont_norm_le_card_mul`). -/
theorem cont_norm_le_card_mul (A : Matrix n n ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A‖ ≤ (Fintype.card n : ℝ) * B := by
  have h1 : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : n, ∑ _j : n, B ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  have h2 : ∑ _i : n, ∑ _j : n, B ^ 2 = ((Fintype.card n : ℝ) * B) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    ((cont_opNorm_sq_le_frob A).trans (h1.trans h2.le))

/-- `‖1‖ ≤ 1`.  `Continuity:410` (`cont_norm_one_le`). -/
theorem cont_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

/-- The merged `Gres H z +` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹` (RBM2D's `Gsig H z +`
is `green H z`, `Hierarchy/Loops.lean:48`). -/
theorem cont_Gres_true_eq_green (H : Matrix n n ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- The merged `Gres H z -` is `RBM.green H z̄ = (H - z̄)⁻¹`. -/
theorem cont_Gres_false_eq_green (H : Matrix n n ℂ) (z : ℂ) :
    Gres H z false = green H ((starRingEnd ℂ) z) := by
  simp only [green, Gres, Bool.false_eq_true, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- `‖(H - z)⁻¹‖ ≤ η⁻¹` for `H` Hermitian and `η ≤ |Im z|`: the merged
`norm_Gsig_le_inv_eta` (`Gauss/FlowCalculus.lean:644`) read for `RBM.green`; RBM2D
`norm_green_le` (`Gauss/Envelope.lean:116`). -/
theorem cont_norm_green_le {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) : ‖green H z‖ ≤ η⁻¹ := by
  have h := norm_Gsig_le_inv_eta hH hη hz true
  rw [cont_Gres_true_eq_green] at h
  exact h

/-- The two-matrix resolvent estimate.  `Continuity:415` (`cont_green_diff`). -/
theorem cont_green_diff {H H' : Matrix n n ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    (hz' : η ≤ |z'.im|) :
    ‖green H z - green H' z'‖ ≤ η⁻¹ * η⁻¹ * (‖H - H'‖ + ‖z - z'‖) := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hzim' : z'.im ≠ 0 := fun h => absurd hz' (by rw [h]; simpa using hη)
  have hA := isUnit_sub_smul_of_isHermitian hH hzim
  have hB := isUnit_sub_smul_of_isHermitian hH' hzim'
  have hA' : green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hB' : (H' - z' • (1 : Matrix n n ℂ)) * green H' z' = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB)
  have hid : green H z - green H' z' =
      green H z * ((H' - H) - (z' - z) • (1 : Matrix n n ℂ)) * green H' z' := by
    calc green H z - green H' z'
        = green H z * ((H' - z' • (1 : Matrix n n ℂ)) * green H' z') -
            (green H z * (H - z • (1 : Matrix n n ℂ))) * green H' z' := by
          rw [hA', hB']; simp
      _ = green H z * ((H' - z' • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ))) *
            green H' z' := by noncomm_ring
      _ = _ := by
          congr 2
          module
  have hG := cont_norm_green_le hH hη hz
  have hG' := cont_norm_green_le hH' hη hz'
  have hmid : ‖(H' - H) - (z' - z) • (1 : Matrix n n ℂ)‖ ≤ ‖H - H'‖ + ‖z - z'‖ := by
    calc ‖(H' - H) - (z' - z) • (1 : Matrix n n ℂ)‖
        ≤ ‖H' - H‖ + ‖(z' - z) • (1 : Matrix n n ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖H - H'‖ + ‖z - z'‖ := by
          rw [norm_sub_rev H' H]
          refine add_le_add le_rfl ?_
          rw [norm_smul, norm_sub_rev z' z]
          exact mul_le_of_le_one_right (norm_nonneg _) cont_norm_one_le
  rw [hid]
  calc ‖green H z * ((H' - H) - (z' - z) • (1 : Matrix n n ℂ)) * green H' z'‖
      ≤ ‖green H z‖ * ‖(H' - H) - (z' - z) • (1 : Matrix n n ℂ)‖ * ‖green H' z'‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ η⁻¹ * (‖H - H'‖ + ‖z - z'‖) * η⁻¹ := by
        gcongr
    _ = η⁻¹ * η⁻¹ * (‖H - H'‖ + ‖z - z'‖) := by ring

end Resolvent

section Modulus

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Port of RBM1D `abs_sqrt_sub_sqrt_le` (`Gauss/FlowHolder.lean:95`, commit `86573b9`).
`Continuity:465` (`cont_abs_sqrt_sub_sqrt_le`). -/
theorem cont_abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  rcases le_total y x with h | h
  · have hs : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt h
    rw [abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (sub_nonneg.2 h)]
    have key : (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x - y := by
      have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
      have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
      have hxy : Real.sqrt y * Real.sqrt y ≤ Real.sqrt x * Real.sqrt y :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg y)
      nlinarith [hxx, hyy, hxy]
    have h2 := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (sub_nonneg.2 hs)] at h2
  · have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt h
    rw [abs_sub_comm, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (sub_nonneg.2 h)]
    have key : (Real.sqrt y - Real.sqrt x) ^ 2 ≤ y - x := by
      have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
      have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
      have hxy : Real.sqrt x * Real.sqrt x ≤ Real.sqrt y * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
      nlinarith [hxx, hyy, hxy]
    have h2 := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (sub_nonneg.2 hs)] at h2

/-- An entry of `X` is at most `2B` when every real coordinate is at most `B`.
`Continuity:490` (`cont_norm_Xentry_le`). -/
theorem cont_norm_Xentry_le (ω : Ω d L W) {B : ℝ} (h : ∀ c, |ω c| ≤ B)
    (i j : Idx d L W) : ‖Xentry d L W ω i j‖ ≤ 2 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (h (i, j, true))
  unfold Xentry
  split_ifs
  · calc ‖((ω (i, j, true) : ℝ) : ℂ) + Complex.I * ((ω (i, j, false) : ℝ) : ℂ)‖
        ≤ ‖((ω (i, j, true) : ℝ) : ℂ)‖ + ‖Complex.I * ((ω (i, j, false) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ 2 * B := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
          linarith [h (i, j, true), h (i, j, false)]
  · calc ‖((ω (j, i, true) : ℝ) : ℂ) - Complex.I * ((ω (j, i, false) : ℝ) : ℂ)‖
        ≤ ‖((ω (j, i, true) : ℝ) : ℂ)‖ + ‖Complex.I * ((ω (j, i, false) : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * B := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
          linarith [h (j, i, true), h (j, i, false)]
  · rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [h (i, j, true)]

/-- On `Ξ`, `‖X‖ ≤ #Idx · 2B`.  `Continuity:512` (`cont_norm_Xmat_le`). -/
theorem cont_norm_Xmat_le (ω : Ω d L W) {B : ℝ} (h : ∀ c, |ω c| ≤ B) :
    ‖Xmat d L W ω‖ ≤ (Fintype.card (Idx d L W) : ℝ) * (2 * B) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (h (0, 0, true))
  exact cont_norm_le_card_mul _ (by positivity) fun i j => cont_norm_Xentry_le ω h i j

/-- On `Ξ`, `‖X‖ ≤ #Vtx · 2B` for the block-product reading of `X` (`blockMat`).
`Continuity:517` (`cont_norm_blockMat_Xmat_le`), `BlockIndex` is `Vtx`. -/
theorem cont_norm_blockMat_Xmat_le (ω : Ω d L W) {B : ℝ} (h : ∀ c, |ω c| ≤ B) :
    ‖blockMat d L W (Xmat d L W ω)‖ ≤ (Fintype.card (Vtx d L W) : ℝ) * (2 * B) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (h (0, 0, true))
  exact cont_norm_le_card_mul _ (by positivity) fun p q =>
    cont_norm_Xentry_le ω h _ _

/-- `Continuity:523` (`cont_blockMat_sub`). -/
theorem cont_blockMat_sub (M M' : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockMat d L W (M - M') = blockMat d L W M - blockMat d L W M' := by
  ext p q; simp [blockMat]

/-- `Continuity:527` (`cont_blockMat_smul`). -/
theorem cont_blockMat_smul (c : ℂ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockMat d L W (c • M) = c • blockMat d L W M := by
  ext p q; simp [blockMat]

end Modulus

section GreenFlow

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent modulus along the flow: `H - H' = c X`, `|c| ≤ √Δ`, `‖X‖ ≤ Xb`, `‖z - z'‖ ≤ Δ`,
`Δ ≤ 1`, `η⁻¹ ≤ Q`.  `Continuity:541` (`cont_green_flow_diff`). -/
theorem cont_green_flow_diff {H H' X : Matrix n n ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X) {Xb Δ : ℝ} (hX : ‖X‖ ≤ Xb)
    (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) {z z' : ℂ} {η Q : ℝ} (hη : 0 < η)
    (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ) :
    ‖green H z - green H' z'‖ ≤ Q * Q * (Xb + 1) * Real.sqrt Δ := by
  have h1 := cont_green_diff hH hH' hη hz hz'
  have hQ0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hX0 : 0 ≤ Xb := (norm_nonneg _).trans hX
  have hΔs : Δ ≤ Real.sqrt Δ := by
    calc Δ = Real.sqrt Δ * Real.sqrt Δ := (Real.mul_self_sqrt hΔ0).symm
      _ ≤ Real.sqrt Δ * 1 := by
          gcongr
          rw [Real.sqrt_le_one]; exact hΔ1
      _ = Real.sqrt Δ := mul_one _
  have hHH : ‖H - H'‖ ≤ Real.sqrt Δ * Xb := by
    rw [hd, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hc hX (norm_nonneg _) (Real.sqrt_nonneg _)
  have h2 : η⁻¹ * η⁻¹ ≤ Q * Q := mul_le_mul hQ hQ hQ0 (hQ0.trans hQ)
  calc ‖green H z - green H' z'‖ ≤ η⁻¹ * η⁻¹ * (‖H - H'‖ + ‖z - z'‖) := h1
    _ ≤ Q * Q * (Real.sqrt Δ * Xb + Real.sqrt Δ) := by
        refine mul_le_mul h2 ?_ (by positivity) (mul_self_nonneg _)
        linarith
    _ = Q * Q * (Xb + 1) * Real.sqrt Δ := by ring

end GreenFlow

section Spectral

/-- `‖m‖ = 1` and `Im m ≤ 1`.  `Continuity:570` (`cont_im_m_le_one`); `spectralM` is `mE`. -/
theorem cont_im_m_le_one {E : ℝ} (hE : |E| ≤ 2) : (mE E).im ≤ 1 := by
  have h := Complex.abs_im_le_norm (mE E)
  rw [norm_mE hE] at h
  exact (le_abs_self _).trans h

/-- `η_t ≤ |Im z_u|` for `u ≤ t < 1`.  `Continuity:575` (`cont_eta_le_abs_im`); `spectralZ` is
`zt`, `etaT` the merged `Gauss.etaT`. -/
theorem cont_eta_le_abs_im {E t u : ℝ} (hE : |E| < 2) (ht : t < 1) (hut : u ≤ t) :
    etaT E t ≤ |(zt E u).im| := by
  have hm := mE_im_pos hE
  rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) hm.le)]
  unfold etaT
  exact mul_le_mul_of_nonneg_right (by linarith) hm.le

/-- `‖z_u - z_{u'}‖ = |u - u'|`.  `Continuity:582` (`cont_norm_spectralZ_sub`). -/
theorem cont_norm_spectralZ_sub {E : ℝ} (hE : |E| ≤ 2) (u u' : ℝ) :
    ‖zt E u - zt E u'‖ = |u - u'| := by
  have h : zt E u - zt E u' = ((u' - u : ℝ) : ℂ) * mE E := by
    unfold zt; push_cast; ring
  rw [h, norm_mul, norm_mE hE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

/-- `Im m ≥ 0` (the 2D `cont_spectralM_im_nonneg`, `Continuity:614`). -/
theorem cont_spectralM_im_nonneg (E : ℝ) : 0 ≤ (mE E).im := by
  rw [mE_im]; positivity

end Spectral

section EblkNorm

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L]

/-- `‖E_a‖ ≤ W^{-d} ≤ 1`.  `Continuity:596` (`cont_norm_Eblk_le_one`), rule R3: the merged
`norm_Eblk_le_inv_W_sq` has `(W^d)⁻¹`, RBM2D's `W⁻²`. -/
theorem cont_norm_Eblk_le_one (hW : 1 ≤ W) (c : Zd d L) : ‖Eblk d L W c‖ ≤ 1 := by
  refine (norm_Eblk_le_inv_W_sq d L W c).trans ?_
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hW))

end EblkNorm

/-! ## 4. Scalar estimates for the controls

The `d = 2` controls `scaleM L W E u = Im m · min (W², N (1-u))` and `ℓ_u` of `Continuity:604-694`
(`cont_scaleM_diff`, `cont_im_le_scaleM`, `cont_scaleM_le`, `cont_one_div_sqrt_diff`,
`cont_ellT_diff`) do not exist at `d ≥ 3`.  The controls of the Step 1 families are
`((1-s)/(1-u))^{k-1} (W^{-d} B_{s,0})^{k-1}` (`STStep1Loop`) and `(W^{-d} B_{u,0})^{1/4}`
(`STStep1Weak`), `W^{-d} B_{u,0} = Sizes.Bctl` (`1_2:1107`), whose only dependence on the time is
through `1 - u` in two explicit terms.  What the net lift needs of them is (i) the lower bound
`N^{-1} ≤ Bctl n s` (`0 ≤ s < 1`; it replaces `cont_scaleM_le`, `M ≤ N`), (ii) the ratio of the
controls at two times `u, u' ≤ t < 1` (it replaces `cont_scaleM_diff`, `cont_ellT_diff`): all of
them are re-derived here for `Bctl` and are new text, not renamings. -/

section Ratio

/-- `b⁻¹ ≤ κ a⁻¹` from `a ≤ κ b` (positive `a, b`); RBM1D `inv_le_const_mul_inv_of_le_const_mul`
(`Gauss/GridNetLift.lean:127`, commit `86573b9`).  `Continuity:700` (`cont_inv_le_const_mul_inv`). -/
theorem cont_inv_le_const_mul_inv {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ κ * b) : b⁻¹ ≤ κ * a⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hb ha]
  nlinarith [h]

/-- The ratio of `(γ + 1 - u)⁻¹` at two times `u, u' ≤ t < 1` (`γ ≥ 0`): both are at least
`1 - t`, so a time change `|u - u'|` costs the factor `1 + (1-t)⁻¹ |u - u'|`.  New at `d ≥ 3`
(replaces `Continuity:933` `cont_scaleM_ratio`). -/
theorem cont_inv_add_one_sub_ratio {γ t u u' : ℝ} (hγ : 0 ≤ γ) (ht : t < 1) (hut : u ≤ t)
    (hu't : u' ≤ t) :
    (γ + (1 - u))⁻¹ ≤ (1 + (1 - t)⁻¹ * |u - u'|) * (γ + (1 - u'))⁻¹ := by
  have h1t : 0 < 1 - t := by linarith
  have ha : 0 < γ + (1 - u) := by linarith
  have ha' : 0 < γ + (1 - u') := by linarith
  refine cont_inv_le_const_mul_inv (a := γ + (1 - u')) (b := γ + (1 - u)) ha' ha ?_
  have hc : 1 ≤ (1 - t)⁻¹ * (γ + (1 - u)) := by
    calc (1 : ℝ) = (1 - t)⁻¹ * (1 - t) := (inv_mul_cancel₀ h1t.ne').symm
      _ ≤ (1 - t)⁻¹ * (γ + (1 - u)) :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 h1t.le)
  nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (u - u')), le_abs_self (u - u')]

/-- `W^{-d} B_{u,0} = W^{-d} [(ĝ² + 1 - u)⁻¹ + (L^d (1-u))⁻¹]` for `u < 1` (`(eq_B_param)`,
`1_2:1107`, `K = 0`). -/
theorem cont_Bctl_eq {d : ℕ} (sz : Sizes d) (n : ℕ) {t : ℝ} (ht : t < 1) :
    sz.Bctl n t = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      ((sz.lam n ^ 2 + (1 - t))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹) := by
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos (by linarith : 0 < 1 - t)]
  simp

/-- **Lower bound of the control**: `N^{-1} ≤ W^{-d} B_{s,0}` for `0 ≤ s < 1` (the zero-mode term
`W^{-d} (L^d (1-s))⁻¹ ≥ (W L)^{-d}`).  New at `d ≥ 3`; replaces `Continuity:640` `cont_scaleM_le`
(`M_u ≤ N`) in `cont_LP_low`, `cont_WL_low` of the second part. -/
theorem cont_inv_size_le_Bctl {d : ℕ} (sz : Sizes d) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n s := by
  rw [cont_Bctl_eq sz n hs1]
  have hx : 0 < 1 - s := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith)
  have h2 : (0 : ℝ) ≤ (sz.lam n ^ 2 + (1 - s))⁻¹ := by
    have : 0 < sz.lam n ^ 2 + (1 - s) := by positivity
    positivity
  rw [hsize, mul_inv]
  exact mul_le_mul_of_nonneg_left (h1.trans (le_add_of_nonneg_left h2))
    (inv_nonneg.2 hWd.le)

/-- **Ratio of the controls at two times**: `W^{-d} B_{u,0} ≤ (1 + (1-t)⁻¹ |u-u'|) W^{-d} B_{u',0}`
for `u, u' ≤ t < 1` (each of the two terms of `B` is a ratio of the type
`cont_inv_add_one_sub_ratio`).  New at `d ≥ 3`; with `(1-t)⁻¹ ≤ N` it gives `1 + N |u-u'|`, the
analogue of `Continuity:933` `cont_scaleM_ratio` for `STStep1Weak`. -/
theorem cont_Bctl_ratio {d : ℕ} (sz : Sizes d) (n : ℕ) {t u u' : ℝ} (ht : t < 1) (hut : u ≤ t)
    (hu't : u' ≤ t) :
    sz.Bctl n u ≤ (1 + (1 - t)⁻¹ * |u - u'|) * sz.Bctl n u' := by
  have hu : u < 1 := by linarith
  have hu' : u' < 1 := by linarith
  rw [cont_Bctl_eq sz n hu, cont_Bctl_eq sz n hu']
  have hA := cont_inv_add_one_sub_ratio (γ := sz.lam n ^ 2) (sq_nonneg _) ht hut hu't
  have hB := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hut hu't
  have hLi : (0 : ℝ) ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hWi : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hBe : ∀ v : ℝ, (((sz.L n : ℕ) : ℝ) ^ d * (1 - v))⁻¹ =
      (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - v))⁻¹ := by
    intro v; rw [zero_add, mul_inv]
  rw [hBe u, hBe u']
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ +
        (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 + (1 - t)⁻¹ * |u - u'|) * (sz.lam n ^ 2 + (1 - u'))⁻¹ +
        (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ((1 + (1 - t)⁻¹ * |u - u'|) * (0 + (1 - u'))⁻¹)) := by
        gcongr
    _ = (1 + (1 - t)⁻¹ * |u - u'|) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        ((sz.lam n ^ 2 + (1 - u'))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - u'))⁻¹)) := by
        ring

end Ratio

section Analytic

/-- Port of RBM1D `sqrt_rpow_eq` (`Gauss/GridNetLift.lean:122`, commit `86573b9`):
`√(N^e) = N^{e/2}`.  `Continuity:711` (`cont_sqrt_rpow`). -/
theorem cont_sqrt_rpow {N : ℝ} (hN : 0 ≤ N) (e : ℝ) :
    Real.sqrt (N ^ e) = N ^ (e / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN]
  ring_nf

/-- Port of RBM1D `sqrt_abs_sub_le_rpow` (`Gauss/GridNetLift.lean:48`, commit `86573b9`).
`Continuity:717` (`cont_sqrt_abs_le`). -/
theorem cont_sqrt_abs_le {N Δ A : ℝ} (hN : 0 ≤ N) (h : Δ ≤ N ^ (-A)) :
    Real.sqrt Δ ≤ N ^ (-A / 2) := by
  rw [← cont_sqrt_rpow hN]
  exact Real.sqrt_le_sqrt h

end Analytic

section Bulk

/-- The bulk constant: `|E| ≤ 2 - κ` gives `Im m ≥ √(2κ)/2 > 0`.  `Continuity:727` (`cont_bulk`);
`spectralM` is `mE`, `spectralM_im` is `mE_im`. -/
theorem cont_bulk {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    |E| < 2 ∧ Real.sqrt (2 * κ) / 2 ≤ (mE E).im := by
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hκ2 : κ ≤ 2 := by linarith
  refine ⟨by linarith, ?_⟩
  rw [mE_im]
  have h1 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ hE0 hE 2
  have h2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

end Bulk

section Assembly

/-- `C x^p ≤ κ x^q` eventually along `size → ∞`, for `p < q`.  `Continuity:745` (`cont_gap`). -/
theorem cont_gap {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) (C : ℝ) {κ p q : ℝ}
    (hκ : 0 < κ) (hpq : p < q) :
    ∀ᶠ n : ℕ in atTop, C * ((size n : ℕ) : ℝ) ^ p ≤ κ * ((size n : ℕ) : ℝ) ^ q := by
  filter_upwards [hsize.eventually (eventually_le_rpow (C / κ) (sub_pos.2 hpq)),
    hsize.eventually (eventually_ge_atTop 1)] with n h1 h2
  have hx : (0 : ℝ) < ((size n : ℕ) : ℝ) := by exact_mod_cast h2
  have h3 : C / κ * ((size n : ℕ) : ℝ) ^ p ≤ ((size n : ℕ) : ℝ) ^ (q - p) * ((size n : ℕ) : ℝ) ^ p :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx.le _)
  rw [← Real.rpow_add hx, sub_add_cancel] at h3
  have h4 : C * ((size n : ℕ) : ℝ) ^ p = κ * (C / κ * ((size n : ℕ) : ℝ) ^ p) := by
    field_simp
  rw [h4]
  exact mul_le_mul_of_nonneg_left h3 hκ.le

/-- `x^k x^e = x^{k+e}`.  `Continuity:759` (`cont_pow_mul_rpow`). -/
theorem cont_pow_mul_rpow {x : ℝ} (hx : 0 < x) (k : ℕ) (e : ℝ) :
    x ^ k * x ^ e = x ^ ((k : ℝ) + e) := by
  rw [Real.rpow_add hx, Real.rpow_natCast]

end Assembly

/-! ## 5. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), `SizeTendsto` by `sz0_tendsto`; `κ = 1/10`, `E ≡ 1/2`.  The sample is
the all-ones sample `ω₁` (`|ω₁ c| = 1 ≤ N`, so `ω₁ ∈ contGood sz0 0`).  The only hypothesis of an
instance that is not discharged is `GopboundPin sz0 κ E` itself (S1-34 proves it as `gopbound`) and,
for `cont_core`, the per-time domination `PerTimeDomAt` of the family (another gate's pin). -/

section Instances

open RBM.Gauss.SizesInst

private theorem contInst_hsize : Tendsto sz0.size atTop atTop := sz0.tendsto_size sz0_tendsto

private theorem contInst_one_le (n : ℕ) : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) :=
  Nat.one_le_cast.2 (sz0.one_le_size n)

/-- The all-ones sample: every coordinate equals `1`. -/
private def contInstω : sz0.SeqΩ := fun _ => 1

private theorem contInstω_good : contInstω ∈ contGood sz0 0 := fun _ => by
  simpa [contInstω] using contInst_one_le 0

/-- **`GopboundPin` at `sz0`**, `κ = 1/10`, `E ≡ 1/2`: its three deterministic premises
(`0 < κ`, `|E n| ≤ 2 - κ = 19/10`, `SizeTendsto sz0`) are discharged; the pin itself is S1-34's
`gopbound`, so it stays a hypothesis of the instance. -/
example (h : GopboundPin sz0 (1 / 10) (fun _ => (1 / 2 : ℝ))) :=
  h (by norm_num) (fun _ => by norm_num) sz0_tendsto

/-- **`cont_core` at `sz0`**: the entries of the flow on the window `[0, 1/16]`,
`ξ(u,(i,j)) = |H_u(i,j)|`, `ζ ≡ 1`, label set `Idx × Idx` (`N²` labels), `A = 4`, `Cv = 2`,
`ε = 2 N⁻¹`.  Discharged: the window, `#V ≤ N²`, the good event `contGood` (w.h.p., by
`cont_highProbAt_good`), `ε ≤ ζ`, and the closeness on `contGood` (from `cont_norm_Xentry_le`,
`cont_abs_sqrt_sub_sqrt_le`, `cont_sqrt_abs_le`).  The per-time domination stays a hypothesis. -/
example (hpt : PerTimeDomAt sz0.seqP sz0.size
      (U := fun n => TimeIcc (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => 1 / 16) n ×
        (Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)))
      (fun n p ω => ‖sz0.seqHflow n (p.1 : ℝ) ω p.2.1 p.2.2‖) (fun _ _ _ => (1 : ℝ))) :
    StochDomAt sz0.seqP sz0.size
      (U := fun n => TimeIcc (fun _ : ℕ => (0 : ℝ)) (fun _ : ℕ => 1 / 16) n ×
        (Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)))
      (fun n p ω => ‖sz0.seqHflow n (p.1 : ℝ) ω p.2.1 p.2.2‖) (fun _ _ _ => (1 : ℝ)) := by
  refine cont_core (V := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
    contInst_hsize (s := fun _ => (0 : ℝ)) (t := fun _ => 1 / 16) (fun _ => by norm_num)
    (fun _ => by norm_num) (A := 4) (Cv := 2) (by norm_num) (by norm_num) ?_ hpt
    (cont_highProbAt_good sz0 contInst_hsize)
    (ε := fun n => 2 * ((sz0.size n : ℕ) : ℝ)⁻¹) (fun n => by positivity) ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    rw [Fintype.card_prod, Nat.cast_mul, sz0.card_Idx n, Real.rpow_two]
    exact le_of_eq (by ring)
  · filter_upwards [contInst_hsize.eventually_ge_atTop 2] with n hn p ω
    have hN : (2 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast hn
    have : 2 * ((sz0.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; exact hN
    exact this
  · refine Eventually.of_forall fun n => ?_
    intro ω hω u u' hΔ v
    obtain ⟨i, j⟩ := v
    refine ⟨?_, by norm_num⟩
    have hN : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (contInst_one_le n)
    have hu0 : 0 ≤ (u : ℝ) := u.2.1
    have hu'0 : 0 ≤ (u' : ℝ) := u'.2.1
    have hsq := cont_sqrt_abs_le hN.le hΔ
    have hX := cont_norm_Xentry_le (sz0.slice n ω) (fun c => hω c) i j
    have e : ((sz0.size n : ℕ) : ℝ) ^ (-(4 : ℝ) / 2) = (((sz0.size n : ℕ) : ℝ) ^ 2)⁻¹ := by
      rw [show -(4 : ℝ) / 2 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hN.le, Real.rpow_natCast]
    have hdiff : ‖sz0.seqHflow n (u : ℝ) ω i j - sz0.seqHflow n (u' : ℝ) ω i j‖ ≤
        2 * ((sz0.size n : ℕ) : ℝ)⁻¹ := by
      have h1 := Hflow_sub_apply 3 (sz0.L n) (sz0.W n) (u : ℝ) (u' : ℝ) (sz0.slice n ω) i j
      change ‖(Hflow 3 (sz0.L n) (sz0.W n) u (sz0.slice n ω) -
        Hflow 3 (sz0.L n) (sz0.W n) u' (sz0.slice n ω)) i j‖ ≤ _
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |Real.sqrt u - Real.sqrt u'| * ‖Xentry 3 (sz0.L n) (sz0.W n) (sz0.slice n ω) i j‖
          ≤ Real.sqrt |(u : ℝ) - u'| * (2 * ((sz0.size n : ℕ) : ℝ)) :=
            mul_le_mul (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) hX (norm_nonneg _) (Real.sqrt_nonneg _)
        _ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(4 : ℝ) / 2) * (2 * ((sz0.size n : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = 2 * ((sz0.size n : ℕ) : ℝ)⁻¹ := by rw [e]; field_simp
    have := norm_le_insert' (sz0.seqHflow n (u : ℝ) ω i j) (sz0.seqHflow n (u' : ℝ) ω i j)
    change ‖sz0.seqHflow n (u : ℝ) ω i j‖ ≤ ‖sz0.seqHflow n (u' : ℝ) ω i j‖ + _
    linarith

/-- The good event has high probability (`cont_highProbAt_good` at `sz0`), and the tail bound of
`cont_good_compl` at `n = 0` (`N = 2097152`). -/
example : HighProbAt sz0.seqP sz0.size (contGood sz0) := cont_highProbAt_good sz0 contInst_hsize

example := cont_good_compl sz0 0

example : ∀ᶠ x : ℝ in atTop, 2 * x ^ 2 * (2 * Real.exp (-x ^ 2 / 2)) ≤ x ^ (-(10 : ℝ)) :=
  cont_eventually_tail 10

/-- `ω₁ ∈ contGood sz0 0` is used by the deterministic instances below: `‖X‖ ≤ #Idx · 2 N`, also for the
block-product reading. -/
example := cont_norm_Xmat_le (sz0.slice 0 contInstω) (B := ((sz0.size 0 : ℕ) : ℝ)) contInstω_good

example := cont_norm_blockMat_Xmat_le (sz0.slice 0 contInstω) (B := ((sz0.size 0 : ℕ) : ℝ))
  contInstω_good

example := cont_norm_Xentry_le (sz0.slice 0 contInstω) (B := ((sz0.size 0 : ℕ) : ℝ))
  contInstω_good (0 : Idx 3 (sz0.L 0) (sz0.W 0)) 1

example := cont_blockMat_sub (Xmat 3 (sz0.L 0) (sz0.W 0) (sz0.slice 0 contInstω))
  (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)

example := cont_blockMat_smul (Complex.I : ℂ) (Xmat 3 (sz0.L 0) (sz0.W 0) (sz0.slice 0 contInstω))

/- The resolvent bounds at the model matrix, `E = 1/2`, `t = 1/2`, `u = 1/4`, `u' = 1/8`,
`η = η_t = (1/2) Im m`. -/
section Resolvent

private theorem contInst_eta_pos : 0 < etaT (1 / 2) (1 / 2) := etaT_pos (by norm_num) (by norm_num)

private theorem contInst_herm (u : ℝ) : (sz0.seqHflow 0 u contInstω).IsHermitian :=
  Sizes.seqHflow_isHermitian sz0 0 u contInstω

example := cont_norm_green_le (contInst_herm (1 / 4)) contInst_eta_pos
  (cont_eta_le_abs_im (E := 1 / 2) (t := 1 / 2) (u := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num))

example := cont_green_diff (contInst_herm (1 / 4)) (contInst_herm (1 / 8)) contInst_eta_pos
  (cont_eta_le_abs_im (E := 1 / 2) (t := 1 / 2) (u := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num))
  (cont_eta_le_abs_im (E := 1 / 2) (t := 1 / 2) (u := 1 / 8) (by norm_num) (by norm_num)
    (by norm_num))

/-- **`cont_green_flow_diff` at the model**: `H_u - H_{u'} = (√u - √u') X`, `‖X‖ ≤ #Idx · 2N`
(`ω₁ ∈ contGood`), `Δ = |u - u'| = 1/8`, `Q = η⁻¹`. -/
example :=
  cont_green_flow_diff (contInst_herm (1 / 4)) (contInst_herm (1 / 8))
    (c := Real.sqrt (1 / 4) - Real.sqrt (1 / 8))
    (X := Xmat 3 (sz0.L 0) (sz0.W 0) (sz0.slice 0 contInstω))
    (Hflow_sub 3 (sz0.L 0) (sz0.W 0) (1 / 4) (1 / 8) (sz0.slice 0 contInstω))
    (cont_norm_Xmat_le (sz0.slice 0 contInstω) (B := ((sz0.size 0 : ℕ) : ℝ)) contInstω_good)
    (cont_abs_sqrt_sub_sqrt_le (by norm_num) (by norm_num)) (abs_nonneg _)
    (abs_le.2 ⟨by norm_num, by norm_num⟩) contInst_eta_pos le_rfl
    (cont_eta_le_abs_im (E := 1 / 2) (t := 1 / 2) (u := 1 / 4) (by norm_num) (by norm_num)
      (by norm_num))
    (cont_eta_le_abs_im (E := 1 / 2) (t := 1 / 2) (u := 1 / 8) (by norm_num) (by norm_num)
      (by norm_num))
    (le_of_eq (cont_norm_spectralZ_sub (E := 1 / 2) (by norm_num) (1 / 4) (1 / 8)))

example := cont_Gres_true_eq_green (sz0.seqHflow 0 (1 / 4) contInstω) (zt (1 / 2) (1 / 4))

example := cont_Gres_false_eq_green (sz0.seqHflow 0 (1 / 4) contInstω) (zt (1 / 2) (1 / 4))

/-- A `4 × 4` matrix instance of the generic operator-norm lemmas. -/
example := cont_norm_le_card_mul (1 : Matrix (Fin 4) (Fin 4) ℂ) (B := 1) zero_le_one
  (fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h])

example := cont_norm_one_le (n := Fin 4)

end Resolvent

/-- The spectral facts at `E = 1/2`, `κ = 1/10`, and `‖E_a‖ ≤ 1` at `L = 4`, `W = 32`, `d = 3`. -/
example := cont_im_m_le_one (E := 1 / 2) (by norm_num)

example := cont_spectralM_im_nonneg (1 / 2)

example := cont_norm_spectralZ_sub (E := 1 / 2) (by norm_num) (1 / 4) (1 / 8)

example := cont_eta_le_abs_im (E := 1 / 2) (t := 1 / 2) (u := 1 / 4) (by norm_num) (by norm_num)
  (by norm_num)

example := cont_norm_Eblk_le_one (d := 3) (L := sz0.L 0) (W := sz0.W 0) (sz0.W_pos 0)
  (0 : Zd 3 (sz0.L 0))

example := cont_bulk (κ := 1 / 10) (E := 1 / 2) (by norm_num) (by norm_num)

example := cont_abs_sqrt_sub_sqrt_le (x := 1 / 4) (y := 1 / 8) (by norm_num) (by norm_num)

example := cont_sqrt_rpow (N := ((sz0.size 0 : ℕ) : ℝ)) (Nat.cast_nonneg _) (-4)

example := cont_sqrt_abs_le (N := ((sz0.size 0 : ℕ) : ℝ)) (A := 4) (Δ := ((sz0.size 0 : ℕ) : ℝ) ^ (-(4 : ℝ)))
  (Nat.cast_nonneg _) le_rfl

example := cont_gap contInst_hsize 3 (κ := 1) (p := 1) (q := 2) one_pos (by norm_num)

example := cont_pow_mul_rpow (x := ((sz0.size 0 : ℕ) : ℝ)) (lt_of_lt_of_le one_pos (contInst_one_le 0)) 6
  (-(25 : ℝ))

/-- The scalar facts of section 4 at `sz0`, `n = 0`: the lower bound `N⁻¹ ≤ W^{-3} B_{s,0}` at
`s = 1/2`, and the ratio of the controls at `u = 1/4`, `u' = 3/8`, `t = 1/2`. -/
example := cont_inv_le_const_mul_inv (a := 1) (b := 2) (κ := 2) one_pos two_pos (by norm_num)

example := cont_inv_add_one_sub_ratio (γ := ((1 : ℝ) / 64) ^ 2) (t := 1 / 2) (u := 1 / 4)
  (u' := 3 / 8) (sq_nonneg _) (by norm_num) (by norm_num) (by norm_num)

example := cont_Bctl_eq sz0 0 (t := 1 / 2) (by norm_num)

example := cont_inv_size_le_Bctl sz0 0 (s := 1 / 2) (by norm_num) (by norm_num)

example := cont_Bctl_ratio sz0 0 (t := 1 / 2) (u := 1 / 4) (u' := 3 / 8) (by norm_num)
  (by norm_num) (by norm_num)

end Instances

end ContinuityNet

end RBM.Ind
