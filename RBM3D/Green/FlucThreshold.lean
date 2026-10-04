/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.MinorDiffCond
import RBM3D.Green.LocalLaw
import RBM3D.Green.FlucIterGain

/-!
# The smallness of the bad-event tower, and the fluctuation gain from the local law (ST-1, S1-28)

Ticket T2123.  Port of RBM2D `Green/Eq45Small.lean` (lines 59-404 of 505: `PolyLo`, `PolyHi`, the
closure lemmas, `measureReal_compl_le_of_polyLo`, `hsmall_of_highProb`) and of
`Green/FlucThreshold.lean` (lines 60-465 of 718: `detFlucDelta`, `detFlucControl`, `detFlucTheta`
and their bounds, `highProbAt_detFlucDelta_of_localLaw`, `flucGain_of_localLaw`) at RBM2D commit
`c9a24cf`, to `d ≥ 3`, with the renaming rules R1-R3 of `docs/tickets/ST1-COMMON.md`
(`d : Sizes` becomes `sz : Sizes d`, `Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`,
`d.size n = (W L)^d` becomes `sz.size n`, `W⁻²`-type becomes `W^{-d}`).  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem_GbEXP` (`3_5:14`), `(def_asGMc)` (`3_5:16`),
the window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` of `(initialGT2)` (`3_5:27`), `(GavLGEX)` (`3_5:33`); the
proof is "that of Lemma 4.1 in [YY_25]" (`3_5:37`).

## The route

  `LocalLawDetSeq sz E t Ψ`  ⟶  the per-time good event `{∀ i j, llErrMat … ≤ δ n}` at
  `δ = detFlucDelta sz Ψ θ` has high probability (`highProbAt_detFlucDelta_of_localLaw`)
  ⟶  `hsmall` (`hsmall_of_highProb`)  ⟶  `FlucGainUpTo'` (`flucGainUpTo'_goodEvent`,
  `Green/MinorDiffCond.lean`), the input of the `2p`-th moment expansion
  `integral_norm_flucAvg_pow_le_iter_budget` (`Green/FlucIterGain.lean`).

This file discharges the two debts of S1-26 (T2117): `hsmall` (`P(badTower) ≤ …`, invisible to the
axiom scan) is the theorem `hsmall_of_highProb`, and `hB1` is `detFlucDelta_moment_small`
(eventually, from `δ ≤ N^{-min(a/2,1)}`).  Both are `∀ᶠ n` statements; the threshold at which they
start (`D_W` for `hsmall`, `δ ≤ 2^{-19}` for `hB1` at `M = 1`) is in the prove report.

## What depends on the dimension

Only `size = (W L)^d` and the floor.  `PolyLo`/`PolyHi` are in powers of `size`, the regularising
floor `(size + 4)^{-2}` of `detFlucDelta`, the union over the `size²` pairs of
`highProbAt_detFlucDelta_of_localLaw`, `θ = min(a/8, τ/32, 1/8)` and `8 M δ ≤ 1` carry no `d`.
No statement needs `3 ≤ d`.

## Differences from RBM2D (every other ported statement equals RBM2D's after the renaming)

* **The floor and the weight conjunct** (paper-delta candidate `T2123a`).  RBM2D takes `W⁻¹ ≤ Ψ`
  and concludes `(W⁻¹)² ≤ (2 (2δ))²`.  Here the floor is the paper's `W^{-d/2} ≤ Ψ` (`3_5:27`, the
  floor of the merged pins `FixedTimeFAThm`, `LocalLawDetThm`; DECISIONS D213) and the conjunct is
  `W^{-d} ≤ (2 (2δ))²`, the `c ≤ ρ²` of `integral_norm_flucAvg_pow_le_iter_budget` at the bounded
  weight `c = W^{-d}` (DECISIONS §30, `uniformWeight_blockAvg2`, `boundedWeight_svarF`).  RBM2D's
  `(W⁻¹)²` with the pin's floor is false: `flucThreshold_literal_false` (a compiled slice
  `n = 3` of the instance).  The proof is `(W^{-d/2})² = W^{-d} ≤ Ψ² ≤ (4δ)²` (`Ψ/4 ≤ δ`,
  `Ψ ≤ 1`).  No statement here takes the floor `W⁻¹`; `detFlucControl_floor` and
  `detFlucDelta_floor_le` are the regularising floor `(size + 4)^{-2}`, not a floor on `Ψ`
  (`flucThreshold_control_eq_psi`: under the pin floor `W^{-d/2} ≤ Ψ` it never binds).
* `RBM.Path.etaT` is `RBM.Gauss.etaT`; `spectralZ E t`, `spectralM E` are `zt E t`, `mE E`;
  RBM2D `AvgPins_one_le_size` is the private real-valued `flucThreshold_one_le_size`
  (`Sizes.one_le_size`).
* `flucThreshold_check_consumer` takes the bounded weight
  `(uniformWeight_blockAvg2 …).toBoundedWeight` (RBM2D: the uniform weight itself).
* RBM2D's private `Checks` sections (instances at `RBM.Green.Instance` of RBM2D) are replaced by the
  instances at the end of this file, at the merged `sz0` (`d = 3`): `t ≡ 1/2` with the local law as
  hypothesis (A), and `t ≡ 0` with no hypothesis (B).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter RBM RBM.Gauss RBM.Path

open scoped ENNReal

variable {d : ℕ}

/-! ### Polynomial envelopes -/

/-- `f` is eventually at least a fixed negative power of the size `size n` (RBM1D `PolyLo`,
`Gauss/Eq45Small.lean:80`, with the size sequence in place of the level `N`). -/
def PolyLo (size : ℕ → ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ n : ℕ in atTop, C * ((size n : ℕ) : ℝ) ^ (-D) ≤ f n

/-- `f` is eventually at most a fixed power of the size `size n` (RBM1D `PolyHi`,
`Gauss/Eq45Small.lean:84`). -/
def PolyHi (size : ℕ → ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ n : ℕ in atTop, f n ≤ C * ((size n : ℕ) : ℝ) ^ D

theorem polyLo_const {size : ℕ → ℕ} {c : ℝ} (hc : 0 < c) : PolyLo size (fun _ => c) :=
  ⟨c, hc, 0, Filter.Eventually.of_forall fun n => by rw [neg_zero, Real.rpow_zero, mul_one]⟩

theorem polyHi_const {size : ℕ → ℕ} {c : ℝ} (hc : 0 < c) : PolyHi size (fun _ => c) :=
  ⟨c, hc, 0, Filter.Eventually.of_forall fun n => by rw [Real.rpow_zero, mul_one]⟩

theorem PolyLo.mono {size : ℕ → ℕ} {f g : ℕ → ℝ} (hf : PolyLo size f)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PolyLo size g := by
  obtain ⟨C, hC, D, hD⟩ := hf
  exact ⟨C, hC, D, by filter_upwards [hD, h] with n h1 h2 using h1.trans h2⟩

theorem PolyHi.mono {size : ℕ → ℕ} {f g : ℕ → ℝ} (hg : PolyHi size g)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PolyHi size f := by
  obtain ⟨C, hC, D, hD⟩ := hg
  exact ⟨C, hC, D, by filter_upwards [hD, h] with n h1 h2 using h2.trans h1⟩

theorem PolyLo.mul {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyLo size f) (hg : PolyLo size g) :
    PolyLo size (fun n => f n * g n) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C * C', by positivity, D + D', ?_⟩
  filter_upwards [hD, hD', hs.eventually_ge_atTop 1] with n h1 h2 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hsplit : ((size n : ℕ) : ℝ) ^ (-(D + D'))
      = ((size n : ℕ) : ℝ) ^ (-D) * ((size n : ℕ) : ℝ) ^ (-D') := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h1' : (0 : ℝ) ≤ C * ((size n : ℕ) : ℝ) ^ (-D) := by positivity
  have h2' : (0 : ℝ) ≤ C' * ((size n : ℕ) : ℝ) ^ (-D') := by positivity
  calc C * C' * ((size n : ℕ) : ℝ) ^ (-(D + D'))
      = (C * ((size n : ℕ) : ℝ) ^ (-D)) * (C' * ((size n : ℕ) : ℝ) ^ (-D')) := by
        rw [hsplit]; ring
    _ ≤ f n * g n := mul_le_mul h1 h2 h2' (h1'.trans h1)

theorem PolyHi.mul {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyHi size f) (hg : PolyHi size g)
    (hf0 : ∀ᶠ n : ℕ in atTop, 0 ≤ f n) (hg0 : ∀ᶠ n : ℕ in atTop, 0 ≤ g n) :
    PolyHi size (fun n => f n * g n) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C * C', by positivity, D + D', ?_⟩
  filter_upwards [hD, hD', hf0, hg0, hs.eventually_ge_atTop 1] with n h1 h2 h3 h4 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hsplit : ((size n : ℕ) : ℝ) ^ (D + D')
      = ((size n : ℕ) : ℝ) ^ D * ((size n : ℕ) : ℝ) ^ D' := Real.rpow_add hN0 _ _
  calc f n * g n ≤ (C * ((size n : ℕ) : ℝ) ^ D) * (C' * ((size n : ℕ) : ℝ) ^ D') :=
        mul_le_mul h1 h2 h4 (h3.trans h1)
    _ = C * C' * ((size n : ℕ) : ℝ) ^ (D + D') := by rw [hsplit]; ring

theorem PolyHi.add {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyHi size f) (hg : PolyHi size g) :
    PolyHi size (fun n => f n + g n) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C + C', by positivity, max D D', ?_⟩
  filter_upwards [hD, hD', hs.eventually_ge_atTop 1] with n h1 h2 hN1
  have hle : ((size n : ℕ) : ℝ) ^ D ≤ ((size n : ℕ) : ℝ) ^ (max D D') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have hle' : ((size n : ℕ) : ℝ) ^ D' ≤ ((size n : ℕ) : ℝ) ^ (max D D') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
  calc f n + g n ≤ C * ((size n : ℕ) : ℝ) ^ D + C' * ((size n : ℕ) : ℝ) ^ D' := by linarith
    _ ≤ C * ((size n : ℕ) : ℝ) ^ (max D D') + C' * ((size n : ℕ) : ℝ) ^ (max D D') := by
        have a1 : C * ((size n : ℕ) : ℝ) ^ D ≤ C * ((size n : ℕ) : ℝ) ^ (max D D') :=
          mul_le_mul_of_nonneg_left hle hC.le
        have a2 : C' * ((size n : ℕ) : ℝ) ^ D' ≤ C' * ((size n : ℕ) : ℝ) ^ (max D D') :=
          mul_le_mul_of_nonneg_left hle' hC'.le
        linarith
    _ = (C + C') * ((size n : ℕ) : ℝ) ^ (max D D') := by ring

theorem PolyLo.pow {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyLo size f) (k : ℕ) : PolyLo size (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using polyLo_const (size := size) (c := (1 : ℝ)) one_pos
  | succ k ih =>
      have := PolyLo.mul hs ih hf
      refine this.mono ?_
      exact Filter.Eventually.of_forall fun n => le_of_eq (by rw [pow_succ])

theorem PolyHi.pow {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyHi size f) (hf0 : ∀ᶠ n : ℕ in atTop, 0 ≤ f n) (k : ℕ) :
    PolyHi size (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using polyHi_const (size := size) (c := (1 : ℝ)) one_pos
  | succ k ih =>
      have hpow0 : ∀ᶠ n : ℕ in atTop, 0 ≤ f n ^ k := by
        filter_upwards [hf0] with n h using pow_nonneg h k
      have := PolyHi.mul hs ih hf hpow0 hf0
      refine this.mono ?_
      exact Filter.Eventually.of_forall fun n => le_of_eq (by rw [pow_succ])

/-- The reciprocal of a `PolyHi` function is `PolyLo`. -/
theorem PolyLo.inv {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyHi size f) (hf0 : ∀ᶠ n : ℕ in atTop, 0 < f n) :
    PolyLo size (fun n => (f n)⁻¹) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  refine ⟨C⁻¹, by positivity, D, ?_⟩
  filter_upwards [hD, hf0, hs.eventually_ge_atTop 1] with n h1 h2 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hrp : (0 : ℝ) < ((size n : ℕ) : ℝ) ^ D := Real.rpow_pos_of_pos hN0 _
  have hCN : (0 : ℝ) < C * ((size n : ℕ) : ℝ) ^ D := by positivity
  have : (C * ((size n : ℕ) : ℝ) ^ D)⁻¹ ≤ (f n)⁻¹ := inv_anti₀ h2 h1
  refine le_trans (le_of_eq ?_) this
  rw [mul_inv, ← Real.rpow_neg hN0.le]

/-- The reciprocal of a `PolyLo` function is `PolyHi`. -/
theorem PolyHi.inv {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f : ℕ → ℝ} (hf : PolyLo size f) : PolyHi size (fun n => (f n)⁻¹) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  refine ⟨C⁻¹, by positivity, D, ?_⟩
  filter_upwards [hD, hs.eventually_ge_atTop 1] with n h1 hN1
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  have hrp : (0 : ℝ) < ((size n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hCN : (0 : ℝ) < C * ((size n : ℕ) : ℝ) ^ (-D) := by positivity
  have : (f n)⁻¹ ≤ (C * ((size n : ℕ) : ℝ) ^ (-D))⁻¹ := inv_anti₀ hCN h1
  refine this.trans (le_of_eq ?_)
  rw [mul_inv, ← Real.rpow_neg hN0.le, neg_neg]

/-- A `PolyLo` numerator over a `PolyHi` denominator is `PolyLo`. -/
theorem PolyLo.div {size : ℕ → ℕ} (hs : Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop)
    {f g : ℕ → ℝ} (hf : PolyLo size f) (hg : PolyHi size g)
    (hg0 : ∀ᶠ n : ℕ in atTop, 0 < g n) : PolyLo size (fun n => f n / g n) := by
  have := PolyLo.mul hs hf (PolyLo.inv hs hg hg0)
  refine this.mono (Filter.Eventually.of_forall fun n => ?_)
  rw [div_eq_mul_inv]

/-! ### The only use of `HighProbAt` -/

/-- **Statement of `measureReal_compl_le_of_polyLo`** (RBM2D `Green/Eq45Small.lean:201`, RBM1D
`Gauss/Eq45Small.lean:211`): the
complement of a `HighProbAt` event is eventually below any `PolyLo` function, once the sizes
diverge.  This is where the `∀ D` of `HighProbAt` is spent. -/
theorem measureReal_compl_le_of_polyLo :
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ),
    Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop →
    ∀ {Ξ : ℕ → Set Ω}, HighProbAt P size Ξ → ∀ {f : ℕ → ℝ}, PolyLo size f →
      ∀ᶠ n : ℕ in atTop, P.real (Ξ n)ᶜ ≤ f n := by
  intro Ω _ P size hs Ξ hΞ f hf
  obtain ⟨C, hC, D, hD⟩ := hf
  have hD'pos : (0 : ℝ) < max (D + 1) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [hΞ (max (D + 1) 1) hD'pos, hD, hs.eventually_ge_atTop 1,
    hs.eventually_ge_atTop C⁻¹] with n h1 h2 hN1 hNC
  have hN0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by linarith
  set D' : ℝ := max (D + 1) 1 with hD'
  -- the measure bound, transported to `ℝ`
  have hstep1 : P.real (Ξ n)ᶜ ≤ ((size n : ℕ) : ℝ) ^ (-D') := by
    rw [measureReal_def]
    calc (P (Ξ n)ᶜ).toReal ≤ (ENNReal.ofReal (((size n : ℕ) : ℝ) ^ (-D'))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = ((size n : ℕ) : ℝ) ^ (-D') := ENNReal.toReal_ofReal (Real.rpow_nonneg hN0.le _)
  -- and the arithmetic `size^{-D'} ≤ C size^{-D}`
  have hCN : ((size n : ℕ) : ℝ)⁻¹ ≤ C := (inv_le_comm₀ hC hN0).1 hNC
  have hDD : (1 : ℝ) ≤ D' - D := by
    have : D + 1 ≤ D' := le_max_left _ _
    linarith
  have hsmallexp : ((size n : ℕ) : ℝ) ^ (-(D' - D)) ≤ C := by
    calc ((size n : ℕ) : ℝ) ^ (-(D' - D)) ≤ ((size n : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = ((size n : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ C := hCN
  have hstep2 : ((size n : ℕ) : ℝ) ^ (-D') ≤ C * ((size n : ℕ) : ℝ) ^ (-D) := by
    have hsplit : ((size n : ℕ) : ℝ) ^ (-D')
        = ((size n : ℕ) : ℝ) ^ (-D) * ((size n : ℕ) : ℝ) ^ (-(D' - D)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [hsplit]
    have hnn : (0 : ℝ) ≤ ((size n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
    calc ((size n : ℕ) : ℝ) ^ (-D) * ((size n : ℕ) : ℝ) ^ (-(D' - D))
        ≤ ((size n : ℕ) : ℝ) ^ (-D) * C := mul_le_mul_of_nonneg_left hsmallexp hnn
      _ = C * ((size n : ℕ) : ℝ) ^ (-D) := by ring
  exact hstep1.trans (hstep2.trans h2)

/-! ### `hsmall`, derived -/

/-- **Statement of `hsmall_of_highProb`** (RBM2D `Green/Eq45Small.lean:248`; RBM1D
`hsmall_of_highProb_auxN`, `EnergyN/Gauss/Eq45Small.lean:48`, and `hsmall_of_highProbN` :237, per
time): the `hsmall` premise of the merged `flucGainUpTo'_goodEvent` at
`ε = condEps (E n) (t n) M (2 δ n)`, for every pair of budgets `M, K`, from the high probability of
the per-time good event (4.1).  The price `condEnv^K ((ε + size)/ε)^{M+1}` is `PolyHi`, the target
`B₀^K (2 · 2δ)^{KM}` is `PolyLo`, and one `D` of `HighProbAt` beats their ratio: it suffices that
`P(Ωᶜ) ≤ size^{-D_N}` with `D_N = log_N (price / target)`, and `D_W = ν D_N` in powers of `W`
(`size = W^ν`, `ν = log_W N`; `ν = 2d` at `L = W`).  Only `size = (W L)^d` carries the dimension. -/
theorem hsmall_of_highProb :
  ∀ (sz : Sizes d) {E t δ : ℕ → ℝ}, sz.SizeTendsto → (∀ n, |E n| < 2) → (∀ n, t n < 1) →
    (∀ n, 0 < δ n) → PolyLo sz.size δ →
    PolyHi sz.size (fun n => (etaT (E n) (t n))⁻¹ + 1) →
    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}) →
    ∀ M K : ℕ, ∀ᶠ n : ℕ in atTop,
      condEnv (E n) (t n) M ^ K
          * (Sizes.seqP sz).real (badTower sz n (condEps (E n) (t n) M (2 * δ n))
              (badBase sz E t δ n) (M + 1))
        ≤ (2 * minorDiffC M * (2 * δ n)
            + condCost (E n) (t n) M (2 * δ n) (condEps (E n) (t n) M (2 * δ n))) ^ K
          * (2 * (2 * δ n)) ^ (K * M) := by
  intro sz E t δ hsz hE ht1 hδpos hδlo hηhi hΩ M K
  classical
  have hΨpos : ∀ n, (0 : ℝ) < 2 * δ n := fun n => by linarith [hδpos n]
  have hηt : ∀ n, 0 < etaT (E n) (t n) := fun n => etaT_pos (hE n) (ht1 n)
  have hEnv0 : ∀ n, (0 : ℝ) < condEnv (E n) (t n) M := fun n =>
    lt_of_lt_of_le zero_lt_one (one_le_condEnv (hE n) (ht1 n) M)
  have hMEnv0 : ∀ n, (0 : ℝ) < ((M : ℝ) + 1) * condEnv (E n) (t n) M := fun n => by
    have := hEnv0 n; positivity
  have heps0 : ∀ n, (0 : ℝ) < condEps (E n) (t n) M (2 * δ n) := by
    intro n
    change (0 : ℝ) < (2 * δ n) * (2 * (2 * δ n)) ^ M
      * (((M : ℝ) + 1) * condEnv (E n) (t n) M)⁻¹
    have h1 := hΨpos n
    have h3 : (0 : ℝ) < (2 * (2 * δ n)) ^ M := by positivity
    exact mul_pos (mul_pos h1 h3) (inv_pos.2 (hMEnv0 n))
  have hR0 : ∀ n, (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => Nat.cast_nonneg _
  have hq0 : ∀ n, (0 : ℝ) < (condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
      / condEps (E n) (t n) M (2 * δ n) := fun n =>
    div_pos (add_pos_of_pos_of_nonneg (heps0 n) (hR0 n)) (heps0 n)
  have hG0 : ∀ n, (0 : ℝ) < condEnv (E n) (t n) M ^ K
      * ((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
          / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1) := fun n =>
    mul_pos (pow_pos (hEnv0 n) K) (pow_pos (hq0 n) (M + 1))
  -- the target is bounded below by a fixed negative power of the size
  have hΨlo : PolyLo sz.size fun n => 2 * δ n :=
    hδlo.mono (Filter.Eventually.of_forall fun n => by linarith [(hδpos n).le])
  have hB0lo : PolyLo sz.size fun n => 2 * minorDiffC M * (2 * δ n) + 2 * δ n :=
    hΨlo.mono (Filter.Eventually.of_forall fun n => by
      have h1 := minorDiffC_nonneg M
      have h2 := (hδpos n).le
      nlinarith)
  have h2Ψlo : PolyLo sz.size fun n => 2 * (2 * δ n) :=
    hΨlo.mono (Filter.Eventually.of_forall fun n => by linarith [(hδpos n).le])
  have hSlo : PolyLo sz.size fun n =>
      (2 * minorDiffC M * (2 * δ n) + 2 * δ n) ^ K * (2 * (2 * δ n)) ^ (K * M) :=
    (hB0lo.pow hsz K).mul hsz (h2Ψlo.pow hsz (K * M))
  -- the price is bounded above by a fixed power of the size
  have hEnvhi : PolyHi sz.size fun n => condEnv (E n) (t n) M := by
    have hc : PolyHi sz.size fun _ : ℕ => (2 : ℝ) ^ (2 * M + 1) := polyHi_const (by positivity)
    have hnn : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (etaT (E n) (t n))⁻¹ + 1 :=
      Filter.Eventually.of_forall fun n => by
        have : (0 : ℝ) ≤ (etaT (E n) (t n))⁻¹ := inv_nonneg.2 (hηt n).le
        linarith
    have h := hc.mul hsz hηhi (Filter.Eventually.of_forall fun _ => by positivity) hnn
    exact h.mono (Filter.Eventually.of_forall fun n => le_of_eq rfl)
  have hMEnvhi : PolyHi sz.size fun n => ((M : ℝ) + 1) * condEnv (E n) (t n) M :=
    (polyHi_const (c := (M : ℝ) + 1) (by positivity)).mul hsz hEnvhi
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall fun n => (hEnv0 n).le)
  have hepslo : PolyLo sz.size fun n => condEps (E n) (t n) M (2 * δ n) := by
    have h := (hΨlo.mul hsz (h2Ψlo.pow hsz M)).mul hsz
      (PolyLo.inv hsz hMEnvhi (Filter.Eventually.of_forall hMEnv0))
    exact h.mono (Filter.Eventually.of_forall fun n => le_of_eq rfl)
  have hRhi : PolyHi sz.size fun n => ((sz.size n : ℕ) : ℝ) :=
    ⟨1, one_pos, 1, Filter.Eventually.of_forall fun n => by rw [Real.rpow_one, one_mul]⟩
  have hquothi : PolyHi sz.size fun n =>
      (condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
        / condEps (E n) (t n) M (2 * δ n) := by
    have hprod : PolyHi sz.size fun n =>
        ((sz.size n : ℕ) : ℝ) * (condEps (E n) (t n) M (2 * δ n))⁻¹ :=
      hRhi.mul hsz (PolyHi.inv hsz hepslo) (Filter.Eventually.of_forall hR0)
        (Filter.Eventually.of_forall fun n => (inv_pos.2 (heps0 n)).le)
    refine ((polyHi_const (c := (1 : ℝ)) one_pos).add hsz hprod).mono
      (Filter.Eventually.of_forall fun n => le_of_eq ?_)
    rw [add_div, div_self (heps0 n).ne', div_eq_mul_inv]
  have hGhi : PolyHi sz.size fun n => condEnv (E n) (t n) M ^ K
      * ((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
          / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1) :=
    (hEnvhi.pow hsz (Filter.Eventually.of_forall fun n => (hEnv0 n).le) K).mul hsz
      (hquothi.pow hsz (Filter.Eventually.of_forall fun n => (hq0 n).le) (M + 1))
      (Filter.Eventually.of_forall fun n => pow_nonneg (hEnv0 n).le K)
      (Filter.Eventually.of_forall fun n => pow_nonneg (hq0 n).le (M + 1))
  -- and (4.1) beats the quotient
  have hkey := measureReal_compl_le_of_polyLo (Sizes.seqP sz) sz.size hsz hΩ
    (hSlo.div hsz hGhi (Filter.Eventually.of_forall hG0))
  filter_upwards [hkey] with n hn
  -- the tower's measure
  have hε0 : (0 : ℝ) ≤ condEps (E n) (t n) M (2 * δ n) := (heps0 n).le
  have htow := minorDiffCond_meas_badTower_le_size sz n
    (ε := condEps (E n) (t n) M (2 * δ n)) (measurableSet_badBase sz E t δ n) (M + 1)
  have hfin : ((ENNReal.ofReal (condEps (E n) (t n) M (2 * δ n))
      + ((sz.size n : ℕ) : ℝ≥0∞)) ^ (M + 1) * (Sizes.seqP sz) (badBase sz E t δ n)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.natCast_ne_top _⟩)) (measure_ne_top _ _)
  have hL : (ENNReal.ofReal (condEps (E n) (t n) M (2 * δ n)) ^ (M + 1)
        * (Sizes.seqP sz) (badTower sz n (condEps (E n) (t n) M (2 * δ n))
            (badBase sz E t δ n) (M + 1))).toReal
      = condEps (E n) (t n) M (2 * δ n) ^ (M + 1)
        * (Sizes.seqP sz).real (badTower sz n (condEps (E n) (t n) M (2 * δ n))
            (badBase sz E t δ n) (M + 1)) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε0, measureReal_def]
  have hRr : ((ENNReal.ofReal (condEps (E n) (t n) M (2 * δ n))
        + ((sz.size n : ℕ) : ℝ≥0∞)) ^ (M + 1) * (Sizes.seqP sz) (badBase sz E t δ n)).toReal
      = (condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ)) ^ (M + 1)
        * (Sizes.seqP sz).real (badBase sz E t δ n) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _),
      ENNReal.toReal_ofReal hε0, ENNReal.toReal_natCast, measureReal_def]
  have hreal := ENNReal.toReal_mono hfin htow
  rw [hL, hRr] at hreal
  have hp0 : (Sizes.seqP sz).real (badBase sz E t δ n)
      = (Sizes.seqP sz).real {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
          llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}ᶜ := by
    rw [measureReal_def, measureReal_def, meas_badBase]
  have hp0nn : (0 : ℝ) ≤ (Sizes.seqP sz).real (badBase sz E t δ n) := measureReal_nonneg
  -- divide by `ε^{M+1}`
  have hA : (Sizes.seqP sz).real
        (badTower sz n (condEps (E n) (t n) M (2 * δ n)) (badBase sz E t δ n) (M + 1))
      ≤ ((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
          / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1)
        * (Sizes.seqP sz).real (badBase sz E t δ n) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos (heps0 n) (M + 1)), mul_comm]
    exact hreal
  -- the price of conditionalizing is exactly `2 δ n` at `ε = condEps`
  have hcc : condCost (E n) (t n) M (2 * δ n) (condEps (E n) (t n) M (2 * δ n)) = 2 * δ n :=
    condCost_condEps (hE n) (ht1 n) M (hΨpos n)
  rw [hcc]
  calc condEnv (E n) (t n) M ^ K
        * (Sizes.seqP sz).real
          (badTower sz n (condEps (E n) (t n) M (2 * δ n)) (badBase sz E t δ n) (M + 1))
      ≤ condEnv (E n) (t n) M ^ K
          * (((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
              / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1)
            * (Sizes.seqP sz).real (badBase sz E t δ n)) :=
        mul_le_mul_of_nonneg_left hA (pow_nonneg (hEnv0 n).le K)
    _ = (condEnv (E n) (t n) M ^ K
          * ((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
              / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1))
        * (Sizes.seqP sz).real (badBase sz E t δ n) := by ring
    _ ≤ (condEnv (E n) (t n) M ^ K
          * ((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
              / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1))
        * (((2 * minorDiffC M * (2 * δ n) + 2 * δ n) ^ K * (2 * (2 * δ n)) ^ (K * M))
          / (condEnv (E n) (t n) M ^ K
            * ((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
                / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (hG0 n).le
        rw [hp0]; exact hn
    _ = (2 * minorDiffC M * (2 * δ n) + 2 * δ n) ^ K * (2 * (2 * δ n)) ^ (K * M) := by
        have hGne : condEnv (E n) (t n) M ^ K
            * ((condEps (E n) (t n) M (2 * δ n) + ((sz.size n : ℕ) : ℝ))
                / condEps (E n) (t n) M (2 * δ n)) ^ (M + 1) ≠ 0 := (hG0 n).ne'
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hGne]

/-! ### The threshold -/

/-- Positive threshold, capped at `1/4`, with a polynomial floor (RBM1D `detFlucDelta`,
`Gauss/DetFlucThreshold.lean:33`, the level `N` replaced by the size `sz.size n`; RBM2D
`Green/FlucThreshold.lean:64`). -/
def detFlucDelta (sz : Sizes d) (Ψ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : ℝ :=
  min (1 / 4 : ℝ)
    ((((sz.size n : ℕ) : ℝ) + 4) ^ θ * max (Ψ n) ((((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ))))

/-- The regularized entry control (RBM1D `detFlucControl`, `Gauss/DetFlucThreshold.lean:38`). -/
def detFlucControl (sz : Sizes d) (Ψ : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (Ψ n) ((((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)))

/-- A threshold exponent chosen after the domination tolerance `τ` (RBM1D `detFlucTheta`,
`Gauss/DetFlucThreshold.lean:42`). -/
def detFlucTheta (a τ : ℝ) : ℝ :=
  min (a / 8) (min (τ / 32) (1 / 8))

theorem detFlucTheta_specs {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    0 < detFlucTheta a τ ∧ detFlucTheta a τ < a / 4 ∧
      detFlucTheta a τ < τ / 16 ∧ detFlucTheta a τ ≤ 1 / 4 := by
  unfold detFlucTheta
  have hpos : 0 < min (a / 8) (min (τ / 32) (1 / 8)) :=
    lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have ha8 := min_le_left (a / 8) (min (τ / 32) (1 / 8))
  have hτ32 := (min_le_right (a / 8) (min (τ / 32) (1 / 8))).trans
    (min_le_left (τ / 32) (1 / 8))
  have h8 := (min_le_right (a / 8) (min (τ / 32) (1 / 8))).trans
    (min_le_right (τ / 32) (1 / 8))
  refine ⟨hpos, ?_, ?_, ?_⟩ <;> linarith

theorem detFlucControl_pos (sz : Sizes d) (Ψ : ℕ → ℝ) (n : ℕ) : 0 < detFlucControl sz Ψ n := by
  unfold detFlucControl
  have hn : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) + 4 := by positivity
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hn _) (le_max_right _ _)

theorem detFlucControl_ge_psi (sz : Sizes d) (Ψ : ℕ → ℝ) (n : ℕ) : Ψ n ≤ detFlucControl sz Ψ n :=
  le_max_left _ _

theorem detFlucControl_floor (sz : Sizes d) (Ψ : ℕ → ℝ) (n : ℕ) :
    (((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)) ≤ detFlucControl sz Ψ n :=
  le_max_right _ _

/-! #### Real-variable cores (`x` stands for the size `sz.size n`) -/

private theorem detFlucCtrl_le_rpow_core {x ψ a : ℝ} (hx : 1 ≤ x) (hψ : ψ ≤ x ^ (-a)) :
    max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min a 1)) := by
  have hβa : min a 1 ≤ a := min_le_left _ _
  have hβ1 : min a 1 ≤ 1 := min_le_right _ _
  have hnp : (0 : ℝ) < x := by linarith
  have hxx : x ≤ x + 4 := by linarith
  have hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnp hxx (by norm_num)
  apply max_le
  · exact hψ.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  · exact hfloor.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))

private theorem detFlucDelta_floor_le_core {x ψ θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ) :
    (x + 4) ^ (-(2 : ℝ)) ≤ min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) := by
  have hx4 : (4 : ℝ) ≤ x + 4 := by linarith
  have hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ 1 / 4 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) hx4
      (by norm_num : -(2 : ℝ) ≤ 0)
    norm_num at h ⊢
    linarith
  have hpow : 1 ≤ (x + 4) ^ θ := Real.one_le_rpow (by linarith : (1 : ℝ) ≤ x + 4) hθ
  apply le_min
  · exact hfloor
  · have hmax : (x + 4) ^ (-(2 : ℝ)) ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) := le_max_right _ _
    have hpos : 0 ≤ (x + 4) ^ (-(2 : ℝ)) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hpos,
      mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x + 4) θ) (sub_nonneg.mpr hmax)]

private theorem detFlucPow_neg_four_le_core {x : ℝ} (hx : 4 ≤ x) :
    x ^ (-(4 : ℝ)) ≤ (x + 4) ^ (-(2 : ℝ)) := by
  have hnp : (0 : ℝ) < x := by linarith
  have hsq : x + 4 ≤ x ^ (2 : ℕ) := by nlinarith
  have hlow := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < x + 4) hsq
    (by norm_num : -(2 : ℝ) ≤ 0)
  have hr : (x ^ (2 : ℕ)) ^ (-(2 : ℝ)) = x ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnp.le]
    norm_num
  rw [hr] at hlow
  exact hlow

private theorem detFlucDelta_le_rpow_core {x ψ a θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4) (hx : 4 ≤ x) (hψ : ψ ≤ x ^ (-a)) :
    min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) ≤ x ^ (-(min (a / 2) 1)) := by
  have hβa : min (a / 2) 1 ≤ a / 2 := min_le_left _ _
  have hβ1 : min (a / 2) 1 ≤ 1 := min_le_right _ _
  have hn : (1 : ℝ) ≤ x := by linarith
  have hnpos : (0 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) ≤ x + 4 := by positivity
  have hxN : x ≤ x + 4 := by linarith
  have hxN2 : x + 4 ≤ x ^ (2 : ℕ) := by nlinarith
  have hpow : (x + 4) ^ θ ≤ x ^ (2 * θ) := by
    calc
      (x + 4) ^ θ ≤ (x ^ (2 : ℕ)) ^ θ := Real.rpow_le_rpow hx0 hxN2 hθ0
      _ = x ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        ring_nf
  have hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnpos hxN (by norm_num)
  have hΨcap : ψ ≤ x ^ (-(min (a / 2) 1 + 2 * θ)) :=
    hψ.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have hfloorcap : (x + 4) ^ (-(2 : ℝ)) ≤ x ^ (-(min (a / 2) 1 + 2 * θ)) :=
    hfloor.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have hmax : max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min (a / 2) 1 + 2 * θ)) :=
    max_le hΨcap hfloorcap
  have hmax0 : (0 : ℝ) ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) :=
    le_trans (by positivity) (le_max_right _ _)
  have hraw : (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))
      ≤ x ^ (2 * θ) * x ^ (-(min (a / 2) 1 + 2 * θ)) := by
    calc
      _ ≤ x ^ (2 * θ) * max ψ ((x + 4) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hpow hmax0
      _ ≤ x ^ (2 * θ) * x ^ (-(min (a / 2) 1 + 2 * θ)) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
  calc
    min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))))
        ≤ (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))) := min_le_right _ _
    _ ≤ x ^ (2 * θ) * x ^ (-(min (a / 2) 1 + 2 * θ)) := hraw
    _ = x ^ (-(min (a / 2) 1)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

private theorem detFlucDelta_margin_core {x ψ a θ : ℝ} (hθ0 : 0 < θ) (hx : 1 ≤ x)
    (hctrl : max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min a 1)))
    (hpow : 4 ≤ x ^ (min a 1 - θ / 2)) :
    x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ)))
      ≤ min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) := by
  have hnp : (0 : ℝ) < x := by linarith
  have hpowp : (0 : ℝ) < x ^ (min a 1 - θ / 2) := Real.rpow_pos_of_pos hnp _
  have hctrl0 : (0 : ℝ) ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) :=
    le_trans (by positivity) (le_max_right _ _)
  have hcap : x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ 1 / 4 := by
    have hh : x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ))) ≤ x ^ (-(min a 1 - θ / 2)) := by
      calc
        _ ≤ x ^ (θ / 2) * x ^ (-(min a 1)) :=
          mul_le_mul_of_nonneg_left hctrl (by positivity)
        _ = x ^ (-(min a 1 - θ / 2)) := by
          rw [← Real.rpow_add hnp]
          congr 1
          ring
    have hquarter : x ^ (-(min a 1 - θ / 2)) ≤ 1 / 4 := by
      rw [Real.rpow_neg hnp.le]
      rw [inv_le_iff_one_le_mul₀ hpowp]
      linarith
    exact hh.trans hquarter
  have hraw : x ^ (θ / 2) * max ψ ((x + 4) ^ (-(2 : ℝ)))
      ≤ (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))) := by
    have hbase : x ^ (θ / 2) ≤ (x + 4) ^ θ := by
      calc
        x ^ (θ / 2) ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
        _ ≤ (x + 4) ^ θ := Real.rpow_le_rpow hnp.le (by linarith) hθ0.le
    exact mul_le_mul_of_nonneg_right hbase hctrl0
  exact le_min hcap hraw

private theorem detFlucDelta_quarter_psi_le_core {x ψ θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ)
    (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ 1) :
    ψ / 4 ≤ min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) := by
  apply le_min
  · linarith
  · have hn : (1 : ℝ) ≤ x + 4 := by linarith
    have hp : 1 ≤ (x + 4) ^ θ := Real.one_le_rpow hn hθ
    have hmax : ψ ≤ max ψ ((x + 4) ^ (-(2 : ℝ))) := le_max_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hψ0,
      mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x + 4) θ) (sub_nonneg.mpr hmax)]

/-! #### The threshold and its bounds -/

/-- The positive floor does not change the eventual polynomial upper scale. -/
theorem detFlucControl_le_rpow (sz : Sizes d) (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {a : ℝ}
    (_ha : 0 < a) (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop, detFlucControl sz Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-(min a 1)) := by
  filter_upwards [hΨ, hsz.eventually_ge_atTop 1] with n hΨn hn
  exact detFlucCtrl_le_rpow_core hn hΨn

theorem detFlucDelta_pos (sz : Sizes d) (Ψ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : 0 < detFlucDelta sz Ψ θ n := by
  unfold detFlucDelta
  have hn : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) + 4 := by positivity
  exact lt_min (by norm_num) (mul_pos (Real.rpow_pos_of_pos hn θ)
    (lt_of_lt_of_le (Real.rpow_pos_of_pos hn _) (le_max_right _ _)))

theorem detFlucDelta_le_quarter (sz : Sizes d) (Ψ : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    detFlucDelta sz Ψ θ n ≤ 1 / 4 := min_le_left _ _

theorem detFlucDelta_floor_le (sz : Sizes d) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    (((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)) ≤ detFlucDelta sz Ψ θ n :=
  detFlucDelta_floor_le_core (Nat.cast_nonneg _) hθ

theorem detFlucDelta_polyLo (sz : Sizes d) (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) :
    PolyLo sz.size (detFlucDelta sz Ψ θ) := by
  refine ⟨1, one_pos, 4, ?_⟩
  filter_upwards [hsz.eventually_ge_atTop 4] with n hn
  rw [one_mul]
  exact (detFlucPow_neg_four_le_core hn).trans (detFlucDelta_floor_le sz hθ n)

/-- Both the entry-control branch and the positive floor decay at a common power. -/
theorem detFlucDelta_le_rpow (sz : Sizes d) (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {a θ : ℝ}
    (_ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop,
      detFlucDelta sz Ψ θ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-(min (a / 2) 1)) := by
  filter_upwards [hΨ, hsz.eventually_ge_atTop 4] with n hΨn hn
  exact detFlucDelta_le_rpow_core hθ0 hθa hθ1 hn hΨn

/-- The required good-event margin `size^{θ/2} · control ≤ threshold`, including the global positive
control floor. -/
theorem detFlucDelta_margin (sz : Sizes d) (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop,
      ((sz.size n : ℕ) : ℝ) ^ (θ / 2) * detFlucControl sz Ψ n ≤ detFlucDelta sz Ψ θ n := by
  have hβθ : 0 < min a 1 - θ / 2 := by
    have hβpos : 0 < min a 1 := lt_min ha (by norm_num)
    rcases le_total a 1 with ha1 | ha1
    · rw [min_eq_left ha1]; linarith
    · rw [min_eq_right ha1]; linarith
  filter_upwards [detFlucControl_le_rpow sz hsz ha hΨ,
    ((tendsto_rpow_atTop hβθ).comp hsz).eventually_ge_atTop 4,
    hsz.eventually_ge_atTop 1] with n hctrl hpow hn
  exact detFlucDelta_margin_core (a := a) hθ0 hn hctrl hpow

/-- For each fixed coefficient, the threshold is eventually small. -/
theorem detFlucDelta_eventually_mul_le_one (sz : Sizes d) (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ}
    {a θ C : ℝ} (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C * detFlucDelta sz Ψ θ n ≤ 1 := by
  have hβ : 0 < min (a / 2) 1 := lt_min (by linarith) (by norm_num)
  filter_upwards [detFlucDelta_le_rpow sz hsz ha hθ0 hθa hθ1 hΨ,
    ((tendsto_rpow_atTop hβ).comp hsz).eventually_ge_atTop C, hsz.eventually_ge_atTop 1]
    with n hδ hCn hn
  have hnp : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hp : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (min (a / 2) 1) := Real.rpow_pos_of_pos hnp _
  have hbound : C * ((sz.size n : ℕ) : ℝ) ^ (-(min (a / 2) 1)) ≤ 1 := by
    rw [Real.rpow_neg hnp.le]
    rw [mul_inv_le_iff₀ hp]
    simpa using hCn
  exact (mul_le_mul_of_nonneg_left hδ hC).trans hbound

/-- The two smallness conditions of `flucGainUpTo'_goodEvent` at the threshold, for every budget
`M`: `8 M δ ≤ 1` and `2 C_M (2 δ) + 2 δ ≤ 1` (`hB1` at `condCost = 2 δ`), eventually. -/
theorem detFlucDelta_moment_small (sz : Sizes d) (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) (M : ℕ) :
    (∀ᶠ n : ℕ in atTop, 8 * (M : ℝ) * detFlucDelta sz Ψ θ n ≤ 1) ∧
    (∀ᶠ n : ℕ in atTop,
      2 * minorDiffC M * (2 * detFlucDelta sz Ψ θ n) + 2 * detFlucDelta sz Ψ θ n ≤ 1) := by
  have hC : 0 ≤ 4 * minorDiffC M + 2 := by
    have := minorDiffC_nonneg M
    linarith
  constructor
  · filter_upwards [detFlucDelta_eventually_mul_le_one sz hsz ha hθ0 hθa hθ1 hΨ
      (C := 8 * (M : ℝ)) (by positivity)] with n hn
    exact hn
  · filter_upwards [detFlucDelta_eventually_mul_le_one sz hsz ha hθ0 hθa hθ1 hΨ
      (C := 4 * minorDiffC M + 2) hC] with n hn
    nlinarith

/-- The cap never reduces the threshold below a quarter of a small entry control. -/
theorem detFlucDelta_quarter_psi_le (sz : Sizes d) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    {n : ℕ} (hΨ0 : 0 ≤ Ψ n) (hΨ1 : Ψ n ≤ 1) :
    Ψ n / 4 ≤ detFlucDelta sz Ψ θ n :=
  detFlucDelta_quarter_psi_le_core (Nat.cast_nonneg _) hθ hΨ0 hΨ1

/-- `(W^{-d/2})² = W^{-d}` (private copy of `LocalLaw.lean`'s `localLaw_rpow_floor_sq`). -/
private theorem flucThreshold_rpow_floor_sq (W d : ℕ) :
    (((W : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((W : ℕ) : ℝ) ^ d)⁻¹ := by
  have hW : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
  have h : -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) := by push_cast; ring
  rw [h, Real.rpow_neg hW, Real.rpow_natCast]

/-- **The `d`-dimensional weight condition.**  The floor `W^{-d/2} ≤ Ψ` (`3_5:27`, the floor of the
merged pins `FixedTimeFAThm`, `LocalLawDetThm`) and `Ψ ≤ size^{-a}` give `W^{-d} ≤ (2 (2 δ))²`
eventually: the `c ≤ ρ²` of `integral_norm_flucAvg_pow_le_iter_budget` at the bounded weight
`c = W^{-d}` (DECISIONS §30, `uniformWeight_blockAvg2`, `boundedWeight_svarF`) and `ρ = 2 (2 δ)`.
It follows from `(W^{-d/2})² = W^{-d} ≤ Ψ² ≤ (4δ)²`, `Ψ/4 ≤ δ` (`detFlucDelta_quarter_psi_le`) and
`Ψ ≤ 1`.  Replaces RBM2D `flucThreshold_W_inv_sq_le_detFlucDelta_sq` (`(W⁻¹)² ≤ (2 (2 δ))²` from
`W⁻¹ ≤ Ψ`, false here: `T2123` preflight (a) row 12) and RBM1D
`eventually_W_inv_le_detFlucDelta_sq` (`Gauss/DetFlucThreshold.lean:309`,
`W^{-1/2} ≤ Ψ ⇒ W⁻¹ ≤ (4δ)²`: the `d = 1` case of this one). -/
private theorem flucThreshold_W_pow_inv_le_detFlucDelta_sq (sz : Sizes d) (hsz : sz.SizeTendsto)
    {Ψ : ℕ → ℝ} {a θ : ℝ} (ha : 0 < a) (hθ : 0 ≤ θ)
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (2 * (2 * detFlucDelta sz Ψ θ n)) ^ 2 := by
  filter_upwards [hΨlo, hΨhi, hsz.eventually_ge_atTop 1] with n hlow hhigh hn
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hΨ0 : 0 ≤ Ψ n := hW0.trans hlow
  have hΨ1 : Ψ n ≤ 1 :=
    hhigh.trans (by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith : -a ≤ (0 : ℝ))))
  have hquarter := detFlucDelta_quarter_psi_le sz hθ hΨ0 hΨ1
  have hΨδ : Ψ n ≤ 2 * (2 * detFlucDelta sz Ψ θ n) := by linarith
  rw [← flucThreshold_rpow_floor_sq (sz.W n) d]
  exact (pow_le_pow_left₀ hW0 hlow 2).trans (pow_le_pow_left₀ hΨ0 hΨδ 2)

/-- **The regularising floor never binds under the pin floor.**  `N = (W L)^d ≥ W^d`, so
`(N + 4)^{-2} ≤ W^{-d/2}`, and `W^{-d/2} ≤ Ψ n` gives `detFlucControl sz Ψ n = Ψ n`.  This is the
check of `detFlucControl_floor` and `detFlucDelta_floor_le` at the floor `W^{-d/2}`: they are floors
`(N + 4)^{-2}` of the regularised control, not floors on `Ψ`, and they are below the pin's. -/
private theorem flucThreshold_control_eq_psi (sz : Sizes d) {Ψ : ℕ → ℝ} {n : ℕ}
    (h : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) : detFlucControl sz Ψ n = Ψ n := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h1 : (sz.W n) ^ d ≤ sz.size n := by
      unfold Sizes.size
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    exact_mod_cast h1
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hx : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) + 4 := by linarith
  have hle : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) ≤ (((sz.size n : ℕ) : ℝ) + 4) ^ (2 : ℕ) := by
    calc ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      _ = ((sz.W n : ℕ) : ℝ) ^ d := Real.rpow_natCast _ d
      _ ≤ ((sz.size n : ℕ) : ℝ) + 4 := by linarith
      _ ≤ (((sz.size n : ℕ) : ℝ) + 4) ^ (2 : ℕ) := by nlinarith
  have hfloor : (((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [neg_div, Real.rpow_neg hW0.le, show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (by linarith), Real.rpow_natCast]
    exact inv_anti₀ (Real.rpow_pos_of_pos hW0 _) hle
  unfold detFlucControl
  exact max_eq_left (hfloor.trans h)

/-! #### The `η` input -/

/-- `1 ≤ size n` in `ℝ` (the merged `Sizes.one_le_size`; RBM2D `AvgPins_one_le_size`). -/
private theorem flucThreshold_one_le_size (sz : Sizes d) (n : ℕ) :
    (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n

/-- `size^{-K} ≤ η_t` gives `η_t⁻¹ ≤ size^K` (RBM1D `etaInv_le_rpow_of_lowerN`,
`EnergyN/Gauss/DetFlucThreshold.lean:53`). -/
theorem flucThreshold_etaInv_le_rpow_of_lower (sz : Sizes d) {E t : ℕ → ℝ} {K : ℝ}
    (hη : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-K) ≤ etaT (E n) (t n)) :
    ∀ᶠ n : ℕ in atTop, (etaT (E n) (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ K := by
  filter_upwards [hη] with n hηn
  have hn : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    have := flucThreshold_one_le_size sz n
    linarith
  have hpow : 0 < ((sz.size n : ℕ) : ℝ) ^ (-K) := Real.rpow_pos_of_pos hn _
  have h := inv_anti₀ hpow hηn
  rw [Real.rpow_neg hn.le, inv_inv] at h
  exact h

/-- `size^{-K} ≤ η_t` (with `K ≥ 0`) makes `η_t⁻¹ + 1` a `PolyHi` function (RBM1D
`etaPolyHi_of_lowerN`, `EnergyN/Gauss/DetFlucThreshold.lean:66`). -/
theorem flucThreshold_etaPolyHi_of_lower (sz : Sizes d) {E t : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-K) ≤ etaT (E n) (t n)) :
    PolyHi sz.size (fun n => (etaT (E n) (t n))⁻¹ + 1) := by
  refine ⟨2, by norm_num, K, ?_⟩
  filter_upwards [flucThreshold_etaInv_le_rpow_of_lower sz hη] with n hInv
  have hn : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := flucThreshold_one_le_size sz n
  have hOne : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ K := Real.one_le_rpow hn hK
  linarith

/-! ### The good event at the threshold, from the local law -/

/-- **Statement of `highProbAt_detFlucDelta_of_localLaw`** (RBM2D `Green/FlucThreshold.lean:382`,
new there; in place of RBM1D `highProb_detFlucDelta_of_localLawN`,
`EnergyN/Gauss/DetFlucThreshold.lean:108`, which goes through a time net): the per-time good event
(4.1) at the threshold `detFlucDelta` has high probability.  Proof: the margin
`size^{θ/2} · detFlucControl ≤ detFlucDelta` (eventually), `Ψ ≤ detFlucControl`, `PerTimeDomAt` at
`τ = θ/2`, `D + 2`, and the union over the `size²` pairs (`#(Idx × Idx) = size²`,
`flucAvg_card_Idx_eq_size`; `size = (W L)^d`, so the union costs `N²` in every dimension). -/
theorem highProbAt_detFlucDelta_of_localLaw :
  ∀ (sz : Sizes d) {E t Ψ : ℕ → ℝ} {a θ : ℝ}, sz.SizeTendsto →
    0 < a → 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq sz E t Ψ →
    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤
        detFlucDelta sz Ψ θ n}) := by
  intro sz E t Ψ a θ hsz ha hθ0 hθa hθ1 hΨhi hll
  have hmargin := detFlucDelta_margin sz hsz ha hθ0 hθa hθ1 hΨhi
  -- `#(Idx × Idx) = size²` pairs
  have hcard : ∀ᶠ n : ℕ in atTop,
      (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) :=
    Filter.Eventually.of_forall fun n => by
      rw [Fintype.card_prod, flucAvg_card_Idx_eq_size, Real.rpow_two]
      push_cast
      rw [sq]
  -- one pair at a time: `PerTimeDomAt` at `τ = θ/2`, with the margin
  have hpair : ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
        (Sizes.seqP sz) ({ω : Sizes.SeqΩ sz |
            llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) p.1 p.2
              ≤ detFlucDelta sz Ψ θ n})ᶜ
          ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    intro D hD
    filter_upwards [hll (θ / 2) (half_pos hθ0) D hD, hmargin] with n hn hm p
    refine le_trans (measure_mono ?_) (hn ((), p.1, p.2))
    intro ω hω
    have hω' : detFlucDelta sz Ψ θ n
        < llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) p.1 p.2 :=
      not_le.1 hω
    have hle : ((sz.size n : ℕ) : ℝ) ^ (θ / 2) * Ψ n ≤ detFlucDelta sz Ψ θ n :=
      le_trans (mul_le_mul_of_nonneg_left (detFlucControl_ge_psi sz Ψ n)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hm
    exact lt_of_le_of_lt hle hω'
  have hpairs := highProbAt_iInter (Sizes.seqP sz) sz.size
    (K := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (Ξ := fun n p => {ω : Sizes.SeqΩ sz |
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) p.1 p.2
        ≤ detFlucDelta sz Ψ θ n})
    (C := 2) (by norm_num) hcard hpair
  exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono hpairs
    (Filter.Eventually.of_forall fun n ω hω i j => Set.mem_iInter.1 hω (i, j))

/-! ### The endpoint: the gain from the local law -/

/-- **Statement of `flucGain_of_localLaw`** (RBM1D `fixedMoment_gain_of_localLawN`,
`EnergyN/Gauss/DetFlucThreshold.lean:126`, with `fixedMoment_gain_of_goodSetFlowN`,
`EnergyN/Gauss/DetFlucAvg.lean:76`, per time): from the local law at the deterministic scale `Ψ`,
the gain `FlucGainUpTo'` at the time `t n` with `δ = detFlucDelta sz Ψ θ`,
`B = 2 (2 C_M (2δ) + 2δ)`, `ρ = 2 (2δ)`, for every pair of budgets `M, K`; and the `d`-dimensional
weight condition `W^{-d} ≤ ρ²` (the `c ≤ ρ²` of `integral_norm_flucAvg_pow_le_iter_budget` at the
bounded weight `c = W^{-d}`, `uniformWeight_blockAvg2`, `boundedWeight_svarF`).  The floor is the
paper's `W^{-d/2} ≤ Ψ` (`3_5:27`).  RBM2D `flucGain_of_localLaw` (`Green/FlucThreshold.lean:436`)
has the floor `W⁻¹ ≤ Ψ` and the conjunct `(W⁻¹)² ≤ ρ²`, which is false at `d = 3`
(`flucThreshold_literal_false`, paper-delta candidate `T2123a`).  Consumer: S1-30
(`fixedTimeFAThm`). -/
theorem flucGain_of_localLaw :
  ∀ (sz : Sizes d) {E t Ψ : ℕ → ℝ} {a Kη θ : ℝ}, sz.SizeTendsto →
    (∀ n, |E n| < 2) → (∀ n, t n < 1) →
    0 < a → 0 ≤ Kη → 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-Kη) ≤ etaT (E n) (t n)) →
    (∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq sz E t Ψ → ∀ M K : ℕ,
    (∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' sz n (t n) (zt (E n) (t n)) (mE (E n))
        (2 * (2 * minorDiffC M * (2 * detFlucDelta sz Ψ θ n) + 2 * detFlucDelta sz Ψ θ n))
        (2 * (2 * detFlucDelta sz Ψ θ n)) M K) ∧
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (2 * (2 * detFlucDelta sz Ψ θ n)) ^ 2) := by
  intro sz E t Ψ a Kη θ hsz hE ht1 ha hKη hθ0 hθa hθ1 hη hΨlo hΨhi hll M K
  have hΩ := highProbAt_detFlucDelta_of_localLaw sz hsz ha hθ0 hθa hθ1 hΨhi hll
  have hsmall := hsmall_of_highProb sz hsz hE ht1 (detFlucDelta_pos sz Ψ θ)
    (detFlucDelta_polyLo sz hsz hθ0.le) (flucThreshold_etaPolyHi_of_lower sz hKη hη) hΩ M K
  obtain ⟨hMδ, hδC⟩ := detFlucDelta_moment_small sz hsz ha hθ0.le hθa hθ1 hΨhi M
  refine ⟨?_, flucThreshold_W_pow_inv_le_detFlucDelta_sq sz hsz ha hθ0.le hΨlo hΨhi⟩
  filter_upwards [hMδ, hδC, hsmall] with n hMδn hδCn hsmalln
  have hΨ : (0 : ℝ) < 2 * detFlucDelta sz Ψ θ n := by linarith [detFlucDelta_pos sz Ψ θ n]
  have hcc : condCost (E n) (t n) M (2 * detFlucDelta sz Ψ θ n)
      (condEps (E n) (t n) M (2 * detFlucDelta sz Ψ θ n)) = 2 * detFlucDelta sz Ψ θ n :=
    condCost_condEps (hE n) (ht1 n) M hΨ
  have h := flucGainUpTo'_goodEvent (sz := sz) (E := E) (t := t) (δ := detFlucDelta sz Ψ θ)
    (n := n) (hE n) (ht1 n) (condEps_nonneg (hE n) (ht1 n) M hΨ.le)
    (detFlucDelta_pos sz Ψ θ n) (detFlucDelta_le_quarter sz Ψ θ n) hMδn
    (by rw [hcc]; exact hδCn) hsmalln
  rwa [hcc] at h

/-! ### The endpoint feeds the consumer (shape check) -/

section Consumer

/-- **The endpoint feeds the consumer**: at each large `n`, the first conjunct of
`flucGain_of_localLaw` (with `M = K = 2p`) is the `hg` of `integral_norm_flucAvg_pow_le_iter_budget`
at `u = t n`, and the second conjunct is its `hcρ : c ≤ ρ²` for the bounded weight
`(uniformWeight_blockAvg2 …).toBoundedWeight` (`c = W^{-d}`, `ρ = 2 (2 δ)`); the consumer's
`hρ1 : ρ ≤ 1` is `detFlucDelta_le_quarter`.  RBM2D `flucThreshold_check_consumer`
(`Green/FlucThreshold.lean:651`), with `UniformWeight` replaced by `BoundedWeight` (DECISIONS §30). -/
private theorem flucThreshold_check_consumer (sz : Sizes d) {E t Ψ : ℕ → ℝ} {a Kη θ : ℝ}
    (hsz : sz.SizeTendsto) (hE : ∀ n, |E n| < 2) (ht : ∀ n, t n < 1) (ha : 0 < a) (hK : 0 ≤ Kη)
    (hθ : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-Kη) ≤ etaT (E n) (t n))
    (hlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n)
    (hhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a))
    (hll : LocalLawDetSeq sz E t Ψ) (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ a' : Zd d (sz.L n),
      2 * p ≤ ((Finset.univ : Finset (Idx d (sz.L n) (sz.W n))).filter
        fun k => (split d (sz.L n) (sz.W n) k).1 = a').card →
      ∫ ω, ‖flucAvg sz n (t n) (zt (E n) (t n)) (mE (E n))
          (fun k : Idx d (sz.L n) (sz.W n) =>
            if (split d (sz.L n) (sz.W n) k).1 = a' then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0) ω‖
            ^ (2 * p) ∂(Sizes.seqP sz)
        ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
          * ((2 : ℝ) ^ (2 * p - 1) * (2 * (2 * detFlucDelta sz Ψ θ n)) *
              (2 * (2 * minorDiffC (2 * p) * (2 * detFlucDelta sz Ψ θ n)
                + 2 * detFlucDelta sz Ψ θ n))) ^ (2 * p) := by
  obtain ⟨h1, h2⟩ := flucGain_of_localLaw sz hsz hE ht ha hK hθ hθa hθ1 hη hlo hhi hll (2 * p)
    (2 * p)
  filter_upwards [h1, h2] with n hg hw a' hcard
  exact integral_norm_flucAvg_pow_le_iter_budget (hE n) (ht n) (u := t n) hg le_rfl le_rfl
    (by have := detFlucDelta_le_quarter sz Ψ θ n; linarith) hw
    (uniformWeight_blockAvg2 d (sz.L n) (sz.W n) a').toBoundedWeight hcard

end Consumer

/-! ### Compiled nonempty instances at `d = 3`

The data is the merged preflight sequence `sz0` (`RBM.Gauss.SizesInst`, `Defs/Sizes.lean:260`:
`L n = 4 (n + 1)`, `W n = (2 (n + 1))^5`, `N n = (W n L n)^3`; `n = 0`: `L = 4`, `W = 32`,
`N = 2097152`), the energy `E ≡ 0` (`m = i`), the control `Ψ n = W n^{-3/2}` (`= W^{-d/2}`: the
floor of `3_5:27` with equality), `a = 1/4` (`Ψ ≤ N^{-1/4}` is `N ≤ W^6`, `sz0_size_le_W_pow`),
`θ = detFlucTheta (1/4) 1 = 1/32`, `K_η = 1`, and the budgets `M = 1`, `K = 2`.

* Instance A: `t ≡ 1/2` (`η = 1/2`, `G_t ≠ m`, the flow is not collapsed).  What stays a hypothesis
  of the example is the local law `LocalLawDetSeq sz0 E t Ψ`: the output of the merged
  `localLawDetThm` from `AsGMcSeq` and `LoopDetSeq` (random premises of other gates).
* Instance B: `t ≡ 0` (`H = 0`, `G = m 1`): `LocalLawDetSeq` is the merged
  `localLawDetSeq_time_zero`, so no hypothesis is left (the flow is collapsed, so this is a
  complement to A, not a replacement).

Every conclusion is an eventual (`∀ᶠ n`) statement, as the theorems are. -/

section Instances

open RBM.Gauss.SizesInst

/-- The instance control `Ψ n = W n^{-3/2}` (the floor `W^{-d/2}` at `d = 3`, with equality). -/
private def flucThresholdPsi (n : ℕ) : ℝ := ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)

private theorem flucThreshold_inst_floor :
    ∀ᶠ n : ℕ in atTop, ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ flucThresholdPsi n :=
  Filter.Eventually.of_forall fun _ => le_rfl

/-- `Ψ n = W^{-3/2} ≤ N^{-1/4}`: `N^{1/4} ≤ (W^6)^{1/4} = W^{3/2}` (`sz0_size_le_W_pow`). -/
private theorem flucThreshold_inst_ceiling :
    ∀ᶠ n : ℕ in atTop, flucThresholdPsi n ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) :=
  Filter.Eventually.of_forall fun n => by
    have hN0 : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ) := by
      have := sz0.one_le_size n
      exact_mod_cast (by omega : 0 < sz0.size n)
    have hW0 : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos n
    have h : ((sz0.size n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by
      exact_mod_cast sz0_size_le_W_pow n
    have h1 : ((sz0.size n : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
      calc ((sz0.size n : ℕ) : ℝ) ^ (1 / 4 : ℝ)
          ≤ (((sz0.W n : ℕ) : ℝ) ^ 6) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) h (by norm_num)
        _ = ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
            norm_num
    unfold flucThresholdPsi
    rw [Real.rpow_neg hN0.le, show (-((3 : ℕ) : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num,
      Real.rpow_neg hW0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) h1

/-- `m^{(0)} = i`. -/
private theorem flucThreshold_inst_mE_zero : mE 0 = Complex.I := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  apply Complex.ext <;> simp [mE, hsqrt]

/-- `η_0 = 1` at `E = 0`. -/
private theorem flucThreshold_inst_etaT_zero : etaT 0 0 = 1 := by
  rw [etaT, flucThreshold_inst_mE_zero]; simp

/-- `η_{1/2} = 1/2` at `E = 0`. -/
private theorem flucThreshold_inst_etaT_half : etaT 0 (1 / 2) = 1 / 2 := by
  rw [etaT, flucThreshold_inst_mE_zero]; norm_num

/-- The `η` input at `t ≡ 1/2`, `K_η = 1`: `N^{-1} ≤ 1/2 = η_{1/2}` once `N ≥ 2`. -/
private theorem flucThreshold_inst_eta_half :
    ∀ᶠ n : ℕ in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT 0 (1 / 2) := by
  filter_upwards [sz0_tendsto.eventually_ge_atTop 2] with n hn
  rw [flucThreshold_inst_etaT_half, Real.rpow_neg_one]
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- The `η` input at `t ≡ 0`, `K_η = 0`: `N^{-0} = 1 ≤ η_0 = 1`. -/
private theorem flucThreshold_inst_eta_zero :
    ∀ᶠ n : ℕ in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-(0 : ℝ)) ≤ etaT 0 0 :=
  Filter.Eventually.of_forall fun n => by
    rw [neg_zero, Real.rpow_zero, flucThreshold_inst_etaT_zero]

private theorem flucThreshold_inst_theta :
    0 < detFlucTheta (1 / 4) 1 ∧ detFlucTheta (1 / 4) 1 ≤ 1 / 4 / 4 ∧
      detFlucTheta (1 / 4) 1 ≤ 1 / 4 := by
  obtain ⟨h0, h1, -, h3⟩ := detFlucTheta_specs (a := 1 / 4) (τ := 1) (by norm_num) one_pos
  exact ⟨h0, h1.le, h3⟩

private theorem flucThreshold_inst_hE (n : ℕ) : |(fun _ : ℕ => (0 : ℝ)) n| < 2 := by norm_num

/-- The local law at `t ≡ 0` (merged `localLawDetSeq_time_zero`). -/
private theorem flucThreshold_inst_ll_zero :
    LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 0) flucThresholdPsi :=
  localLawDetSeq_time_zero sz0 (fun _ => by norm_num)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **Instance of `detFlucDelta_polyLo`**: the threshold at `sz0`, `Ψ = W^{-3/2}`, `θ = 1/32` is
`PolyLo` in `N` (`C = 1`, `D = 4`). -/
private theorem flucThreshold_inst_polyLo :
    PolyLo sz0.size (detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1)) :=
  detFlucDelta_polyLo sz0 sz0_tendsto flucThreshold_inst_theta.1.le

/-- **Instance of `flucThreshold_etaPolyHi_of_lower`** at `t ≡ 1/2`: `η⁻¹ + 1` is `PolyHi`. -/
private theorem flucThreshold_inst_polyHi_half :
    PolyHi sz0.size (fun n => (etaT ((fun _ : ℕ => (0 : ℝ)) n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹ + 1) :=
  flucThreshold_etaPolyHi_of_lower sz0 zero_le_one flucThreshold_inst_eta_half

/-- **Instance of `detFlucControl_le_rpow`, `detFlucDelta_le_rpow`, `detFlucDelta_margin`,
`detFlucDelta_eventually_mul_le_one`, `detFlucDelta_moment_small`** at `sz0`, `Ψ = W^{-3/2}`,
`a = 1/4`, `θ = 1/32`. -/
private theorem flucThreshold_inst_bounds :
    (∀ᶠ n : ℕ in atTop, detFlucControl sz0 flucThresholdPsi n ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(min (1 / 4 : ℝ) 1))) ∧
    (∀ᶠ n : ℕ in atTop, detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n
      ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(min (1 / 4 / 2 : ℝ) 1))) ∧
    (∀ᶠ n : ℕ in atTop, ((sz0.size n : ℕ) : ℝ) ^ (detFlucTheta (1 / 4) 1 / 2) *
        detFlucControl sz0 flucThresholdPsi n
      ≤ detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n) ∧
    (∀ᶠ n : ℕ in atTop, 5 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n ≤ 1) ∧
    (∀ᶠ n : ℕ in atTop, 8 * ((1 : ℕ) : ℝ) * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n ≤ 1) ∧
    (∀ᶠ n : ℕ in atTop,
      2 * minorDiffC 1 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
        + 2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n ≤ 1) :=
  ⟨detFlucControl_le_rpow sz0 sz0_tendsto (by norm_num) flucThreshold_inst_ceiling,
   detFlucDelta_le_rpow sz0 sz0_tendsto (by norm_num) flucThreshold_inst_theta.1.le
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_ceiling,
   detFlucDelta_margin sz0 sz0_tendsto (by norm_num) flucThreshold_inst_theta.1
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_ceiling,
   detFlucDelta_eventually_mul_le_one sz0 sz0_tendsto (by norm_num) flucThreshold_inst_theta.1.le
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_ceiling
    (C := 5) (by norm_num),
   (detFlucDelta_moment_small sz0 sz0_tendsto (by norm_num) flucThreshold_inst_theta.1.le
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_ceiling 1).1,
   (detFlucDelta_moment_small sz0 sz0_tendsto (by norm_num) flucThreshold_inst_theta.1.le
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_ceiling 1).2⟩

/-- **Instance A of `highProbAt_detFlucDelta_of_localLaw`**: `t ≡ 1/2`, the local law kept as the
hypothesis; the per-time good event at the threshold has high probability. -/
private theorem flucThreshold_inst_highProb_half
    (hll : LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) flucThresholdPsi) :
    HighProbAt (Sizes.seqP sz0) sz0.size (fun n => {ω : Sizes.SeqΩ sz0 |
      ∀ i j : Idx 3 (sz0.L n) (sz0.W n),
        llErrMat 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (Sizes.seqHflow sz0 n (1 / 2) ω) i j ≤
          detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n}) :=
  highProbAt_detFlucDelta_of_localLaw sz0 (E := fun _ => 0) (t := fun _ => 1 / 2)
    (Ψ := flucThresholdPsi) (a := 1 / 4) (θ := detFlucTheta (1 / 4) 1) sz0_tendsto (by norm_num)
    flucThreshold_inst_theta.1 flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2
    flucThreshold_inst_ceiling hll

/-- **Instance B of `highProbAt_detFlucDelta_of_localLaw`**: `t ≡ 0`, no hypothesis left. -/
private theorem flucThreshold_inst_highProb_zero :
    HighProbAt (Sizes.seqP sz0) sz0.size (fun n => {ω : Sizes.SeqΩ sz0 |
      ∀ i j : Idx 3 (sz0.L n) (sz0.W n),
        llErrMat 3 (sz0.L n) (sz0.W n) 0 0 (Sizes.seqHflow sz0 n 0 ω) i j ≤
          detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n}) :=
  highProbAt_detFlucDelta_of_localLaw sz0 (E := fun _ => 0) (t := fun _ => 0)
    (Ψ := flucThresholdPsi) (a := 1 / 4) (θ := detFlucTheta (1 / 4) 1) sz0_tendsto (by norm_num)
    flucThreshold_inst_theta.1 flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2
    flucThreshold_inst_ceiling flucThreshold_inst_ll_zero

/-- **Instance of `measureReal_compl_le_of_polyLo`** at the `PolyLo` function
`detFlucDelta sz0 Ψ θ` and the good event of Instance A: its complement has probability at most
`δ n`, eventually. -/
private theorem flucThreshold_inst_measureReal
    (hll : LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) flucThresholdPsi) :
    ∀ᶠ n : ℕ in atTop, (Sizes.seqP sz0).real ({ω : Sizes.SeqΩ sz0 |
      ∀ i j : Idx 3 (sz0.L n) (sz0.W n),
        llErrMat 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (Sizes.seqHflow sz0 n (1 / 2) ω) i j ≤
          detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n})ᶜ
      ≤ detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n :=
  measureReal_compl_le_of_polyLo (Sizes.seqP sz0) sz0.size sz0_tendsto
    (flucThreshold_inst_highProb_half hll) flucThreshold_inst_polyLo

/-- **Instance A of `hsmall_of_highProb`** at `M = 1`, `K = 2`, `E ≡ 0`, `t ≡ 1/2` (`η = 1/2`),
`δ = detFlucDelta sz0 Ψ (detFlucTheta (1/4) 1)`: every deterministic hypothesis is discharged;
the local law is the kept hypothesis. -/
private theorem flucThreshold_inst_hsmall_half
    (hll : LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) flucThresholdPsi) :
    ∀ᶠ n : ℕ in atTop,
      condEnv 0 (1 / 2) 1 ^ 2 * (Sizes.seqP sz0).real (badTower sz0 n
          (condEps 0 (1 / 2) 1 (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n))
          (badBase sz0 (fun _ => 0) (fun _ => 1 / 2)
            (detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1)) n) (1 + 1))
        ≤ (2 * minorDiffC 1 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
            + condCost 0 (1 / 2) 1
              (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
              (condEps 0 (1 / 2) 1
                (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n))) ^ 2
          * (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) ^ (2 * 1) :=
  hsmall_of_highProb sz0 (E := fun _ => 0) (t := fun _ => 1 / 2)
    (δ := detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1)) sz0_tendsto
    flucThreshold_inst_hE (fun _ => by norm_num)
    (detFlucDelta_pos sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1)) flucThreshold_inst_polyLo
    flucThreshold_inst_polyHi_half (flucThreshold_inst_highProb_half hll) 1 2

/-- **Instance B of `hsmall_of_highProb`** at `M = 1`, `K = 2`, `E ≡ 0`, `t ≡ 0`: no hypothesis
left (the local law is `localLawDetSeq_time_zero`). -/
private theorem flucThreshold_inst_hsmall_zero :
    ∀ᶠ n : ℕ in atTop,
      condEnv 0 0 1 ^ 2 * (Sizes.seqP sz0).real (badTower sz0 n
          (condEps 0 0 1 (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n))
          (badBase sz0 (fun _ => 0) (fun _ => 0)
            (detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1)) n) (1 + 1))
        ≤ (2 * minorDiffC 1 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
            + condCost 0 0 1
              (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
              (condEps 0 0 1
                (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n))) ^ 2
          * (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) ^ (2 * 1) :=
  hsmall_of_highProb sz0 (E := fun _ => 0) (t := fun _ => 0)
    (δ := detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1)) sz0_tendsto
    flucThreshold_inst_hE (fun _ => by norm_num)
    (detFlucDelta_pos sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1)) flucThreshold_inst_polyLo
    (flucThreshold_etaPolyHi_of_lower sz0 le_rfl flucThreshold_inst_eta_zero)
    flucThreshold_inst_highProb_zero 1 2

/-- **Instance A of `flucGain_of_localLaw`** at `M = 1`, `K = 2`, `E ≡ 0`, `t ≡ 1/2`,
`Ψ = W^{-3/2}`, `a = 1/4`, `K_η = 1`, `θ = detFlucTheta (1/4) 1`: both conjuncts, every
deterministic hypothesis discharged; the local law is the kept hypothesis. -/
private theorem flucThreshold_inst_flucGain_half
    (hll : LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) flucThresholdPsi) :
    (∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' sz0 n (1 / 2) (zt 0 (1 / 2)) (mE 0)
        (2 * (2 * minorDiffC 1 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
          + 2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n))
        (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) 1 2) ∧
    (∀ᶠ n : ℕ in atTop, (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹
      ≤ (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) ^ 2) :=
  flucGain_of_localLaw sz0 (E := fun _ => 0) (t := fun _ => 1 / 2) (Ψ := flucThresholdPsi)
    (a := 1 / 4) (Kη := 1) (θ := detFlucTheta (1 / 4) 1) sz0_tendsto flucThreshold_inst_hE
    (fun _ => by norm_num) (by norm_num) zero_le_one flucThreshold_inst_theta.1
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_eta_half
    flucThreshold_inst_floor flucThreshold_inst_ceiling hll 1 2

/-- **Instance B of `flucGain_of_localLaw`** at `M = 1`, `K = 2`, `E ≡ 0`, `t ≡ 0`
(`η = 1`, `K_η = 0`): both conjuncts, no hypothesis left. -/
private theorem flucThreshold_inst_flucGain_zero :
    (∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' sz0 n 0 (zt 0 0) (mE 0)
        (2 * (2 * minorDiffC 1 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
          + 2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n))
        (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) 1 2) ∧
    (∀ᶠ n : ℕ in atTop, (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹
      ≤ (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) ^ 2) :=
  flucGain_of_localLaw sz0 (E := fun _ => 0) (t := fun _ => 0) (Ψ := flucThresholdPsi)
    (a := 1 / 4) (Kη := 0) (θ := detFlucTheta (1 / 4) 1) sz0_tendsto flucThreshold_inst_hE
    (fun _ => by norm_num) (by norm_num) le_rfl flucThreshold_inst_theta.1
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_eta_zero
    flucThreshold_inst_floor flucThreshold_inst_ceiling flucThreshold_inst_ll_zero 1 2

/-- **Instances of the closure lemmas** `PolyLo.mono/mul/pow/div/inv`, `PolyHi.mono/mul/add/pow/inv`
at the threshold `δ` (`PolyLo`) and `η⁻¹ + 1` at `t ≡ 1/2` (`PolyHi`). -/
private theorem flucThreshold_inst_poly :
    PolyLo sz0.size (fun n => detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n
      * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n) ∧
    PolyLo sz0.size (fun n => detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n ^ 3) ∧
    PolyLo sz0.size (fun n => detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n
      / ((etaT 0 (1 / 2))⁻¹ + 1)) ∧
    PolyLo sz0.size (fun _ => ((etaT 0 (1 / 2))⁻¹ + 1)⁻¹) ∧
    PolyLo sz0.size (fun _ => (1 / 2 : ℝ)) ∧
    PolyHi sz0.size (fun n => (detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)⁻¹) ∧
    PolyHi sz0.size (fun _ => ((etaT 0 (1 / 2))⁻¹ + 1) * ((etaT 0 (1 / 2))⁻¹ + 1)) ∧
    PolyHi sz0.size (fun _ => ((etaT 0 (1 / 2))⁻¹ + 1) + ((etaT 0 (1 / 2))⁻¹ + 1)) ∧
    PolyHi sz0.size (fun _ => ((etaT 0 (1 / 2))⁻¹ + 1) ^ 2) ∧
    PolyHi sz0.size (fun _ => (3 : ℝ)) := by
  have hδ := flucThreshold_inst_polyLo
  have hη : PolyHi sz0.size (fun _ : ℕ => (etaT 0 (1 / 2))⁻¹ + 1) := flucThreshold_inst_polyHi_half
  have hη0 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (etaT 0 (1 / 2))⁻¹ + 1 :=
    Filter.Eventually.of_forall fun _ => by
      rw [flucThreshold_inst_etaT_half]; norm_num
  have hηpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (etaT 0 (1 / 2))⁻¹ + 1 :=
    Filter.Eventually.of_forall fun _ => by
      rw [flucThreshold_inst_etaT_half]; norm_num
  refine ⟨PolyLo.mul sz0_tendsto hδ hδ, PolyLo.pow sz0_tendsto hδ 3,
    PolyLo.div sz0_tendsto hδ hη hηpos, PolyLo.inv sz0_tendsto hη hηpos,
    polyLo_const (by norm_num), PolyHi.inv sz0_tendsto hδ,
    PolyHi.mul sz0_tendsto hη hη hη0 hη0, PolyHi.add sz0_tendsto hη hη,
    PolyHi.pow sz0_tendsto hη hη0 2, polyHi_const (by norm_num)⟩

/-- `W^{-3/2} ≤ W⁻¹ / 181` for `W ≥ 32761 = 181²`: `W^{-3/2} = W⁻¹ W^{-1/2}` and `W^{1/2} ≥ 181`. -/
private theorem flucThreshold_neg_aux {W : ℝ} (hW : 32761 ≤ W) :
    W ^ (-((3 : ℕ) : ℝ) / 2) ≤ W⁻¹ / 181 := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hsq : (181 : ℝ) ≤ W ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hsqpos : (0 : ℝ) < W ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have h1 : W ^ (-((3 : ℕ) : ℝ) / 2) = W⁻¹ * (W ^ (1 / 2 : ℝ))⁻¹ := by
    rw [show (-((3 : ℕ) : ℝ) / 2) = -1 + -(1 / 2 : ℝ) by norm_num, Real.rpow_add hW0,
      Real.rpow_neg_one, Real.rpow_neg hW0.le]
  rw [h1]
  have hinv : (W ^ (1 / 2 : ℝ))⁻¹ ≤ 1 / 181 := by
    rw [inv_le_comm₀ hsqpos (by norm_num)]; linarith
  calc W⁻¹ * (W ^ (1 / 2 : ℝ))⁻¹ ≤ W⁻¹ * (1 / 181) :=
        mul_le_mul_of_nonneg_left hinv (inv_nonneg.2 hW0.le)
    _ = W⁻¹ / 181 := by ring

/-- At `n = 3` (`W = 2^15`, `N = 2^57`) the threshold is at most `4 Ψ`: `(N + 4)^{1/32} ≤ 4` and the
control floor `(N + 4)^{-2} ≤ Ψ = W^{-3/2}`. -/
private theorem flucThreshold_delta3_le :
    detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3 ≤ 4 * flucThresholdPsi 3 := by
  have hW : ((sz0.W 3 : ℕ) : ℝ) = 32768 := by norm_num [sz0]
  have hN : ((sz0.size 3 : ℕ) : ℝ) = 2 ^ 57 := by norm_num [Sizes.size, sz0]
  have hθ : detFlucTheta (1 / 4) 1 = 1 / 32 := by norm_num [detFlucTheta]
  have hΨ : flucThresholdPsi 3 = (32768 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) := by
    unfold flucThresholdPsi; rw [hW]
  have hfloor : (((sz0.size 3 : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)) ≤ flucThresholdPsi 3 := by
    rw [hN, hΨ]
    have h1 : (32768 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ 57 + 4 := by
      calc (32768 : ℝ) ^ (3 / 4 : ℝ) ≤ 32768 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ 2 ^ 57 + 4 := by norm_num
    have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 32768 ^ (3 / 4 : ℝ)) h1
      (by norm_num : -(2 : ℝ) ≤ 0)
    refine h2.trans (le_of_eq ?_)
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have hpow : (((sz0.size 3 : ℕ) : ℝ) + 4) ^ (1 / 32 : ℝ) ≤ 4 := by
    rw [hN]
    calc ((2 : ℝ) ^ 57 + 4) ^ (1 / 32 : ℝ) ≤ ((4 : ℝ) ^ 32) ^ (1 / 32 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
      _ = 4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hΨ0 : (0 : ℝ) ≤ flucThresholdPsi 3 := by
    unfold flucThresholdPsi; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold detFlucDelta
  rw [hθ]
  refine (min_le_right _ _).trans ?_
  rw [max_eq_left hfloor]
  exact mul_le_mul_of_nonneg_right hpow hΨ0

/-- `Ψ 3 = W^{-3/2} ≤ (2^15)⁻¹ / 181`. -/
private theorem flucThreshold_psi3_le : flucThresholdPsi 3 ≤ (32768 : ℝ)⁻¹ / 181 := by
  have hW : ((sz0.W 3 : ℕ) : ℝ) = 32768 := by norm_num [sz0]
  unfold flucThresholdPsi
  rw [hW]
  exact flucThreshold_neg_aux (by norm_num)

/-- **The RBM2D weight conjunct is false at `d = 3` under the pin floor** (paper-delta candidate
`T2123a`).  RBM2D's `(W⁻¹)² ≤ (2 (2 δ))²` (from `W⁻¹ ≤ Ψ`) is not implied by the pin's floor
`W^{-d/2} ≤ Ψ`: at `sz0`, `Ψ = W^{-3/2}` (which satisfies every hypothesis of
`flucGain_of_localLaw`, Instances A and B above) and `n = 3` (`W = 2^15`, `N = 2^57`), the
conjunct fails: `4 δ ≤ 16 W^{-3/2} ≤ 16 W⁻¹ / 181 < W⁻¹`, with `δ ≤ (N + 4)^{1/32} W^{-3/2}` and
`(N + 4)^{1/32} ≤ 4`. -/
private theorem flucThreshold_literal_false :
    ¬ ((((sz0.W 3 : ℕ) : ℝ))⁻¹ ^ 2 ≤
      (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3)) ^ 2) := by
  intro h
  have hW : ((sz0.W 3 : ℕ) : ℝ) = 32768 := by norm_num [sz0]
  have hδ := flucThreshold_delta3_le
  have hΨ := flucThreshold_psi3_le
  have hδ0 := detFlucDelta_pos sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3
  rw [hW] at h
  have h4 : (32768 : ℝ)⁻¹ ≤ 2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3) :=
    le_of_sq_le_sq (by linarith) (by positivity)
  norm_num at h4 hΨ
  linarith

/-- **The two smallness conditions of `flucGainUpTo'_goodEvent` at `M = 1`, at the slice `n = 3`**
of the instance sequence (`δ ≤ 4 W^{-3/2} < 7 · 10⁻⁷`, `minorDiffC 1 = 2^17`): `8 M δ ≤ 1` and
`2 C_1 (2 δ) + 2 δ ≤ 1` (`hB1` at `condCost = 2 δ`).  This compiles one slice of the eventual
statements of `detFlucDelta_moment_small` (Instance `flucThreshold_inst_bounds`); that they hold
for every `n ≥ 3` at `M = 1` is the numerical monotonicity check of the prove report (a) row 10,
not compiled here. -/
private theorem flucThreshold_inst_slice3 :
    8 * ((1 : ℕ) : ℝ) * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3 ≤ 1 ∧
    2 * minorDiffC 1 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3)
      + 2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3 ≤ 1 := by
  have hδ := flucThreshold_delta3_le
  have hΨ := flucThreshold_psi3_le
  rw [MinorDiffCondInst.inst_minorDiffC_one]
  norm_num at hΨ ⊢
  constructor <;> linarith

end Instances

end RBM.Green
