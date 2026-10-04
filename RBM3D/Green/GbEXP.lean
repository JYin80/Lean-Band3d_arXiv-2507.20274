/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.FlucThreshold
import RBM3D.Green.IBPRem
import RBM3D.Green.LocalLaw
import RBM3D.Induction.Step1

/-!
# `lem_GbEXP` for every size sequence at `d ≥ 3`: the fixed-time fluctuation averaging, the IBP
display and `gbEXPV3` (ST-1, S1-30)

Ticket T2126, the last ticket of the stochastic layer ST-1.  Port of `RBM2D/Green/FlucAvgDet.lean`
(623 lines, 524 kept), `RBM2D/Green/IBPDet.lean` (335, 287 kept) and `RBM2D/Green/GbEXP.lean`
(111, 59 kept) at RBM2D commit `c9a24cf` (cited `FlucAvgDet:line`, `IBPDet:line`, `GbEXP:line`),
to `d ≥ 3`, with the renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md` (`d : Sizes` becomes
`sz : Sizes d`; `Idx L W`, `Z2 L`, `BlockIndex L W` become `Idx d L W`, `Zd d L`, `Vtx d L W`;
`W²`, `W⁻²`, `(W L)²` become `W^d`, `W^{-d}`, `sz.size n = (W L)^d`; `spectralZ`, `spectralM`
become `zt`, `mE`) on the merged vocabulary of
`Green/{LocalLaw, FlucThreshold, FlucIterGain, IBPRem, CondDom, EntryDom, LDE, FlucVanish, Pins}`.
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem_GbEXP`
(`3_5:14-40`), `(GiiGEX)` (`3_5:21`), `(GijGEX)` (`3_5:24`), `(initialGT2)` (`3_5:28-30`, with the
window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` at `3_5:27`), `(GavLGEX)` (`3_5:33`); the proof is "that of
Lemma 4.1 in [YY_25]" (`3_5:37`).  The fixed-time fluctuation averaging is the display `jasdu`
(`Acta:4571`, weights `0 ≤ |t_k| ≤ W^{-1}`, `∑|t_k| ≤ 1`: in `d` dimensions `W^{-d}`, a
`BoundedWeight`) and the integration-by-parts displays are `Acta:4577, 4587` of
`../RBM1D/paper/Acta_revision_final.tex`.

The route (RBM2D T2171): `LocalLawDetSeq sz E t Ψ` gives, through `flucGain_of_localLaw`
(`Green/FlucThreshold.lean`), the gain `FlucGainUpTo'` with `ρ = 4 δ`, `δ = detFlucDelta Ψ θ`, and
the weight condition `W^{-d} ≤ ρ²`; the moment bound `integral_norm_flucAvg_pow_le_iter_budget` at
the budgets `M = K = 2p` for the two weight families (row `svarF`, block `W^{-d} 1(k ∈ 𝓘_a)`) and
Markov (`perTimeDomAt_of_moment`) give `‖flucAvg‖ ≺ 4 δ²`; the choice
`θ = detFlucTheta a τ < τ/16` turns it into `≺ Ψ²`; the bridge `splitEquiv` carries it to the
block-product index of the pin (`fixedTimeFAThm`).  The IBP display: `perTimeDomAt_ibpRem`
(`Green/IBPRem.lean`) and the union over the `size` sites `k` (`IBPDet_weighted_of_rem`) give
`≺ Ψ²`, then the same bridge (`ibpDetThm`).  `gbEXPV3` is `LocalLaw_gbEXPV3Theorem_of_fa_ibp`
(`Green/LocalLaw.lean`) with these two.

## Contents (namespace `RBM.Green`)

1. the threshold against `Ψ` (floor chain `FlucAvgDet_floor_le`, `detFlucDelta ≤ size^{2θ} Ψ`,
   `size^{τ/2}·4δ² ≤ size^τ Ψ²`: private);
2.-4. `FlucAvgDet_iter_budget_eventually`, `FlucAvgDet_family`, `FlucAvgDet_budgetFamily_absorb`,
   `FlucAvgDet_weighted`;
5. the bridge `FlucAvgDet_greenBlk_true_apply`, `_greenBlk_sub_eq`, `_condDiagBlk_eq`,
   `_row_sum_eq`, `_blk_sum_eq`, `_ibp_sum_eq`, `FlucAvgDet_perTime_reindex`;
6. `fixedTimeFAThm`; 7.-8. `IBPDet_norm_condExpDiag_sub_le_two_phi`, `IBPDet_weighted_of_rem`,
   `IBPDet_hEnv`, `IBPDet_hΨ1`; 9. `ibpDetThm`;
10. `gbEXPV3`, `stGbEXP_holds`, `stStep1_holds` (new: the ST forms of the pins);
11. compiled nonempty instances at `d = 3`.

## Differences from RBM2D (every other ported statement equals RBM2D's after the renaming)

* **The floor** is the paper's `W^{-d/2} ≤ Ψ` (`3_5:27`, D213; the floor of the pins
  `FixedTimeFAThm`, `IBPDetThm`, `LocalLaw.lean:176, 186`), not RBM2D's `W⁻¹ ≤ Ψ`: at
  `Ψ = W^{-3/2}` the latter fails (`gbEXP_W_inv_not_le_psi`).  The regularising floor
  `(N + 4)^{-2} ≤ Ψ` follows from `W^d ≤ N = (W L)^d` (`FlucAvgDet_floor_le`, every `d`; RBM2D
  used `W ≤ size`, `W_le_self`, which needs `1 ≤ d`), and `W^{-d} ≤ Ψ²` is `(W^{-d/2})² = W^{-d}`;
  RBM2D's `IBPDet_hΨlow` (`size^{-1} ≤ Ψ²` from `W⁻¹ ≤ Ψ`) is replaced by the merged
  `IBPRem_hΨlow_of_floor` (floor `W^{-d/2}`, `B = 1`).
* **Weights and counts** (DECISIONS §30, D192): the row `j ↦ S_{ij}` is a `BoundedWeight` with
  `c = W^{-d}` on `#A = (2d + 1) W^d` sites (`boundedWeight_svarF`; RBM2D `uniformWeight_svar`,
  `c = (5 W²)⁻¹`, `#A = 5 W²`, is false at `d ≥ 3`), the block family is uniform, hence bounded,
  with `c = W^{-d}`, `#A = W^d`; the hypothesis `c ≤ ρ²` is the second conjunct
  `(W^d)⁻¹ ≤ (2 (2 δ))²` of `flucGain_of_localLaw`; `hcW : cw n ≤ (W^d)⁻¹` replaces
  `cw n ≤ (W⁻¹)²`.  The diagonal coefficient is `S_ii = W^{-d} (1 + 2 d g²)⁻¹ ≤ W^{-d}`
  (`svarF_diag`).
* **`hd`** (D200): `fixedTimeFAThm` and `ibpDetThm` take `1 ≤ d`: `2 p ≤ #A` uses `W ≤ W^d`, and
  `perTimeDomAt_ibpRem` carries `hd`; `gbEXPV3`, `stGbEXP_holds`, `stStep1_holds` take `3 ≤ d`
  (`localLawDetThm`, D201).
* **The bridge**: the pins are on `Vtx d L W` with `svar`, `blkCoef2`, `greenBlk`; RBM2D's
  `Sblk2_eq_svar` is the private `FlucAvgDet_svar_eq_svarF` (`svarF_eq_svar` and
  `split ∘ splitEquiv.symm = id`); `FlucAvgDet_greenBlk_true_apply` concludes with `green` (the
  merged `entryDom_greenBlk_apply` is the private `Gres` form).
* Not ported: the private `Checks` and the `#print axioms` of RBM2D (replaced by the instances of
  section 11), `IBPDet_hΨlow` (see above).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The threshold against `Ψ` (RBM1D `Gauss/DetFlucAvgComplete.lean`) -/

/-- `Tendsto sz.size` from `SizeTendsto` (copy of the private `tendsto_size_of'`). -/
private theorem FlucAvgDet_tendsto_size {d : ℕ} {sz : Sizes d} (hsz : sz.SizeTendsto) :
    Tendsto sz.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp hsz

/-- **The regularising floor is below the pin floor.**  `W^d ≤ (W L)^d = N` (`L ≥ 1`, every `d`),
so `(N + 4)^{-2} ≤ W^{-d/2}`; the pin floor `W^{-d/2} ≤ Ψ` (`3_5:27`) then gives
`(N + 4)^{-2} ≤ Ψ`.  RBM2D used `W ≤ size` with the floor `W⁻¹ ≤ Ψ`. -/
private theorem FlucAvgDet_floor_le {d : ℕ} (sz : Sizes d) {Ψ : ℕ → ℝ} {n : ℕ}
    (h : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) :
    (((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)) ≤ Ψ n := by
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
  exact hfloor.trans h

/-- Real-variable core of RBM1D `detFlucDelta_le_rpow_mul_psi` (`x` is the size): once the
regularising floor `(x + 4)^{-2}` of the threshold is below `ψ`, the remaining loss is at most
`x^{2θ}` (`x + 4 ≤ x²` for `x ≥ 4`). -/
private theorem FlucAvgDet_delta_le_core {x ψ θ : ℝ} (hθ : 0 ≤ θ) (hx : 4 ≤ x)
    (hfloor : (x + 4) ^ (-(2 : ℝ)) ≤ ψ) :
    min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ)))) ≤ x ^ (2 * θ) * ψ := by
  have hn0 : (0 : ℝ) < x := by linarith
  have hmax : max ψ ((x + 4) ^ (-(2 : ℝ))) = ψ := max_eq_left hfloor
  have hψ0 : 0 ≤ ψ := le_trans (Real.rpow_nonneg (by linarith) _) hfloor
  have hN2 : x + 4 ≤ x ^ (2 : ℕ) := by nlinarith
  have hpow : (x + 4) ^ θ ≤ x ^ (2 * θ) := by
    calc (x + 4) ^ θ ≤ (x ^ (2 : ℕ)) ^ θ := Real.rpow_le_rpow (by positivity) hN2 hθ
      _ = x ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        ring_nf
  calc min (1 / 4 : ℝ) ((x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))))
      ≤ (x + 4) ^ θ * max ψ ((x + 4) ^ (-(2 : ℝ))) := min_le_right _ _
    _ = (x + 4) ^ θ * ψ := by rw [hmax]
    _ ≤ x ^ (2 * θ) * ψ := mul_le_mul_of_nonneg_right hpow hψ0

/-- Once the bandwidth scale is reached, the floor in the threshold is below `Ψ`; the remaining
loss is at most `size^{2θ}` (RBM1D `detFlucDelta_le_rpow_mul_psi`,
`Gauss/DetFlucAvgComplete.lean:21`, with the floor `W^{-d/2} ≤ Ψ`). -/
private theorem FlucAvgDet_detFlucDelta_le_rpow_mul_psi {d : ℕ} (sz : Sizes d)
    (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) :
    ∀ᶠ n : ℕ in atTop, detFlucDelta sz Ψ θ n ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * θ) * Ψ n := by
  filter_upwards [hΨlo, hsz.eventually_ge_atTop 4] with n hΨn hn4
  exact FlucAvgDet_delta_le_core hθ hn4 (FlucAvgDet_floor_le sz hΨn)

/-- Real-variable core of RBM1D `detFlucDelta_scale_absorb` (dimension-free). -/
private theorem FlucAvgDet_scale_absorb_core {x ψ δ τ θ : ℝ} (hθτ : θ ≤ τ / 16)
    (hx1 : 1 ≤ x) (h4 : 4 ≤ x ^ (τ / 4)) (hδ0 : 0 ≤ δ) (hδ : δ ≤ x ^ (2 * θ) * ψ) :
    x ^ (τ / 2) * (4 * δ ^ 2) ≤ x ^ τ * ψ ^ 2 := by
  have hn0 : (0 : ℝ) < x := by linarith
  have hsq : δ ^ 2 ≤ (x ^ (2 * θ) * ψ) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have hPowExp : x ^ (4 * θ) ≤ x ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpow2 : (x ^ (2 * θ)) ^ 2 = x ^ (4 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    ring_nf
  have hΨsq : 0 ≤ ψ ^ 2 := sq_nonneg _
  calc x ^ (τ / 2) * (4 * δ ^ 2)
      = 4 * x ^ (τ / 2) * δ ^ 2 := by ring
    _ ≤ 4 * x ^ (τ / 2) * ((x ^ (2 * θ) * ψ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 * x ^ (τ / 2) * x ^ (4 * θ) * ψ ^ 2 := by rw [mul_pow, hpow2]; ring
    _ ≤ 4 * x ^ (τ / 2) * x ^ (τ / 4) * ψ ^ 2 := by gcongr
    _ ≤ x ^ (τ / 4) * x ^ (τ / 2) * x ^ (τ / 4) * ψ ^ 2 := by gcongr
    _ = x ^ τ * ψ ^ 2 := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, show τ / 4 + τ / 2 + τ / 4 = τ by ring]

/-- Absorb the movable threshold's polynomial loss with half of the requested
stochastic-domination tolerance (RBM1D `detFlucDelta_scale_absorb`,
`Gauss/DetFlucAvgComplete.lean:62`). -/
private theorem FlucAvgDet_detFlucDelta_scale_absorb {d : ℕ} (sz : Sizes d)
    (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {τ θ : ℝ} (hτ : 0 < τ) (hθ0 : 0 ≤ θ) (hθτ : θ ≤ τ / 16)
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) :
    ∀ᶠ n : ℕ in atTop,
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (4 * detFlucDelta sz Ψ θ n ^ 2) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 := by
  filter_upwards [FlucAvgDet_detFlucDelta_le_rpow_mul_psi sz hsz hθ0 hΨlo,
    (FlucAvgDet_tendsto_size hsz).eventually (eventually_le_rpow 4 (by linarith : 0 < τ / 4))]
    with n hδ h4
  exact FlucAvgDet_scale_absorb_core hθτ (by exact_mod_cast sz.one_le_size n) h4
    (detFlucDelta_pos sz Ψ θ n).le hδ

/-! ## 2. The moment bound gives `≺` (RBM1D `unifDomIcc_flucAvg_iter_budget_eventuallyN`) -/

/-- **The `2p`-th moment of the fluctuation average gives `‖flucAvg‖ ≺ ρ B`, per time** (RBM1D
`unifDomIcc_flucAvg_iter_budget_eventuallyN`, `EnergyN/Gauss/DetFlucAvgComplete.lean:52`; RBM2D
`FlucAvgDet_iter_budget_eventually`, `Green/FlucAvgDet.lean:156`): the gain `FlucGainUpTo'` at the
budgets `M = K = 2p` with `B_p ≤ K_p B_m` and `ρ = ep`, a bounded weight `c ≤ ρ²` on a set with
`2 p ≤ #A` eventually (DECISIONS §30: the RBM2D `UniformWeight` is `BoundedWeight` here), and
Markov (`perTimeDomAt_of_moment`, where the size-index `n` carries `size n` in every power). -/
theorem FlucAvgDet_iter_budget_eventually {d : ℕ} {sz : Sizes d} (hsz : sz.SizeTendsto)
    {E t : ℕ → ℝ} {V : ℕ → Type*} (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1)
    {Tw : ∀ n, V n → Idx d (sz.L n) (sz.W n) → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ n, V n → Finset (Idx d (sz.L n) (sz.W n))}
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' sz n (t n) (zt (E n) (t n)) (mE (E n)) (Bp p n) (ep n)
        (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ n, 0 ≤ Bm n)
    (hBK : ∀ p n, Bp p n ≤ Kp p * Bm n)
    (hpos : ∀ n, 0 < ep n * Bm n) (hρ1 : ∀ n, ep n ≤ 1)
    (hcρ : ∀ᶠ n : ℕ in atTop, cw n ≤ ep n ^ 2)
    (hw : ∀ n (a : V n), BoundedWeight (Tw n a) (cw n) (Aw n a))
    (hcardA : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ a : V n, 2 * p ≤ (Aw n a).card) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n (a : V n) ω =>
        ‖flucAvg sz n (t n) (zt (E n) (t n)) (mE (E n)) (Tw n a) ω‖)
      (fun n _ _ => ep n * Bm n) := by
  refine perTimeDomAt_of_moment (FlucAvgDet_tendsto_size hsz) (fun n _ => hpos n)
    (fun p n a => ?_) ?_
  · exact integrable_norm_flucAvg_pow (flucBound_env (hE n) (ht1 n) sz n (t n)).flucDiag_le p
  · intro ε hε p
    have hK0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) :=
      pow_nonneg (mul_nonneg (by positivity) (hKp p)) _
    have hc1 : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) := by positivity
    have hcoef : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) := mul_nonneg hc1 hK0
    refine ⟨((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
      * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) + 1, by linarith, ?_⟩
    filter_upwards [hcardA p, hg p, hcρ] with n h2 hgn hcρn a
    have hmain := integral_norm_flucAvg_pow_le_iter_budget (p := p) (hE n) (ht1 n) (u := t n)
      hgn le_rfl le_rfl (hρ1 n) hcρn (hw n a) (h2 a)
    have hep0 : (0 : ℝ) ≤ ep n := hgn.rho_nonneg
    have hBp0 : (0 : ℝ) ≤ Bp p n := hgn.B_nonneg
    have hstep1 : ((2 : ℝ) ^ (2 * p - 1) * ep n * Bp p n) ^ (2 * p)
        ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep n * Bm n) ^ (2 * p) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc (2 : ℝ) ^ (2 * p - 1) * ep n * Bp p n
          ≤ (2 : ℝ) ^ (2 * p - 1) * ep n * (Kp p * Bm n) :=
            mul_le_mul_of_nonneg_left (hBK p n) (by positivity)
        _ = ((2 : ℝ) ^ (2 * p - 1) * Kp p) * (ep n * Bm n) := by ring
    have hmain2 : ∫ ω, ‖flucAvg sz n (t n) (zt (E n) (t n)) (mE (E n)) (Tw n a) ω‖
          ^ (2 * p) ∂(Sizes.seqP sz)
        ≤ (((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
            * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p)) * (ep n * Bm n) ^ (2 * p) := by
      refine le_trans hmain ?_
      calc ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * ep n * Bp p n) ^ (2 * p)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * (((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep n * Bm n) ^ (2 * p)) :=
            mul_le_mul_of_nonneg_left hstep1 hc1
        _ = _ := by ring
    have hNe : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) (by positivity)
    have hpow : (0 : ℝ) ≤ (ep n * Bm n) ^ (2 * p) :=
      pow_nonneg (mul_nonneg hep0 (hBm n)) _
    simp only [abs_norm]
    refine le_trans hmain2 ?_
    nlinarith [mul_nonneg hcoef hpow, hpow, hNe, hcoef]

/-! ## 3. The family at the threshold `δ = detFlucDelta` (RBM1D `fixedMoment_flucAvg_budget_familyN`) -/

/-- **The fluctuation average is `≺ 4 δ²` at the movable threshold** (RBM1D
`fixedMoment_flucAvg_budget_familyN`, `EnergyN/Gauss/DetFlucAvgComplete.lean:117`; RBM2D
`FlucAvgDet_family`, `Green/FlucAvgDet.lean:224`).  The gain comes from the local law
(`flucGain_of_localLaw`) with the budgets `M = K = 2p`, `B_p = (8 C_{2p} + 4) δ`, `ρ = 4 δ`; the
weight condition `c ≤ ρ²` is its second conjunct, `(W^d)⁻¹ ≤ (2 (2 δ))²`, with `c ≤ (W^d)⁻¹`
(row: `c = W^{-d}`, `#A = (2d + 1) W^d`; block: `c = W^{-d}`, `#A = W^d`; RBM2D `W⁻²`, `5 W²`,
`W²`). -/
theorem FlucAvgDet_family {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E t Ψ : ℕ → ℝ}
    {a Kη θ : ℝ}
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (ha : 0 < a) (hKη : 0 ≤ Kη)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-Kη) ≤ etaT (E n) (t n))
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a))
    (hll : LocalLawDetSeq sz E t Ψ) {V : ℕ → Type*}
    {Tw : ∀ n, V n → Idx d (sz.L n) (sz.W n) → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ n, V n → Finset (Idx d (sz.L n) (sz.W n))}
    (hw : ∀ n (b : V n), BoundedWeight (Tw n b) (cw n) (Aw n b))
    (hcW : ∀ n, cw n ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
    (hcard : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ b : V n, 2 * p ≤ (Aw n b).card) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n (b : V n) ω =>
        ‖flucAvg sz n (t n) (zt (E n) (t n)) (mE (E n)) (Tw n b) ω‖)
      (fun n _ _ => 4 * detFlucDelta sz Ψ θ n ^ 2) := by
  have hgain := flucGain_of_localLaw sz hsz hE ht1 ha hKη hθ0 hθa hθ1 hη hΨlo hΨhi hll
  have hg : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' sz n (t n) (zt (E n) (t n)) (mE (E n))
        ((8 * minorDiffC (2 * p) + 4) * detFlucDelta sz Ψ θ n) (4 * detFlucDelta sz Ψ θ n)
        (2 * p) (2 * p) := by
    intro p
    filter_upwards [(hgain (2 * p) (2 * p)).1] with n hn
    have e1 : 2 * (2 * minorDiffC (2 * p) * (2 * detFlucDelta sz Ψ θ n) + 2 * detFlucDelta sz Ψ θ n)
        = (8 * minorDiffC (2 * p) + 4) * detFlucDelta sz Ψ θ n := by ring
    have e2 : 2 * (2 * detFlucDelta sz Ψ θ n) = 4 * detFlucDelta sz Ψ θ n := by ring
    rw [e1, e2] at hn
    exact hn
  have hcρ : ∀ᶠ n : ℕ in atTop, cw n ≤ (4 * detFlucDelta sz Ψ θ n) ^ 2 := by
    filter_upwards [(hgain 0 0).2] with n hn
    calc cw n ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := hcW n
      _ ≤ (2 * (2 * detFlucDelta sz Ψ θ n)) ^ 2 := hn
      _ = (4 * detFlucDelta sz Ψ θ n) ^ 2 := by ring
  have hKp : ∀ p : ℕ, (0 : ℝ) ≤ 8 * minorDiffC (2 * p) + 4 := fun p => by
    have := minorDiffC_nonneg (2 * p)
    linarith
  have h := FlucAvgDet_iter_budget_eventually hsz hE ht1 (Tw := Tw) (cw := cw) (Aw := Aw)
    (Bp := fun p n => (8 * minorDiffC (2 * p) + 4) * detFlucDelta sz Ψ θ n)
    (Bm := detFlucDelta sz Ψ θ) (Kp := fun p => 8 * minorDiffC (2 * p) + 4)
    (ep := fun n => 4 * detFlucDelta sz Ψ θ n) hg hKp
    (fun n => (detFlucDelta_pos sz Ψ θ n).le) (fun p n => le_refl _)
    (fun n => mul_pos (by linarith [detFlucDelta_pos sz Ψ θ n]) (detFlucDelta_pos sz Ψ θ n))
    (fun n => by linarith [detFlucDelta_le_quarter sz Ψ θ n]) hcρ hw hcard
  convert h using 1
  funext n b ω
  ring

/-! ## 4. Choosing the threshold after the tolerance (RBM1D `fixedMoment_budgetFamily_absorb`) -/

/-- A family of positive thresholds gives domination at the original squared entry control,
because the threshold exponent can be chosen after the requested tolerance (RBM1D
`fixedMoment_budgetFamily_absorb`, `Gauss/DetFlucAvgComplete.lean:102`; RBM2D
`FlucAvgDet_budgetFamily_absorb`, `Green/FlucAvgDet.lean:278`).  For `τ, D`, take
`θ = detFlucTheta a τ` (`θ < τ / 16`), the family at `(τ/2, D)`, and
`size^{τ/2} · 4 δ² ≤ size^τ Ψ²` eventually (floor `W^{-d/2} ≤ Ψ`). -/
theorem FlucAvgDet_budgetFamily_absorb {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto)
    {Ψ : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n)
    {V : ℕ → Type*} {ξ : ∀ n, V n → Sizes.SeqΩ sz → ℝ}
    (hfamily : ∀ θ : ℝ, 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
      PerTimeDomAt (Sizes.seqP sz) sz.size ξ (fun n _ _ => 4 * detFlucDelta sz Ψ θ n ^ 2)) :
    PerTimeDomAt (Sizes.seqP sz) sz.size ξ (fun n _ _ => Ψ n ^ 2) := by
  intro τ hτ D hD
  obtain ⟨hθ0, hθa, hθτ, hθ1⟩ := detFlucTheta_specs ha hτ
  have hsource := hfamily (detFlucTheta a τ) hθ0 hθa.le hθ1 (τ / 2) (by linarith) D hD
  filter_upwards [hsource,
    FlucAvgDet_detFlucDelta_scale_absorb sz hsz hτ hθ0.le hθτ.le hΨlo] with n hn hscale v
  refine (measure_mono ?_).trans (hn v)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt hscale hω

/-- **The weighted fluctuation average is `≺ Ψ²`, per time** (the fine-lattice form of the pin):
the local law, the floor `W^{-d/2} ≤ Ψ`, the ceiling `Ψ ≤ size^{-a}` and `size^{-K_η} ≤ η_t` give
`‖flucAvg‖ ≺ Ψ²` for any bounded weight family with `c ≤ W^{-d}` and `2 p ≤ #A` eventually
(RBM2D `FlucAvgDet_weighted`, `Green/FlucAvgDet.lean:297`). -/
theorem FlucAvgDet_weighted {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E t Ψ : ℕ → ℝ}
    {a Kη : ℝ}
    (hE : ∀ n, |E n| < 2) (ht1 : ∀ n, t n < 1) (ha : 0 < a) (hKη : 0 ≤ Kη)
    (hη : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-Kη) ≤ etaT (E n) (t n))
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a))
    (hll : LocalLawDetSeq sz E t Ψ) {V : ℕ → Type*}
    {Tw : ∀ n, V n → Idx d (sz.L n) (sz.W n) → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ n, V n → Finset (Idx d (sz.L n) (sz.W n))}
    (hw : ∀ n (b : V n), BoundedWeight (Tw n b) (cw n) (Aw n b))
    (hcW : ∀ n, cw n ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
    (hcard : ∀ p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ b : V n, 2 * p ≤ (Aw n b).card) :
    PerTimeDomAt (Sizes.seqP sz) sz.size
      (fun n (b : V n) ω =>
        ‖flucAvg sz n (t n) (zt (E n) (t n)) (mE (E n)) (Tw n b) ω‖)
      (fun n _ _ => Ψ n ^ 2) :=
  FlucAvgDet_budgetFamily_absorb sz hsz ha hΨlo fun _ hθ0 hθa hθ1 =>
    FlucAvgDet_family sz hsz hE ht1 ha hKη hθ0 hθa hθ1 hη hΨlo hΨhi hll hw hcW hcard

/-! ## 5. The bridge from the block-product index `Vtx` to the fine lattice `Idx`

`FARowDet` / `FABlkDet` / `IBPDet` are stated on `Vtx d L W` (`svar`, `blkCoef2`, `greenBlk`,
`condDiagBlk`); `flucAvg`, `condExpDiag`, `condRow` live on `Idx d L W`.  The transport is the
equivalence `splitEquiv` (`Idx ≃ Vtx`), the identity `svarF_eq_svar` (RBM2D `Sblk2_eq_svar` has no
literal analogue: the merged `svar` is on `Vtx` and `svarF` is `svar` read through `split`) and
`Matrix.inv_submatrix_equiv`. -/

section Bridge

/-- `greenBlk` at block-product indices is the fine-lattice resolvent at the `splitEquiv`
coordinates (RBM2D `FlucAvgDet_greenBlk_true_apply`, `Green/FlucAvgDet.lean:326`;
`Matrix.inv_submatrix_equiv`; the merged private `entryDom_greenBlk_apply` is the `Gres` form). -/
theorem FlucAvgDet_greenBlk_true_apply {d L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p q : Vtx d L W) :
    greenBlk d L W E u M true p q =
      green M (zt E u) ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) := by
  unfold greenBlk Gres blockMat
  simp only [ite_true]
  have e1 : M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        zt E u • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_submatrix_equiv]
  rfl

/-- `G_kk - m` at a block-product index `k` is `greenDiagCentered` at the fine index
`splitEquiv.symm k` (RBM2D `FlucAvgDet_greenBlk_sub_eq`, `Green/FlucAvgDet.lean:343`). -/
theorem FlucAvgDet_greenBlk_sub_eq {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz) (k : Vtx d (sz.L n) (sz.W n)) :
    greenBlk d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) true k k
        - mE (E n)
      = greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n))
          ((splitEquiv d (sz.L n) (sz.W n)).symm k) ω := by
  rw [FlucAvgDet_greenBlk_true_apply]
  rfl

/-- `condDiagBlk` at a block-product index is `condExpDiag` at the fine index
`splitEquiv.symm k` (RBM2D `FlucAvgDet_condDiagBlk_eq`, `Green/FlucAvgDet.lean:353`). -/
theorem FlucAvgDet_condDiagBlk_eq {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz) (k : Vtx d (sz.L n) (sz.W n)) :
    condDiagBlk sz E t n ω k
      = condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n))
          ((splitEquiv d (sz.L n) (sz.W n)).symm k) ω := by
  unfold condDiagBlk condExpDiag
  congr 1
  funext ω'
  exact FlucAvgDet_greenBlk_sub_eq sz E t n ω' k

/-- The merged `svar` on `Vtx` is `svarF` on `Idx` read through `splitEquiv` (the `Sblk2_eq_svar`
role of RBM2D: `svarF_eq_svar` and `split ∘ splitEquiv.symm = id`). -/
private theorem FlucAvgDet_svar_eq_svarF {d L W : ℕ} [NeZero L] [NeZero W] (g : ℝ)
    (i k : Vtx d L W) :
    svar d L W g i k
      = svarF d L W g ((splitEquiv d L W).symm i) ((splitEquiv d L W).symm k) := by
  rw [svarF_eq_svar]
  have h1 : split d L W ((splitEquiv d L W).symm i) = i := (splitEquiv d L W).apply_symm_apply i
  have h2 : split d L W ((splitEquiv d L W).symm k) = k := (splitEquiv d L W).apply_symm_apply k
  rw [h1, h2]

/-- **The row family on `Vtx` is `flucAvg` with the weight `svarF` on `Idx`**:
`∑_k S_{ik} ((G_kk - m) - E_k(G_kk - m)) = ∑_j S_{ij} Z_j` (`svarF_eq_svar`, `splitEquiv`; RBM2D
`FlucAvgDet_row_sum_eq`, `Green/FlucAvgDet.lean:365`). -/
theorem FlucAvgDet_row_sum_eq {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz) (i : Vtx d (sz.L n) (sz.W n)) :
    ∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
        ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) true k k
          - mE (E n)) - condDiagBlk sz E t n ω k)
      = flucAvg sz n (t n) (zt (E n) (t n)) (mE (E n))
          (fun j => svarF d (sz.L n) (sz.W n) (sz.lam n)
            ((splitEquiv d (sz.L n) (sz.W n)).symm i) j) ω := by
  unfold flucAvg
  rw [← Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm
    (fun j : Idx d (sz.L n) (sz.W n) => (svarF d (sz.L n) (sz.W n) (sz.lam n)
      ((splitEquiv d (sz.L n) (sz.W n)).symm i) j : ℂ) *
        flucDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) j ω)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [FlucAvgDet_svar_eq_svarF, FlucAvgDet_greenBlk_sub_eq, FlucAvgDet_condDiagBlk_eq]
  rfl

/-- **The block family on `Vtx` is `flucAvg` with the weight `W^{-d} 1(k ∈ 𝓘_a)` on `Idx`**:
`blkCoef2` is that weight read through `splitEquiv` (`flucVanish_blockAvg2_eq_blkCoef2`; RBM2D
`FlucAvgDet_blk_sum_eq`, `Green/FlucAvgDet.lean:383`). -/
theorem FlucAvgDet_blk_sum_eq {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz) (a : Zd d (sz.L n)) :
    ∑ k, (blkCoef2 d (sz.L n) (sz.W n) a k : ℂ) *
        ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) true k k
          - mE (E n)) - condDiagBlk sz E t n ω k)
      = flucAvg sz n (t n) (zt (E n) (t n)) (mE (E n))
          (fun j : Idx d (sz.L n) (sz.W n) =>
            if (split d (sz.L n) (sz.W n) j).1 = a then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0) ω := by
  unfold flucAvg
  rw [← Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm
    (fun j : Idx d (sz.L n) (sz.W n) =>
      ((if (split d (sz.L n) (sz.W n) j).1 = a then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0 : ℝ) : ℂ) *
        flucDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) j ω)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hb : blkCoef2 d (sz.L n) (sz.W n) a k =
      (if (split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm k)).1 = a
        then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0) := by
    rw [flucVanish_blockAvg2_eq_blkCoef2, Equiv.apply_symm_apply]
  rw [hb, FlucAvgDet_greenBlk_sub_eq, FlucAvgDet_condDiagBlk_eq]
  rfl

/-- **The IBP sum on `Vtx` is the fine-lattice sum with `svarF`**: `∑_k S_{ik} (G_kk - m)`
(`svarF_eq_svar`, `splitEquiv`; RBM2D `FlucAvgDet_ibp_sum_eq`, `Green/FlucAvgDet.lean:408`). -/
theorem FlucAvgDet_ibp_sum_eq {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz) (i : Vtx d (sz.L n) (sz.W n)) :
    ∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) true k k
          - mE (E n))
      = ∑ j, (svarF d (sz.L n) (sz.W n) (sz.lam n)
            ((splitEquiv d (sz.L n) (sz.W n)).symm i) j : ℂ) *
          (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) j j - mE (E n)) := by
  rw [← Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm
    (fun j : Idx d (sz.L n) (sz.W n) => (svarF d (sz.L n) (sz.W n) (sz.lam n)
      ((splitEquiv d (sz.L n) (sz.W n)).symm i) j : ℂ) *
        (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) j j - mE (E n)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [FlucAvgDet_svar_eq_svarF, FlucAvgDet_greenBlk_sub_eq]
  rfl

/-- Reindexing and pointwise rewriting of a per-time domination: if `ξ' n v = ξ n (g n v)` and
`ζ' n v = ζ n (g n v)` pointwise, the domination of `(ξ, ζ)` gives that of `(ξ', ζ')` (RBM2D
`FlucAvgDet_perTime_reindex`, `Green/FlucAvgDet.lean:426`). -/
theorem FlucAvgDet_perTime_reindex {d : ℕ} {sz : Sizes d} {U V : ℕ → Type*}
    {ξ ζ : ∀ n, U n → Sizes.SeqΩ sz → ℝ} {ξ' ζ' : ∀ n, V n → Sizes.SeqΩ sz → ℝ}
    (g : ∀ n, V n → U n) (hξ : ∀ n v ω, ξ' n v ω = ξ n (g n v) ω)
    (hζ : ∀ n v ω, ζ' n v ω = ζ n (g n v) ω)
    (h : PerTimeDomAt (Sizes.seqP sz) sz.size ξ ζ) :
    PerTimeDomAt (Sizes.seqP sz) sz.size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn v
  have hset : {ω | ((sz.size n : ℕ) : ℝ) ^ τ * ζ' n v ω < ξ' n v ω}
      = {ω | ((sz.size n : ℕ) : ℝ) ^ τ * ζ n (g n v) ω < ξ n (g n v) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hξ, hζ]
  rw [hset]
  exact hn (g n v)

end Bridge

/-! ## 6. The endpoint: `fixedTimeFAThm` -/

section FAEndpoint

variable {d : ℕ}

/-- **The endpoint (pin FA, RBM2D `fixedTimeFAThm`, `Green/FlucAvgDet.lean:453`).**  Both families
of `jasdu` at `x = condDiagBlk`, with the control `Ψ²`: the row family `t_k = S_{ik}`
(`boundedWeight_svarF`, `c = W^{-d}`, `#A = (2d + 1) W^d`; RBM2D `uniformWeight_svar`, which is
false at `d ≥ 3`, DECISIONS §30) and the block family `t_k = W^{-d} 1(k ∈ 𝓘_a)`
(`uniformWeight_blockAvg2`, `c = W^{-d}`, `#A = W^d`), on the fine lattice (`FlucAvgDet_weighted`,
with the `η` input `size^{-1} ≤ η_t` from `eta_lower_of_rangeCond`), then transported to `Vtx` by the
bridge.  No hypothesis is added to the pin `FixedTimeFAThm` (`LocalLaw.lean:176`) except
`hd : 1 ≤ d` (D200): `2 p ≤ #A` uses `W ≤ W^d`. -/
theorem fixedTimeFAThm (hd : 1 ≤ d) : FixedTimeFAThm d := by
  intro sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE _ h1 hR Ψ a ha _ hΨ hll
  obtain ⟨-, -, hsz, hbw, -⟩ := hA
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hη : ∀ᶠ n : ℕ in atTop,
      ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E n) (t n) :=
    (eta_lower_of_rangeCond sz hκ hδ hsz hE hR).mono fun n h => by
      rw [etaT_eq_zt_im]
      exact h
  have hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n :=
    hΨ.mono fun n hn => hn.1
  have hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a) := hΨ.mono fun n hn => hn.2
  have hWd : ∀ n, sz.W n ≤ sz.W n ^ d := fun n => Nat.le_self_pow (by omega) _
  refine ⟨?_, ?_⟩
  · -- the row family `t_k = S_{ik}`
    have hrow := FlucAvgDet_weighted sz hsz hE2 h1 ha (zero_le_one' ℝ) hη hΨlo hΨhi hll
      (V := fun n => Idx d (sz.L n) (sz.W n))
      (Tw := fun n i j => svarF d (sz.L n) (sz.W n) (sz.lam n) i j)
      (cw := fun n => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
      (Aw := fun n i => (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))).filter fun j =>
        (split d (sz.L n) (sz.W n) j).1 - (split d (sz.L n) (sz.W n) i).1
          ∈ flucVanish_sbSupport d (sz.L n))
      (fun n i => boundedWeight_svarF d (sz.L n) (sz.W n) (sz.three_le_L n) (sz.lam n) i)
      (fun n => le_rfl)
      (fun p => by
        filter_upwards [eventually_le_W sz h𝔠 hsz hbw (2 * p)] with n hn i
        rw [card_Sblk_support]
        exact hn.trans ((hWd n).trans (Nat.le_mul_of_pos_left _ (by omega))))
    exact FlucAvgDet_perTime_reindex (fun n i => (splitEquiv d (sz.L n) (sz.W n)).symm i)
      (fun n i ω => by rw [FlucAvgDet_row_sum_eq]) (fun _ _ _ => rfl) hrow
  · -- the block family `t_k = W^{-d} 1(k ∈ 𝓘_a)`
    have hblk := FlucAvgDet_weighted sz hsz hE2 h1 ha (zero_le_one' ℝ) hη hΨlo hΨhi hll
      (V := fun n => Zd d (sz.L n))
      (Tw := fun n a j => if (split d (sz.L n) (sz.W n) j).1 = a
        then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0)
      (cw := fun n => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
      (Aw := fun n a => (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))).filter fun j =>
        (split d (sz.L n) (sz.W n) j).1 = a)
      (fun n a => (uniformWeight_blockAvg2 d (sz.L n) (sz.W n) a).toBoundedWeight)
      (fun n => le_rfl)
      (fun p => by
        filter_upwards [eventually_le_W sz h𝔠 hsz hbw (2 * p)] with n hn a
        rw [card_blockAvg_support]
        exact hn.trans (hWd n))
    exact FlucAvgDet_perTime_reindex (fun n a => a)
      (fun n a ω => by rw [FlucAvgDet_blk_sum_eq]) (fun _ _ _ => rfl) hblk

end FAEndpoint

/-! ## 7. The weighted reduction of the IBP remainder (RBM1D `Gauss/DetIBPWeighted.lean`) -/

/-- The actual conditional IBP residual, with the diagonal coefficient kept (RBM1D
`norm_condExpDiag_sub_le_two_phi`, `Gauss/DetIBPWeighted.lean:33`; RBM2D
`IBPDet_norm_condExpDiag_sub_le_two_phi`, `Green/IBPDet.lean:65`): with
`‖ibpRem (i,k)‖ ≤ A Φ` for `k ≠ i`, `‖ibpRem (i,i)‖ ≤ A` and `W^{-d} ≤ Φ`, the residual is
`≤ 2 A Φ`.  The diagonal coefficient is `S_ii = W^{-d} (1 + 2 d g²)⁻¹ ≤ W^{-d}` (RBM2D
`(5 W²)⁻¹ ≤ (W⁻¹)²`; RBM1D `S_ii ≤ W⁻¹ ≤ Φ`). -/
theorem IBPDet_norm_condExpDiag_sub_le_two_phi {d : ℕ} {sz : Sizes d} {n : ℕ} {E t : ℝ}
    (hE : |E| < 2) (ht0 : 0 ≤ t) (ht : t < 1) (i : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) {A Φ : ℝ} (hA0 : 0 ≤ A) (hΦ0 : 0 ≤ Φ)
    (hWΦ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Φ)
    (hoff : ∀ k : Idx d (sz.L n) (sz.W n), k ≠ i → ‖ibpRem sz n E t (i, k) ω‖ ≤ A * Φ)
    (hdiag : ‖ibpRem sz n E t (i, i) ω‖ ≤ A) :
    ‖condExpDiag sz n t (zt E t) (mE E) i ω
        - (t : ℂ) * mE E ^ 2 * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * (green (Sizes.seqHflow sz n t ω) (zt E t) k k - mE E)‖ ≤ 2 * A * Φ := by
  have hS : svarF d (sz.L n) (sz.W n) (sz.lam n) i i ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [svarF_diag]
    have h0 : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    have h1 : (1 + 2 * (d : ℝ) * sz.lam n ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (sz.lam n), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 + 2 * (d : ℝ) * sz.lam n ^ 2)⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := mul_one _
  calc _ ≤ A * Φ + svarF d (sz.L n) (sz.W n) (sz.lam n) i i * A :=
      norm_condExpDiag_sub_le_offdiag hE ht0 ht i ω (mul_nonneg hA0 hΦ0) hoff hdiag
    _ ≤ A * Φ + Φ * A :=
      add_le_add_right (mul_le_mul_of_nonneg_right (hS.trans hWΦ) hA0) _
    _ = 2 * A * Φ := by ring

/-- **The weighted IBP display from the remainder bound** (RBM1D
`unifDomIcc_condExpDiag_weighted_of_remN`, `EnergyN/Gauss/DetIBPWeighted.lean:39`; RBM2D
`IBPDet_weighted_of_rem`, `Green/IBPDet.lean:88`): from `ibpRem (i,k) ≺ Ψ²` off the diagonal and
`≺ 1` on it (`hrem`), and `W^{-d} ≤ Ψ²`, `|E_i(G_ii - m) - t m² Σ_k S_ik (G_kk - m)| ≺ Ψ²`, per
time.  The union is over the `size = (W L)^d` sites `k` of the row (spending `D + 2` on `D`); `i`
stays outside the probability. -/
theorem IBPDet_weighted_of_rem {d : ℕ} {sz : Sizes d} (hsz : sz.SizeTendsto) {E t Ψ : ℕ → ℝ}
    (hE : ∀ n, |E n| < 2) (h0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hWΨ : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Ψ n * Ψ n)
    (hrem : PerTimeDomAt (Sizes.seqP sz) sz.size
      (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω => ‖ibpRem sz n (E n) (t n) q ω‖)
      (fun n q _ => if q.1 = q.2 then (1 : ℝ) else Ψ n * Ψ n)) :
    PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun n => Idx d (sz.L n) (sz.W n))
      (fun n i ω =>
        ‖condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) i ω
          - (t n : ℂ) * mE (E n) ^ 2 * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
            * (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) k k
              - mE (E n))‖)
      (fun n _ _ => Ψ n * Ψ n) := by
  classical
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  filter_upwards [hrem (τ / 2) hτ2 (D + 2) (by linarith), hWΨ,
    (FlucAvgDet_tendsto_size hsz).eventually (eventually_le_rpow 2 hτ2)] with
    n hremN hWΨn h2N i
  have hNge1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set a : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hadef
  have ha0 : 0 ≤ a := (Real.rpow_pos_of_pos hNpos _).le
  have ha2 : a * a = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [hadef, ← Real.rpow_add hNpos]
    congr 1
    ring
  set T : Idx d (sz.L n) (sz.W n) → Set (Sizes.SeqΩ sz) := fun k =>
    {ω | a * (if i = k then (1 : ℝ) else Ψ n * Ψ n) <
      ‖ibpRem sz n (E n) (t n) (i, k) ω‖} with hTdef
  have hTk : ∀ k : Idx d (sz.L n) (sz.W n), (Sizes.seqP sz) (T k) ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 2))) := fun k => hremN (i, k)
  have hunion : (Sizes.seqP sz) (⋃ k, T k) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    have hpow : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
    have hcard' : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [flucAvg_card_Idx_eq_size]
    calc (Sizes.seqP sz) (⋃ k, T k)
        ≤ ∑ k : Idx d (sz.L n) (sz.W n), (Sizes.seqP sz) (T k) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : Idx d (sz.L n) (sz.W n),
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 2))) :=
          Finset.sum_le_sum fun k _ => hTk k
      _ = ENNReal.ofReal ((Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) *
          ((sz.size n : ℕ) : ℝ) ^ (-(D + 2))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) *
              ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) ≤
              ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) :=
            mul_le_mul_of_nonneg_right hcard' hpow
          have h2 : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) =
              ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := by
            have hsplit := Real.rpow_add hNpos 1 (-(D + 2))
            rw [Real.rpow_one] at hsplit
            rw [← hsplit]
            congr 1
            ring
          have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) :=
            Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
          linarith
  have hsub : {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (Ψ n * Ψ n) <
      ‖condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) i ω
        - (t n : ℂ) * mE (E n) ^ 2 * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) k k
            - mE (E n))‖} ⊆ ⋃ k, T k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    have hTle : ∀ k : Idx d (sz.L n) (sz.W n), ‖ibpRem sz n (E n) (t n) (i, k) ω‖ ≤
        a * (if i = k then (1 : ℝ) else Ψ n * Ψ n) := by
      intro k
      have := hcon k
      rw [hTdef] at this
      simpa only [Set.mem_ofPred_eq, not_lt] using this
    have hΦ0 : 0 ≤ Ψ n * Ψ n := mul_nonneg (hΨ0 n) (hΨ0 n)
    have hbound := IBPDet_norm_condExpDiag_sub_le_two_phi (hE n) (h0 n) (ht1 n) i ω ha0 hΦ0
      hWΨn (fun k hk => by simpa [Ne.symm hk] using hTle k) (by simpa using hTle i)
    have h2a : 2 * a ≤ a * a := by
      have ha : 2 ≤ a := h2N
      nlinarith
    have hfin : ‖condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n)) i ω
        - (t n : ℂ) * mE (E n) ^ 2 * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n)) k k
            - mE (E n))‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (Ψ n * Ψ n) := by
      calc _ ≤ 2 * a * (Ψ n * Ψ n) := hbound
        _ ≤ (a * a) * (Ψ n * Ψ n) := mul_le_mul_of_nonneg_right h2a hΦ0
        _ = _ := by rw [ha2]
    exact (not_le.2 hω) hfin
  exact (measure_mono hsub).trans hunion

/-! ## 8. The eventual inputs of `perTimeDomAt_ibpRem` (RBM1D `Gauss/DetAvgIBPFlow.lean`) -/

/-- The envelope input `hEnv` at `K_env = 3` from `size^{-1} ≤ η_t` (`K_η = 1`): `η⁻¹ ≤ size`, so
`(η⁻¹ + 1)² ≤ (size + 1)² ≤ size³` once `size ≥ 4` (RBM2D `IBPDet_hEnv`,
`Green/IBPDet.lean:186`; dimension-free). -/
theorem IBPDet_hEnv {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {E t : ℕ → ℝ}
    (hη : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E n) (t n)) :
    ∀ᶠ n : ℕ in atTop,
      ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
  filter_upwards [hη, flucThreshold_etaInv_le_rpow_of_lower sz hη, hsz.eventually_ge_atTop 4]
    with n hn hinv hs4
  rw [Real.rpow_one] at hinv
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  have hpos : 0 < etaT (E n) (t n) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hn
  have hinv0 : 0 ≤ (etaT (E n) (t n))⁻¹ := inv_nonneg.2 hpos.le
  set s : ℝ := ((sz.size n : ℕ) : ℝ) with hs
  have h1 : ((etaT (E n) (t n))⁻¹ + 1) ^ 2 ≤ (s + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (s + 1) ^ 2 ≤ s ^ 3 := by nlinarith [sq_nonneg s]
  exact h1.trans h2

/-- The ceiling `Ψ² ≤ 1` from `Ψ ≤ size^{-a}` (RBM1D `eventually_psi_sq_le_one`,
`Gauss/DetAvgIBPFlow.lean:77`; RBM2D `IBPDet_hΨ1`, `Green/IBPDet.lean:224`). -/
theorem IBPDet_hΨ1 {d : ℕ} (sz : Sizes d) {Ψ : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) :
    ∀ᶠ n : ℕ in atTop, Ψ n * Ψ n ≤ 1 := by
  filter_upwards [hΨhi] with n hn
  have h1 : Ψ n ≤ 1 :=
    hn.trans (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast sz.one_le_size n)
      (by linarith))
  nlinarith [hΨ0 n]

/-- The floor `W^{-d/2} ≤ Ψ` gives `W^{-d} ≤ Ψ²` (`(W^{-d/2})² = W^{-d}`; the `hWΨ` of
`IBPDet_weighted_of_rem`; RBM2D `(W⁻¹)² ≤ Ψ²` from `W⁻¹ ≤ Ψ`).  RBM2D's `IBPDet_hΨlow` (the
polynomial floor `size^{-1} ≤ Ψ²` from `W⁻¹ ≤ Ψ`) is replaced by the merged
`IBPRem_hΨlow_of_floor` (floor `W^{-d/2}`). -/
private theorem IBPDet_hWΨ {d : ℕ} (sz : Sizes d) {Ψ : ℕ → ℝ}
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) :
    ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Ψ n * Ψ n := by
  filter_upwards [hΨlo] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hW.le _
  have hsq : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
      = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [← Real.rpow_add hW, show (-(d : ℝ) / 2 + -(d : ℝ) / 2) = -(d : ℝ) by ring,
      Real.rpow_neg hW.le, Real.rpow_natCast]
  rw [← hsq]
  exact mul_le_mul hn hn h0 (h0.trans hn)

/-! ## 9. The endpoint: `ibpDetThm` -/

section IBPEndpoint

variable {d : ℕ}

/-- **The endpoint (pin IBP, RBM2D `ibpDetThm`, `Green/IBPDet.lean:241`).**  The remainder
`ibpRem ≺ 1` (diagonal), `≺ Ψ²` (off the diagonal) from the merged `perTimeDomAt_ibpRem`
(`K_env = 3`, `B = 1`, the good event at `θ = detFlucTheta a 1`), then the weighted reduction
`IBPDet_weighted_of_rem`, then the bridge to `Vtx` (`splitEquiv`, `svarF_eq_svar`).  No hypothesis is
added to the pin `IBPDetThm` (`LocalLaw.lean:186`) except `hd : 1 ≤ d` (D200, carried by
`perTimeDomAt_ibpRem`). -/
theorem ibpDetThm (hd : 1 ≤ d) : IBPDetThm d := by
  intro sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR Ψ a ha hΨ0 hΨ hll
  obtain ⟨-, -, hsz, -, -⟩ := hA
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hη : ∀ᶠ n : ℕ in atTop,
      ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E n) (t n) :=
    (eta_lower_of_rangeCond sz hκ hδ hsz hE hR).mono fun n h => by
      rw [etaT_eq_zt_im]
      exact h
  have hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n :=
    hΨ.mono fun n hn => hn.1
  have hΨhi : ∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a) := hΨ.mono fun n hn => hn.2
  obtain ⟨hθ0, hθa, -, hθ1⟩ := detFlucTheta_specs ha one_pos
  have hΩ := highProbAt_detFlucDelta_of_localLaw sz hsz ha hθ0 hθa.le hθ1 hΨhi hll
  have hrem := perTimeDomAt_ibpRem (d := d) (sz := sz) (E := E) (t := t) (Ψ := Ψ)
    (δ := detFlucDelta sz Ψ (detFlucTheta a 1)) (Kenv := 3) (B := 1) hd
    (FlucAvgDet_tendsto_size hsz) hE2 h1 hΨ0 (by norm_num) zero_le_one
    (IBPDet_hEnv sz hsz hη) (hΨlo.mono fun n hn => IBPRem_hΨlow_of_floor sz n hn)
    (IBPDet_hΨ1 sz ha hΨ0 hΨhi)
    (Eventually.of_forall fun n => (detFlucDelta_le_quarter sz Ψ _ n).trans (by norm_num)) hΩ hll
  have hidx := IBPDet_weighted_of_rem hsz hE2 h0 h1 hΨ0 (IBPDet_hWΨ sz hΨlo) hrem
  exact FlucAvgDet_perTime_reindex (fun n i => (splitEquiv d (sz.L n) (sz.W n)).symm i)
    (fun n i ω => by rw [FlucAvgDet_condDiagBlk_eq, FlucAvgDet_ibp_sum_eq])
    (fun n _ _ => sq (Ψ n)) hidx

end IBPEndpoint

/-! ## 10. `lem_GbEXP` for every size sequence of dimension `d ≥ 3` -/

section GbEXPEndpoint

variable {d : ℕ}

/-- **`lem_GbEXP`** (`3_5:14-40`; RBM2D `gbEXPV3`, `Green/GbEXP.lean:45`): `GbEXPHypV3 sz κ 𝔠 𝔡 δ`
for every size sequence `sz : Sizes d` with `3 ≤ d` and every `κ, 𝔠, 𝔡, δ > 0`, from the three
proved ports `localLawDetThm`, `fixedTimeFAThm`, `ibpDetThm` (`LocalLaw_gbEXPV3Theorem_of_fa_ibp`).
`hd : 3 ≤ d` is that of `localLawDetThm` (D201); the other two need `1 ≤ d`. -/
theorem gbEXPV3 (hd : 3 ≤ d) : GbEXPV3Theorem d :=
  LocalLaw_gbEXPV3Theorem_of_fa_ibp hd (fixedTimeFAThm (by omega)) (ibpDetThm (by omega))

/-- **`(GiiGEX)`, `(GijGEX)`, `(GavLGEX)` of `lem_GbEXP` in the ST form** (`3_5:14-40`): the three
parts hold for every flow (`stGbEXP_of_v3`). -/
theorem stGbEXP_holds (hd : 3 ≤ d) : STGbEXP d := stGbEXP_of_v3 (gbEXPV3 hd)

/-- **Step 1 of `lem:main_ind`** (`1_2:1317-1328`, `3_5:64-66`): `STStep1 d` for every `d ≥ 3`, from
the merged `RBM.Ind.step1TargetV3_holds` under the two parts `(GiiGEX)`, `(GijGEX)` of `lem_GbEXP`
(`stGbEXPii_of_v3`, `stGbEXPij_of_v3`). -/
theorem stStep1_holds (hd : 3 ≤ d) : STStep1 d :=
  RBM.Ind.step1TargetV3_holds d (stGbEXPii_of_v3 (gbEXPV3 hd)) (stGbEXPij_of_v3 (gbEXPV3 hd))

end GbEXPEndpoint

/-! ## 11. Compiled nonempty instances at `d = 3`

The data are those of `RBM3D/Induction/Defs.lean`, section 3 and `Green/Pins.lean`, section 9
(`Instance.premises`): the merged preflight sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`),
admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; `κ = δ = (1/10)/2`; the flow points `z_n = 1/2 + i N_n^{-4/5}`
with the non-constant energy `E_n = lemE z_n`; the time `t ≡ 1/16` (not the collapsed `t ≡ 0`: `G_t ≠
m`).  The control is `Ψ_n = W_n^{-3/2}`: the floor `W^{-d/2}` of the pins **with equality** (so the
RBM2D premise `W⁻¹ ≤ Ψ` fails there, `gbEXP_W_inv_not_le_psi`), and `Ψ_n ≤ N_n^{-1/4}` is
`N_n ≤ W_n^6` (`sz0_size_le_W_pow`); `a = 1/4`.

What stays a hypothesis of an instance at `t ≡ 1/16` is another gate's input: the local law
`LocalLawDetSeq sz0 E t Ψ` (`(asGMc)` at `c = 3/2` with `asGMcSeq_iff`, the output of the merged
`localLawDetThm` from `AsGMcSeq` and `LoopDetSeq`), the premises `AsGMcSeq`, `LoopDetSeq` of the
third clause of `lem_GbEXP`, and `STKbound`, `STLK`, `STLocalMax` at `s` of Step 1.  Every
deterministic hypothesis is proved at the data.  The instances at `t ≡ 0` (`H = 0`, `G = m 1`) have
no hypothesis left (`localLawDetSeq_time_zero`); the flow is collapsed there, so they complement
and do not replace the instances at `t ≡ 1/16`. -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- The instance control `Ψ n = W n^{-3/2}` (the floor `W^{-d/2}` at `d = 3`, with equality). -/
private def gbEXPPsi (n : ℕ) : ℝ := ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)

private theorem gbEXPPsi_nonneg (n : ℕ) : 0 ≤ gbEXPPsi n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- `Ψ n = W^{-3/2} ≤ N^{-1/4}`: `N^{1/4} ≤ (W^6)^{1/4} = W^{3/2}` (`sz0_size_le_W_pow`). -/
private theorem gbEXPPsi_ceiling (n : ℕ) :
    gbEXPPsi n ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
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
  unfold gbEXPPsi
  rw [Real.rpow_neg hN0.le, show (-((3 : ℕ) : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num,
    Real.rpow_neg hW0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) h1

/-- **The RBM2D premise `W⁻¹ ≤ Ψ` fails at the floor of the pins** (`n = 0`, `W = 32`:
`32⁻¹ ≤ 32^{-3/2}` is false): the floor `W^{-d/2}` is strictly weaker than `W⁻¹` for `d ≥ 3`, so no
step of the port may use `W⁻¹ ≤ Ψ` (paper-delta candidate `T2126a`). -/
private theorem gbEXP_W_inv_not_le_psi : ¬ (((sz0.W 0 : ℕ) : ℝ)⁻¹ ≤ gbEXPPsi 0) := by
  have hW : ((sz0.W 0 : ℕ) : ℝ) = 32 := by exact_mod_cast sz0_values.2.1
  unfold gbEXPPsi
  rw [hW, show (-((3 : ℕ) : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num]
  intro h
  have h1 : (32 : ℝ) ^ (-(3 / 2 : ℝ)) < (32 : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  rw [Real.rpow_neg_one] at h1
  linarith

/-- `RangeCond` at `t ≡ 0`: `N^{-1+δ} ≤ 1 = 1 - 0` (`δ ≤ 1`). -/
private theorem gbEXP_rangeCond_zero : sz0.RangeCond ((1 / 10) / 2) (fun _ => 0) :=
  Eventually.of_forall fun n => by
    have h := Real.rpow_le_one_of_one_le_of_nonpos (one_le_size_sz0 n)
      (by norm_num : (-1 + (1 / 10) / 2 : ℝ) ≤ 0)
    linarith

/-- **Instance of `fixedTimeFAThm`**: `d = 3`, `sz0`, `κ = δ = (1/10)/2`, `𝔠 = 1/6`, `𝔡 = 1/10`,
`E = lemE z_n`, `t ≡ 1/16`, `Ψ = W^{-3/2}`, `a = 1/4`: `Admissible`, the bulk, `0 ≤ t < 1`,
`RangeCond`, `0 < a`, `0 ≤ Ψ` and the floor and ceiling are discharged; the local law is the other
gate's pin.  Both families of `jasdu` are produced. -/
private theorem gbEXP_inst_fixedTimeFA
    (hll : LocalLawDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    FARowDet sz0 (STflowE z0) tInst (condDiagBlk sz0 (STflowE z0) tInst) gbEXPPsi ∧
      FABlkDet sz0 (STflowE z0) tInst (condDiagBlk sz0 (STflowE z0) tInst) gbEXPPsi :=
  fixedTimeFAThm (by norm_num : 1 ≤ 3) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Instance.premises.1 (STflowE z0) tInst
    Instance.premises.2.1 Instance.premises.2.2.1 Instance.premises.2.2.2.1
    Instance.premises.2.2.2.2 gbEXPPsi (1 / 4) (by norm_num) gbEXPPsi_nonneg
    (Eventually.of_forall fun n => ⟨le_rfl, gbEXPPsi_ceiling n⟩) hll

/-- **Instance of `ibpDetThm`**: the same data; the IBP display `IBPDetSeq` is produced. -/
private theorem gbEXP_inst_ibpDet (hll : LocalLawDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    IBPDet sz0 (STflowE z0) tInst (condDiagBlk sz0 (STflowE z0) tInst) gbEXPPsi :=
  ibpDetThm (by norm_num : 1 ≤ 3) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Instance.premises.1 (STflowE z0) tInst
    Instance.premises.2.1 Instance.premises.2.2.1 Instance.premises.2.2.2.1
    Instance.premises.2.2.2.2 gbEXPPsi (1 / 4) (by norm_num) gbEXPPsi_nonneg
    (Eventually.of_forall fun n => ⟨le_rfl, gbEXPPsi_ceiling n⟩) hll

/-- **Instance of `fixedTimeFAThm` at `t ≡ 0`**: no hypothesis is left (`LocalLawDetSeq` is
`localLawDetSeq_time_zero`). -/
private theorem gbEXP_inst_fixedTimeFA_zero :
    FixedTimeFASeq sz0 (STflowE z0) (fun _ => 0) gbEXPPsi :=
  fixedTimeFAThm (by norm_num : 1 ≤ 3) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Instance.premises.1 (STflowE z0)
    (fun _ => 0) Instance.premises.2.1 (fun _ => le_rfl) (fun _ => zero_lt_one)
    gbEXP_rangeCond_zero gbEXPPsi (1 / 4) (by norm_num) gbEXPPsi_nonneg
    (Eventually.of_forall fun n => ⟨le_rfl, gbEXPPsi_ceiling n⟩)
    (localLawDetSeq_time_zero sz0 (fun n => by linarith [Instance.premises.2.1 n])
      gbEXPPsi_nonneg)

/-- **Instance of `ibpDetThm` at `t ≡ 0`**: no hypothesis is left. -/
private theorem gbEXP_inst_ibpDet_zero :
    IBPDetSeq sz0 (STflowE z0) (fun _ => 0) gbEXPPsi :=
  ibpDetThm (by norm_num : 1 ≤ 3) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Instance.premises.1 (STflowE z0)
    (fun _ => 0) Instance.premises.2.1 (fun _ => le_rfl) (fun _ => zero_lt_one)
    gbEXP_rangeCond_zero gbEXPPsi (1 / 4) (by norm_num) gbEXPPsi_nonneg
    (Eventually.of_forall fun n => ⟨le_rfl, gbEXPPsi_ceiling n⟩)
    (localLawDetSeq_time_zero sz0 (fun n => by linarith [Instance.premises.2.1 n])
      gbEXPPsi_nonneg)

/-- **Instance of `gbEXPV3`**, clauses (`GijGEX`), (`GiiGEX`): on `Ω(t, c)` for every `c > 0`, with
no probabilistic hypothesis. -/
private theorem gbEXP_inst_gbEXPV3_ij_ii (c : ℝ) (hc : 0 < c) :
    GijOmegaSeq sz0 (STflowE z0) tInst c ∧ GiiOmegaSeq sz0 (STflowE z0) tInst c :=
  have h := gbEXPV3 (by norm_num : 3 ≤ 3) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Instance.premises.1 (STflowE z0) tInst
    Instance.premises.2.1 Instance.premises.2.2.1 Instance.premises.2.2.2.1
    Instance.premises.2.2.2.2 c hc
  ⟨h.1, h.2.1⟩

/-- **Instance of `gbEXPV3`**, clause (`GavLGEX`): under (`asGMc`) at `c` and `LoopDetSeq` (the
random premises of the lemma itself, kept as hypotheses), `GijSeq`, `GiiSeq` and, at the control
`Ψ = W^{-3/2}`, `a = 1/4` (both window bounds proved), `GavLDetSeq`. -/
private theorem gbEXP_inst_gbEXPV3_avg (c : ℝ) (hc : 0 < c)
    (hAs : AsGMcSeq sz0 (STflowE z0) tInst c) (hLoop : LoopDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    GijSeq sz0 (STflowE z0) tInst ∧ GiiSeq sz0 (STflowE z0) tInst ∧
      GavLDetSeq sz0 (STflowE z0) tInst gbEXPPsi := by
  obtain ⟨hij, hii, hav⟩ := (gbEXPV3 (by norm_num : 3 ≤ 3) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10)
    ((1 / 10) / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Instance.premises.1
    (STflowE z0) tInst Instance.premises.2.1 Instance.premises.2.2.1 Instance.premises.2.2.2.1
    Instance.premises.2.2.2.2 c hc).2.2 hAs
  exact ⟨hij, hii, hav gbEXPPsi (1 / 4) (by norm_num) gbEXPPsi_nonneg
    (Eventually.of_forall gbEXPPsi_ceiling) hLoop⟩

/-- **Instance of `stGbEXP_holds`**: the three parts of `lem_GbEXP` in the ST form at the flow,
`t ≡ 1/16`, `ε₀ = 1/20`. -/
private theorem gbEXP_inst_stGbEXP :
    STGiiGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tInst (1 / 20) :=
  inst_gbEXP (stGbEXP_holds (by norm_num : 3 ≤ 3))

/-- **Instance of `stStep1_holds`**: `d = 3`, `sz0`, `z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`𝔠_d = 1/100`, `s ≡ 0 < t ≡ 1/16 ≤ lemT z_n`: `STFlow`, the time ranges and `STConStInd` are
discharged; `STKbound`, `STLK`, `STLocalMax` at `s` are other gates' pins (the ST-6 chain).  Both
conjuncts of `STStep1` are produced, and the two parts of `lem_GbEXP` are no longer hypotheses. -/
private theorem gbEXP_inst_stStep1 (hK : STKbound sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hLoc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst :=
  stStep1_holds (by norm_num : 3 ≤ 3) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 100) (by norm_num) le_rfl (1 / 6) sz0 z0 flow_z0 sInst tInst
    (fun _ => le_rfl) zero_le_lemT (fun n => by simp only [sInst, tInst]; norm_num)
    sixteenth_le_lemT hK hLK hLoc (conStInd_inst (by norm_num))

/-! ### Instances of the supporting theorems (same data, `n = 0` for the identities) -/

/-- The `η` input of the endpoints at the data: `N^{-1} ≤ η_t` (`K_η = 1`), from `RangeCond`
(`eta_lower_of_rangeCond`), as in the proofs of `fixedTimeFAThm`, `ibpDetThm`. -/
private theorem gbEXP_inst_eta :
    ∀ᶠ n : ℕ in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ etaT (STflowE z0 n) (tInst n) :=
  (eta_lower_of_rangeCond sz0 (by norm_num) (by norm_num) sz0_tendsto Instance.premises.2.1
    Instance.premises.2.2.2.2).mono fun n h => by
      rw [etaT_eq_zt_im]
      exact h

/-- **Instance of `FlucAvgDet_weighted`** (and, through its proof, of `FlucAvgDet_family`,
`FlucAvgDet_budgetFamily_absorb`, `FlucAvgDet_iter_budget_eventually`): the block family
`t_k = W^{-d} 1(k ∈ 𝓘_a)` at `sz0`, `Ψ = W^{-3/2}`, `a = 1/4`, `K_η = 1`.  `c = W^{-d}`, `#A = W^d`
and `2 p ≤ #A` from `W → ∞`. -/
private theorem gbEXP_inst_weighted_block
    (hll : LocalLawDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (fun n (a : Zd 3 (sz0.L n)) ω =>
        ‖flucAvg sz0 n (tInst n) (zt (STflowE z0 n) (tInst n)) (mE (STflowE z0 n))
          (fun j : Idx 3 (sz0.L n) (sz0.W n) =>
            if (split 3 (sz0.L n) (sz0.W n) j).1 = a then (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ else 0) ω‖)
      (fun n _ _ => gbEXPPsi n ^ 2) :=
  FlucAvgDet_weighted sz0 sz0_tendsto (fun n => by linarith [Instance.premises.2.1 n])
    Instance.premises.2.2.2.1 (by norm_num : (0 : ℝ) < 1 / 4) zero_le_one gbEXP_inst_eta
    (Eventually.of_forall fun n => le_rfl) (Eventually.of_forall gbEXPPsi_ceiling) hll
    (V := fun n => Zd 3 (sz0.L n))
    (Tw := fun n a j => if (split 3 (sz0.L n) (sz0.W n) j).1 = a
      then (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ else 0)
    (cw := fun n => (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹)
    (Aw := fun n a => (Finset.univ : Finset (Idx 3 (sz0.L n) (sz0.W n))).filter fun j =>
      (split 3 (sz0.L n) (sz0.W n) j).1 = a)
    (fun n a => (uniformWeight_blockAvg2 3 (sz0.L n) (sz0.W n) a).toBoundedWeight)
    (fun n => le_rfl)
    (fun p => by
      filter_upwards [eventually_le_W sz0 (by norm_num : (0 : ℝ) < 1 / 6) sz0_tendsto
        sz0_bandwidth (2 * p)] with n hn a
      rw [card_blockAvg_support]
      exact hn.trans (Nat.le_self_pow (by norm_num) _))

/-- **Instance of `FlucAvgDet_weighted`**, the row family `t_k = S_{ik}` (a bounded weight, not a
uniform one: `c·#A = 7 > 1`, `#A = 7 W^3`, DECISIONS §30) at the same data. -/
private theorem gbEXP_inst_weighted_row
    (hll : LocalLawDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (fun n (i : Idx 3 (sz0.L n) (sz0.W n)) ω =>
        ‖flucAvg sz0 n (tInst n) (zt (STflowE z0 n) (tInst n)) (mE (STflowE z0 n))
          (fun j => svarF 3 (sz0.L n) (sz0.W n) (sz0.lam n) i j) ω‖)
      (fun n _ _ => gbEXPPsi n ^ 2) :=
  FlucAvgDet_weighted sz0 sz0_tendsto (fun n => by linarith [Instance.premises.2.1 n])
    Instance.premises.2.2.2.1 (by norm_num : (0 : ℝ) < 1 / 4) zero_le_one gbEXP_inst_eta
    (Eventually.of_forall fun n => le_rfl) (Eventually.of_forall gbEXPPsi_ceiling) hll
    (V := fun n => Idx 3 (sz0.L n) (sz0.W n))
    (Tw := fun n i j => svarF 3 (sz0.L n) (sz0.W n) (sz0.lam n) i j)
    (cw := fun n => (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹)
    (Aw := fun n i => (Finset.univ : Finset (Idx 3 (sz0.L n) (sz0.W n))).filter fun j =>
      (split 3 (sz0.L n) (sz0.W n) j).1 - (split 3 (sz0.L n) (sz0.W n) i).1
        ∈ flucVanish_sbSupport 3 (sz0.L n))
    (fun n i => boundedWeight_svarF 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) (sz0.lam n) i)
    (fun n => le_rfl)
    (fun p => by
      filter_upwards [eventually_le_W sz0 (by norm_num : (0 : ℝ) < 1 / 6) sz0_tendsto
        sz0_bandwidth (2 * p)] with n hn i
      rw [card_Sblk_support]
      exact hn.trans ((Nat.le_self_pow (by norm_num) _).trans
        (Nat.le_mul_of_pos_left _ (by norm_num))))

/-- **Instances of `IBPDet_hEnv`, `IBPDet_hΨ1`, `IBPDet_hWΨ`** (the eventual inputs of
`perTimeDomAt_ibpRem`; `hΨlow` is the merged `IBPRem_hΨlow_of_floor`) at the data: `K_env = 3`,
`Ψ² ≤ 1`, `W^{-3} ≤ Ψ²`, `N^{-1} ≤ Ψ²`. -/
private theorem gbEXP_inst_ibp_inputs :
    (∀ᶠ n : ℕ in atTop, ((etaT (STflowE z0 n) (tInst n))⁻¹ + 1) ^ 2 ≤
        ((sz0.size n : ℕ) : ℝ) ^ (3 : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop, gbEXPPsi n * gbEXPPsi n ≤ 1) ∧
      (∀ᶠ n : ℕ in atTop, (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ gbEXPPsi n * gbEXPPsi n) ∧
      (∀ n, ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ gbEXPPsi n * gbEXPPsi n) :=
  ⟨IBPDet_hEnv sz0 sz0_tendsto gbEXP_inst_eta,
    IBPDet_hΨ1 sz0 (by norm_num : (0 : ℝ) < 1 / 4) gbEXPPsi_nonneg
      (Eventually.of_forall gbEXPPsi_ceiling),
    IBPDet_hWΨ sz0 (Eventually.of_forall fun n => le_rfl),
    fun n => IBPRem_hΨlow_of_floor sz0 n le_rfl⟩

/-- **Instance of `IBPDet_weighted_of_rem`**: the remainder bound `hrem` (the output of the merged
`perTimeDomAt_ibpRem`, proved in `ibpDetThm` from the local law) is the hypothesis. -/
private theorem gbEXP_inst_weighted_of_rem
    (hrem : PerTimeDomAt (Sizes.seqP sz0) sz0.size
      (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n q ω => ‖ibpRem sz0 n (STflowE z0 n) (tInst n) q ω‖)
      (fun n q _ => if q.1 = q.2 then (1 : ℝ) else gbEXPPsi n * gbEXPPsi n)) :
    PerTimeDomAt (Sizes.seqP sz0) sz0.size (U := fun n => Idx 3 (sz0.L n) (sz0.W n))
      (fun n i ω =>
        ‖condExpDiag sz0 n (tInst n) (zt (STflowE z0 n) (tInst n)) (mE (STflowE z0 n)) i ω
          - (tInst n : ℂ) * mE (STflowE z0 n) ^ 2 *
            ∑ k, (svarF 3 (sz0.L n) (sz0.W n) (sz0.lam n) i k : ℂ)
            * (green (Sizes.seqHflow sz0 n (tInst n) ω) (zt (STflowE z0 n) (tInst n)) k k
              - mE (STflowE z0 n))‖)
      (fun n _ _ => gbEXPPsi n * gbEXPPsi n) :=
  IBPDet_weighted_of_rem sz0_tendsto (fun n => by linarith [Instance.premises.2.1 n])
    Instance.premises.2.2.1 Instance.premises.2.2.2.1 gbEXPPsi_nonneg
    gbEXP_inst_ibp_inputs.2.2.1 hrem

/-- **Instances of the bridge identities** `FlucAvgDet_greenBlk_true_apply`,
`FlucAvgDet_greenBlk_sub_eq`, `FlucAvgDet_condDiagBlk_eq`, `FlucAvgDet_row_sum_eq`,
`FlucAvgDet_blk_sum_eq`, `FlucAvgDet_ibp_sum_eq` at `n = 0` (`L = 4`, `W = 32`, `W^3 = 32768`
sites per block, `N = 2097152`), for every sample `ω` and every block-product index. -/
private theorem gbEXP_inst_bridge (ω : sz0.SeqΩ) (i : Vtx 3 (sz0.L 0) (sz0.W 0))
    (a : Zd 3 (sz0.L 0)) :
    greenBlk 3 (sz0.L 0) (sz0.W 0) (STflowE z0 0) (tInst 0) (Sizes.seqHflow sz0 0 (tInst 0) ω)
        true i i
      = green (Sizes.seqHflow sz0 0 (tInst 0) ω) (zt (STflowE z0 0) (tInst 0))
        ((splitEquiv 3 (sz0.L 0) (sz0.W 0)).symm i) ((splitEquiv 3 (sz0.L 0) (sz0.W 0)).symm i) ∧
    condDiagBlk sz0 (STflowE z0) tInst 0 ω i
      = condExpDiag sz0 0 (tInst 0) (zt (STflowE z0 0) (tInst 0)) (mE (STflowE z0 0))
        ((splitEquiv 3 (sz0.L 0) (sz0.W 0)).symm i) ω ∧
    ∑ k, (svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i k : ℂ) *
        ((greenBlk 3 (sz0.L 0) (sz0.W 0) (STflowE z0 0) (tInst 0)
          (Sizes.seqHflow sz0 0 (tInst 0) ω) true k k - mE (STflowE z0 0))
          - condDiagBlk sz0 (STflowE z0) tInst 0 ω k)
      = flucAvg sz0 0 (tInst 0) (zt (STflowE z0 0) (tInst 0)) (mE (STflowE z0 0))
        (fun j => svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0)
          ((splitEquiv 3 (sz0.L 0) (sz0.W 0)).symm i) j) ω ∧
    ∑ k, (blkCoef2 3 (sz0.L 0) (sz0.W 0) a k : ℂ) *
        ((greenBlk 3 (sz0.L 0) (sz0.W 0) (STflowE z0 0) (tInst 0)
          (Sizes.seqHflow sz0 0 (tInst 0) ω) true k k - mE (STflowE z0 0))
          - condDiagBlk sz0 (STflowE z0) tInst 0 ω k)
      = flucAvg sz0 0 (tInst 0) (zt (STflowE z0 0) (tInst 0)) (mE (STflowE z0 0))
        (fun j : Idx 3 (sz0.L 0) (sz0.W 0) =>
          if (split 3 (sz0.L 0) (sz0.W 0) j).1 = a then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0) ω ∧
    ∑ k, (svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i k : ℂ) *
        (greenBlk 3 (sz0.L 0) (sz0.W 0) (STflowE z0 0) (tInst 0)
          (Sizes.seqHflow sz0 0 (tInst 0) ω) true k k - mE (STflowE z0 0))
      = ∑ j, (svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0)
            ((splitEquiv 3 (sz0.L 0) (sz0.W 0)).symm i) j : ℂ) *
          (green (Sizes.seqHflow sz0 0 (tInst 0) ω) (zt (STflowE z0 0) (tInst 0)) j j
            - mE (STflowE z0 0)) :=
  ⟨FlucAvgDet_greenBlk_true_apply _ _ _ i i, FlucAvgDet_condDiagBlk_eq sz0 (STflowE z0) tInst 0 ω i,
    FlucAvgDet_row_sum_eq sz0 (STflowE z0) tInst 0 ω i,
    FlucAvgDet_blk_sum_eq sz0 (STflowE z0) tInst 0 ω a,
    FlucAvgDet_ibp_sum_eq sz0 (STflowE z0) tInst 0 ω i⟩

end Instances

end RBM.Green

end
