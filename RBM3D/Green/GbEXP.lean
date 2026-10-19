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
display and `gbEXPV3`

Paper: arXiv:2507.20274, Lemma 3.1 (`lem_GbEXP`), (3.2) `GiiGEX`, (3.3) `GijGEX`,
(3.4) `initialGT2` (with the window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` stated before it), (3.5) `GavLGEX`;
the proof is "that of Lemma 4.1 in [YY_25]".  The fixed-time fluctuation averaging and the
integration-by-parts displays are those of the proof of [YY_25, Lemma 4.1]; there the weights
satisfy `0 ≤ |t_k| ≤ W^{-1}`, `∑|t_k| ≤ 1`, in `d` dimensions `W^{-d}` (a `BoundedWeight`).  The
file builds on `Green/{LocalLaw, FlucThreshold, FlucIterGain, IBPRem, CondDom, EntryDom, LDE,
FlucVanish, Pins}`.

Proof outline: `LocalLawDetSeq sz E t Ψ` gives, through `flucGain_of_localLaw`
(in Green/FlucThreshold.lean), the gain `FlucGainUpTo'` with `ρ = 4 δ`, `δ = detFlucDelta Ψ θ`, and
the weight condition `W^{-d} ≤ ρ²`; the moment bound `integral_norm_flucAvg_pow_le_iter_budget` at
the budgets `M = K = 2p` for the two weight families (row `svarF`, block `W^{-d} 1(k ∈ 𝓘_a)`) and
Markov (`perTimeDomAt_of_moment`) give `‖flucAvg‖ ≺ 4 δ²`; the choice
`θ = detFlucTheta a τ < τ/16` turns it into `≺ Ψ²`; the bridge `splitEquiv` carries it to the
block-product index of the statement (`fixedTimeFAThm`).  The IBP display: `perTimeDomAt_ibpRem`
(`Green/IBPRem.lean`) and the union over the `size` sites `k` (`IBPDet_weighted_of_rem`) give
`≺ Ψ²`, then the same bridge (`ibpDetThm`).  `gbEXPV3` is `LocalLaw_gbEXPV3Theorem_of_fa_ibp`
(in Green/LocalLaw.lean) with these two.

## Contents (namespace `Green`)

1. the threshold against `Ψ` (floor chain `FlucAvgDet_floor_le`, `detFlucDelta ≤ size^{2θ} Ψ`,
   `size^{τ/2}·4δ² ≤ size^τ Ψ²`: private);
2.-4. `FlucAvgDet_iter_budget_eventually`, `FlucAvgDet_family`, `FlucAvgDet_budgetFamily_absorb`,
   `FlucAvgDet_weighted`;
5. the bridge `FlucAvgDet_greenBlk_true_apply`, `_greenBlk_sub_eq`, `_condDiagBlk_eq`,
   `_row_sum_eq`, `_blk_sum_eq`, `_ibp_sum_eq`, `FlucAvgDet_perTime_reindex`;
6. `fixedTimeFAThm`; 7.-8. `IBPDet_norm_condExpDiag_sub_le_two_phi`, `IBPDet_weighted_of_rem`,
   `IBPDet_hEnv`, `IBPDet_hΨ1`; 9. `ibpDetThm`;
10. `gbEXPV3`, `stGbEXP_holds`, `stStep1_holds` (the forms of the statements used by the induction).

## Conventions

* **The floor** is the paper's `W^{-d/2} ≤ Ψ` (the floor of `FixedTimeFAThm`, `IBPDetThm`).  The
  regularising floor `(N + 4)^{-2} ≤ Ψ` follows from `W^d ≤ N = (W L)^d`
  (`FlucAvgDet_floor_le`, every `d`), and `W^{-d} ≤ Ψ²` is `(W^{-d/2})² = W^{-d}`; the polynomial
  floor of the IBP remainder is `IBPRem_hΨlow_of_floor` (floor `W^{-d/2}`, `B = 1`).
* **Weights and counts**: the row `j ↦ S_{ij}` is a `BoundedWeight` with `c = W^{-d}` on
  `#A = (2d + 1) W^d` sites (`boundedWeight_svarF`), the block family is uniform, hence bounded,
  with `c = W^{-d}`, `#A = W^d`; the hypothesis `c ≤ ρ²` is the second conjunct
  `(W^d)⁻¹ ≤ (2 (2 δ))²` of `flucGain_of_localLaw`; `hcW : cw n ≤ (W^d)⁻¹`.  The diagonal
  coefficient is `S_ii = W^{-d} (1 + 2 d g²)⁻¹ ≤ W^{-d}` (`svarF_diag`).
* **`hd`**: `fixedTimeFAThm` and `ibpDetThm` take `1 ≤ d`: `2 p ≤ #A` uses `W ≤ W^d`, and
  `perTimeDomAt_ibpRem` carries `hd`; `gbEXPV3`, `stGbEXP_holds`, `stStep1_holds` take `3 ≤ d`
  (`localLawDetThm`).
* **The bridge**: the statements are on `Vtx d L W` with `svar`, `blkCoef2`, `greenBlk`; the
  private `FlucAvgDet_svar_eq_svarF` (`svarF_eq_svar` and `split ∘ (splitEquiv …).symm = id`)
  transports to `Idx d L W`; `FlucAvgDet_greenBlk_true_apply` concludes with `green`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The threshold against `Ψ` -/

/-- `Tendsto sz.size` from `SizeTendsto`. -/
private theorem FlucAvgDet_tendsto_size {d : ℕ} {sz : Sizes d} (hsz : sz.SizeTendsto) :
    Tendsto sz.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp hsz

/-- **The regularising floor is below the floor of `Ψ`.**  `W^d ≤ (W L)^d = N` (`L ≥ 1`, every `d`),
so `(N + 4)^{-2} ≤ W^{-d/2}`; the floor `W^{-d/2} ≤ Ψ` ((3.4) `initialGT2`) then gives
`(N + 4)^{-2} ≤ Ψ`. -/
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

/-- Real-variable core of `FlucAvgDet_detFlucDelta_le_rpow_mul_psi` (`x` is the size): once the
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
loss is at most `size^{2θ}` (with the floor `W^{-d/2} ≤ Ψ`). -/
private theorem FlucAvgDet_detFlucDelta_le_rpow_mul_psi {d : ℕ} (sz : Sizes d)
    (hsz : sz.SizeTendsto) {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hΨlo : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) :
    ∀ᶠ n : ℕ in atTop, detFlucDelta sz Ψ θ n ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * θ) * Ψ n := by
  filter_upwards [hΨlo, hsz.eventually_ge_atTop 4] with n hΨn hn4
  exact FlucAvgDet_delta_le_core hθ hn4 (FlucAvgDet_floor_le sz hΨn)

/-- Real-variable core of `FlucAvgDet_detFlucDelta_scale_absorb` (dimension-free). -/
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
stochastic-domination tolerance. -/
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

/-! ## 2. The moment bound gives `≺` -/

/-- **The `2p`-th moment of the fluctuation average gives `‖flucAvg‖ ≺ ρ B`, per time**: the gain
`FlucGainUpTo'` at the budgets `M = K = 2p` with `B_p ≤ K_p B_m` and `ρ = ep`, a bounded weight
`c ≤ ρ²` on a set with `2 p ≤ #A` eventually, and Markov (`perTimeDomAt_of_moment`, where the
size-index `n` carries `size n` in every power). -/
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

/-! ## 3. The family at the threshold `δ = detFlucDelta` -/

/-- **The fluctuation average is `≺ 4 δ²` at the movable threshold.**  The gain comes from the
local law (`flucGain_of_localLaw`) with the budgets `M = K = 2p`, `B_p = (8 C_{2p} + 4) δ`,
`ρ = 4 δ`; the weight condition `c ≤ ρ²` is its second conjunct, `(W^d)⁻¹ ≤ (2 (2 δ))²`, with
`c ≤ (W^d)⁻¹` (row: `c = W^{-d}`, `#A = (2d + 1) W^d`; block: `c = W^{-d}`, `#A = W^d`). -/
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

/-! ## 4. Choosing the threshold after the tolerance -/

/-- A family of positive thresholds gives domination at the original squared entry bound,
because the threshold exponent can be chosen after the requested tolerance.  For `τ, D`, take
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

/-- **The weighted fluctuation average is `≺ Ψ²`, per time** (the fine-lattice form of the statement):
the local law, the floor `W^{-d/2} ≤ Ψ`, the ceiling `Ψ ≤ size^{-a}` and `size^{-K_η} ≤ η_t` give
`‖flucAvg‖ ≺ Ψ²` for any bounded weight family with `c ≤ W^{-d}` and `2 p ≤ #A` eventually. -/
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
equivalence `splitEquiv` (`Idx ≃ Vtx`), the identity `svarF_eq_svar` (`svar` is on `Vtx` and
`svarF` is `svar` read through `split`) and `Matrix.inv_submatrix_equiv`. -/

section Bridge

/-- `greenBlk` at block-product indices is the fine-lattice resolvent at the `splitEquiv`
coordinates (`Matrix.inv_submatrix_equiv`). -/
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
`(splitEquiv …).symm k`. -/
theorem FlucAvgDet_greenBlk_sub_eq {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz) (k : Vtx d (sz.L n) (sz.W n)) :
    greenBlk d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) true k k
        - mE (E n)
      = greenDiagCentered sz n (t n) (zt (E n) (t n)) (mE (E n))
          ((splitEquiv d (sz.L n) (sz.W n)).symm k) ω := by
  rw [FlucAvgDet_greenBlk_true_apply]
  rfl

/-- `condDiagBlk` at a block-product index is `condExpDiag` at the fine index
`(splitEquiv …).symm k`. -/
theorem FlucAvgDet_condDiagBlk_eq {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz) (k : Vtx d (sz.L n) (sz.W n)) :
    condDiagBlk sz E t n ω k
      = condExpDiag sz n (t n) (zt (E n) (t n)) (mE (E n))
          ((splitEquiv d (sz.L n) (sz.W n)).symm k) ω := by
  unfold condDiagBlk condExpDiag
  congr 1
  funext ω'
  exact FlucAvgDet_greenBlk_sub_eq sz E t n ω' k

/-- `svar` on `Vtx` is `svarF` on `Idx` read through `splitEquiv` (`svarF_eq_svar` and
`split ∘ (splitEquiv …).symm = id`). -/
private theorem FlucAvgDet_svar_eq_svarF {d L W : ℕ} [NeZero L] [NeZero W] (g : ℝ)
    (i k : Vtx d L W) :
    svar d L W g i k
      = svarF d L W g ((splitEquiv d L W).symm i) ((splitEquiv d L W).symm k) := by
  rw [svarF_eq_svar]
  have h1 : split d L W ((splitEquiv d L W).symm i) = i := (splitEquiv d L W).apply_symm_apply i
  have h2 : split d L W ((splitEquiv d L W).symm k) = k := (splitEquiv d L W).apply_symm_apply k
  rw [h1, h2]

/-- **The row family on `Vtx` is `flucAvg` with the weight `svarF` on `Idx`**:
`∑_k S_{ik} ((G_kk - m) - E_k(G_kk - m)) = ∑_j S_{ij} Z_j` (`svarF_eq_svar`, `splitEquiv`). -/
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
`blkCoef2` is that weight read through `splitEquiv` (`flucVanish_blockAvg2_eq_blkCoef2`). -/
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
(`svarF_eq_svar`, `splitEquiv`). -/
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
`ζ' n v = ζ n (g n v)` pointwise, the domination of `(ξ, ζ)` gives that of `(ξ', ζ')`. -/
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

/-- **The endpoint `fixedTimeFAThm`.**  Both families of the fluctuation-averaging estimate at
`x = condDiagBlk`, with the bound `Ψ²`: the row family `t_k = S_{ik}`
(`boundedWeight_svarF`, `c = W^{-d}`, `#A = (2d + 1) W^d`) and the block family
`t_k = W^{-d} 1(k ∈ 𝓘_a)` (`uniformWeight_blockAvg2`, `c = W^{-d}`, `#A = W^d`), on the fine
lattice (`FlucAvgDet_weighted`, with the `η` input `size^{-1} ≤ η_t` from
`eta_lower_of_rangeCond`), then transported to `Vtx` by the bridge.  No hypothesis is added to
`FixedTimeFAThm` except `hd : 1 ≤ d`: `2 p ≤ #A` uses `W ≤ W^d`. -/
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

/-! ## 7. The weighted reduction of the IBP remainder -/

/-- The actual conditional IBP residual, with the diagonal coefficient kept: with
`‖ibpRem (i,k)‖ ≤ A Φ` for `k ≠ i`, `‖ibpRem (i,i)‖ ≤ A` and `W^{-d} ≤ Φ`, the residual is
`≤ 2 A Φ`.  The diagonal coefficient is `S_ii = W^{-d} (1 + 2 d g²)⁻¹ ≤ W^{-d}`. -/
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

/-- **The weighted IBP display from the remainder bound**: from `ibpRem (i,k) ≺ Ψ²` off the
diagonal and `≺ 1` on it (`hrem`), and `W^{-d} ≤ Ψ²`,
`|E_i(G_ii - m) - t m² Σ_k S_ik (G_kk - m)| ≺ Ψ²`, per time.  The union is over the
`size = (W L)^d` sites `k` of the row (spending `D + 2` on `D`); `i` stays outside the
probability. -/
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

/-! ## 8. The eventual inputs of `perTimeDomAt_ibpRem` -/

/-- The envelope input `hEnv` at `K_env = 3` from `size^{-1} ≤ η_t` (`K_η = 1`): `η⁻¹ ≤ size`, so
`(η⁻¹ + 1)² ≤ (size + 1)² ≤ size³` once `size ≥ 4` (dimension-free). -/
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

/-- The ceiling `Ψ² ≤ 1` from `Ψ ≤ size^{-a}`. -/
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
`IBPDet_weighted_of_rem`).  The polynomial floor `size^{-1} ≤ Ψ²` is
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

/-! ## 9. The endpoint `ibpDetThm` -/

section IBPEndpoint

variable {d : ℕ}

/-- **The endpoint `ibpDetThm`.**  The remainder `ibpRem ≺ 1` (diagonal), `≺ Ψ²` (off the
diagonal) from `perTimeDomAt_ibpRem` (`K_env = 3`, `B = 1`, the good event at
`θ = detFlucTheta a 1`), then the weighted reduction `IBPDet_weighted_of_rem`, then the bridge to
`Vtx` (`splitEquiv`, `svarF_eq_svar`).  No hypothesis is added to `IBPDetThm` except
`hd : 1 ≤ d` (carried by `perTimeDomAt_ibpRem`). -/
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

/-- **`lem_GbEXP`** (Lemma 3.1): `GbEXPHypV3 sz κ 𝔠 𝔡 δ`
for every size sequence `sz : Sizes d` with `3 ≤ d` and every `κ, 𝔠, 𝔡, δ > 0`, from
`localLawDetThm`, `fixedTimeFAThm`, `ibpDetThm` (`LocalLaw_gbEXPV3Theorem_of_fa_ibp`).
`hd : 3 ≤ d` is that of `localLawDetThm`; the other two need `1 ≤ d`. -/
theorem gbEXPV3 (hd : 3 ≤ d) : GbEXPV3Theorem d :=
  LocalLaw_gbEXPV3Theorem_of_fa_ibp hd (fixedTimeFAThm (by omega)) (ibpDetThm (by omega))

/-- **(3.2) `GiiGEX`, (3.3) `GijGEX`, (3.5) `GavLGEX` of `lem_GbEXP` in the form of `STGbEXP`**:
the three parts hold for every flow (`stGbEXP_of_v3`). -/
theorem stGbEXP_holds (hd : 3 ≤ d) : STGbEXP d := stGbEXP_of_v3 (gbEXPV3 hd)

/-- **Step 1 of the proof of Theorem 2.24 (`lem:main_ind`)**: `STStep1 d` for every `d ≥ 3`, from
`step1TargetV3_holds` under the two parts (3.2) `GiiGEX`, (3.3) `GijGEX` of `lem_GbEXP`
(`stGbEXPii_of_v3`, `stGbEXPij_of_v3`). -/
theorem stStep1_holds (hd : 3 ≤ d) : STStep1 d :=
  RBM.Ind.step1TargetV3_holds d (stGbEXPii_of_v3 (gbEXPV3 hd)) (stGbEXPij_of_v3 (gbEXPV3 hd))

end GbEXPEndpoint

end RBM.Green

end
