/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RBM3D.Green.EntryCore
import RBM3D.Green.LDEQuad

/-!
# The Hanson–Wright layer, second half: master identity, moment recursion, moment bound

Port of `RBM2D/Green/LDEQuadMom.lean` (lines 1-787, up to the private `Checks` section) of RBM2D at
commit `c9a24cf` (T2044, portmap P.7 row S1-13), to the `d`-dimensional sequence model of
`RBM3D/Gauss/FineModel.lean`, on top of the first half `RBM3D/Green/LDEQuad.lean` (T2031) and the
resolvent core `RBM3D/Green/EntryCore.lean` (T2029).  The paper (arXiv:2507.20274) does not state
this file as a lemma: it is abstract Gaussian calculus on independent centred coordinates, and
involves neither `Z_L^d` nor the variance profile `S`; the statements are those of RBM2D after rule
R1 of `docs/tickets/ST1-COMMON.md` (`d : Sizes` becomes `sz : Sizes d`, `Sizes.SeqΩ d`,
`Sizes.seqP d`, `Sizes.seqGvar d`, `Tame d`, `GaussIBP d`, `RowChaos d κ` become the same with `sz`;
namespace `RBM.Green.RowChaos`).  No exponent of `W`, `L`, `N` occurs, and the constants `2p − 1`,
`2q + 1` are dimension-free.  Only the `Checks` section at the end is dimension-specific (`d = 3`).
A reference `(4.7)` in a docstring below is the quadratic large deviation estimate of the
resolvent-entry layer, which `norm_chaos_sq_eq_ldeQuadLHS` and `Vq_eq_ldeQuadRHS` connect to
`RBM.Green.ldeQuadLHS`, `RBM.Green.ldeQuadRHS` (`RBM3D/Green/EntryCore.lean`).

## Main results (all in `RBM.Green.RowChaos`)

* `integral_chaos_mul` — **the master integration-by-parts identity**:
  `2 ∫ Q F = ∑_k w_k ∫ (∂_{a_k}Q ∂_{a_k}F + ∂_{b_k}Q ∂_{b_k}F)` for every tame `F`.
* `moment_recursion` — with `F = Q^q \bar Q^{q+1}`,
  `2 E|Q|^{2(q+1)} = 2q E[R Q^{q−1}\bar Q^{q+1}] + (q+1) E[T Q^q \bar Q^q]`.
* `two_mul_mom_succ_le` — **the Hanson–Wright recursion**,
  `2 E|Q|^{2(q+1)} ≤ (2q+1) E[T |Q|^{2q}]`.
* `integrable_norm_pow` — `‖Q‖^n` is integrable.
* `mom_succ_le` — **the moment bound** `E|Q|^{2p} ≤ (2p−1)^p E[T^p]`, `p ≥ 1`: the recursion
  closed by the pointwise Young inequality `RBM.Green.young_pow` with the rational parameter
  `K = 2p−1` (no `rpow`, no Hölder inequality).
* `norm_chaos_sq_eq_ldeQuadLHS`, `Vq_eq_ldeQuadRHS` — the two sides are literally
  `RBM.Green.ldeQuadLHS` and `t²·RBM.Green.ldeQuadRHS` (pure reindexing).

## Hypotheses carried

`RBM.Green.GaussIBP sz` (T2031; proved for the model by S1-19) is a hypothesis `hG` of exactly the
declarations that integrate: `integral_chaos_mul`, `moment_recursion`,
`integrable_of_tame_ofReal`, `integrable_norm_pow`, `integrable_Tq_mul`, `norm_integral_Rq_le`,
`two_mul_mom_succ_le`, `integrable_Tq_pow` and `mom_succ_le`.  Nothing else is assumed.

## What is **not** in this file

1. The row isometry `E[\bar h_l h_{l'} Z] = δ_{l l'} σ_l E[Z]`, the exact variance
   `E|Q|² = E[Vq]` and the identity `E[T] = 2 E[Vq]` (not in RBM2D at `c9a24cf` either).
2. The positive-chaos bound `E[T^p] ≤ C_p E[Vq^p]` (a separate file).
3. `GaussIBP` for the model.

## Deviations from the paper

* `Vq_eq_ldeQuadRHS` carries a factor `t²` (`Vq = t² · ldeQuadRHS`) and the hypothesis
  `σ_k = t S_{ki}` as well as `σ_k = t S_{ik}`, because `E|H_{ik}|² = t S_{ik}` for the flow
  `H_t = √t X` while `ldeQuadRHS` is written with `S`.
* The centring constant is `∑_k σ_k B_{kk}` with `σ_k = E|h_k|²`; the paper writes
  `t ∑_k S_{ik} B_{kk}`.  They agree in the model (`σ_k = t S_{ik}`), and the agreement is a
  hypothesis of `norm_chaos_sq_eq_ldeQuadLHS`.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Finset RBM.Gauss
open scoped NNReal

variable {d : ℕ} {sz : Sizes d}

namespace RowChaos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (C : RowChaos sz κ)

/-! #### The master integration-by-parts identity -/

section IBP

variable (hG : GaussIBP sz)
include hG

/-- **The master identity.**  For any tame `F` whose derivatives along the two coordinates of
each row index are `FA k`, `FB k`,

`2 ∫ Q F = ∑_k w_k ∫ (∂_{a_k}Q · ∂_{a_k}F + ∂_{b_k}Q · ∂_{b_k}F)`.

This is Gaussian integration by parts applied once to each of the `2|κ|` coordinates of the row,
using Euler's identity `∑_α ω_α ∂_α Q = 2(Q + ∑_k σ_k B_{kk})` to produce `Q` on the left and
`∂_α ∂_α Q = 2 r² B_{kk}` to cancel the centring constant. -/
theorem integral_chaos_mul {F : Sizes.SeqΩ sz → ℂ} {FA FB : κ → Sizes.SeqΩ sz → ℂ}
    (hF : Tame sz F) (hFA : ∀ k, Tame sz (FA k)) (hFB : ∀ k, Tame sz (FB k))
    (hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)))
    (hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false))) :
    2 * ∫ ω, C.chaos ω * F ω ∂(Sizes.seqP sz)
      = ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP sz) := by
  classical
  have htB : ∀ k : κ, Tame sz fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω := fun k =>
    ((Tame.const (sz := sz) (2 * (C.r : ℂ) ^ 2)).mul (C.tameB k k)).mul hF
  have htsg : ∀ k : κ, Tame sz fun ω => (C.sg k : ℂ) * C.B ω k k * F ω := fun k =>
    ((Tame.const (sz := sz) ((C.sg k : ℂ))).mul (C.tameB k k)).mul hF
  have hcast : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2) = ((C.sg k : ℝ) : ℂ) := by
    intro k
    have : C.sg k = 2 * C.r ^ 2 * C.w k := rfl
    rw [this]; push_cast; ring
  -- the two Stein identities at the row index `k`
  have hIA : ∀ k : κ, ∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(Sizes.seqP sz)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(Sizes.seqP sz) := by
    intro k
    have hst := hG.stein (C.co k true) (fun ω => C.dA ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dA ω k * FA k ω)
      ((C.tamedA k).mul hF) ((htB k).add ((C.tamedA k).mul (hFA k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedA k).mul (hFA k)).integrable hG), mul_add]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dA_true k ω).fun_mul (hdFA k ω)
      simp only [hself] at hmul
      exact hmul
  have hIB : ∀ k : κ, ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(Sizes.seqP sz)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(Sizes.seqP sz) := by
    intro k
    have hst := hG.stein (C.co k false) (fun ω => C.dB ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dB ω k * FB k ω)
      ((C.tamedB k).mul hF) ((htB k).add ((C.tamedB k).mul (hFB k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG), mul_add]
      have hgv : ((Sizes.seqGvar sz (C.co k false) : ℝ) : ℂ) = ((C.w k : ℝ) : ℂ) := by
        rw [C.gvar_tag k]; rfl
      rw [hgv]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dB_false k ω).fun_mul (hdFB k ω)
      simp only [hself] at hmul
      exact hmul
  -- the left-hand side, by Euler's identity
  have hEuler : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(Sizes.seqP sz)
      = ∑ k, (∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(Sizes.seqP sz)
        + ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(Sizes.seqP sz)) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
          + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) := by
      intro ω
      rw [← C.sum_coord_mul_deriv ω, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hti : ∀ k : κ, Tame sz fun ω => (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) :=
      fun k => (Tame.coord (C.co k true)).mul ((C.tamedA k).mul hF)
    have hti' : ∀ k : κ, Tame sz fun ω => (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) :=
      fun k => (Tame.coord (C.co k false)).mul ((C.tamedB k).mul hF)
    calc ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(Sizes.seqP sz)
        = ∫ ω, ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(Sizes.seqP sz) := by
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = ∑ k, ∫ ω, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(Sizes.seqP sz) :=
          MeasureTheory.integral_finsetSum _ fun k _ => ((hti k).add (hti' k)).integrable hG
      _ = _ := Finset.sum_congr rfl fun k _ =>
          MeasureTheory.integral_add ((hti k).integrable hG) ((hti' k).integrable hG)
  -- the left-hand side, expanded
  have hsplit : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(Sizes.seqP sz)
      = 2 * ∫ ω, C.chaos ω * F ω ∂(Sizes.seqP sz) + 2 * ∫ ω, C.cen ω * F ω ∂(Sizes.seqP sz) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = 2 * (C.chaos ω * F ω) + 2 * (C.cen ω * F ω) := fun ω => by ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw),
      MeasureTheory.integral_add
        (((Tame.const (sz := sz) 2).mul (C.tamechaos.mul hF)).integrable hG)
        (((Tame.const (sz := sz) 2).mul (C.tamecen.mul hF)).integrable hG),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the centring constant
  have hcen : ∑ k, ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
      = ∫ ω, C.cen ω * F ω ∂(Sizes.seqP sz) := by
    rw [← MeasureTheory.integral_finsetSum _ fun k _ => (htsg k).integrable hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show _ = (∑ k, (C.sg k : ℂ) * C.B ω k k) * F ω
    rw [Finset.sum_mul]
  -- put everything together
  have hkey := hEuler
  rw [hsplit] at hkey
  rw [Finset.sum_congr rfl fun k _ => by rw [hIA k, hIB k]] at hkey
  have hrearr : ∑ k, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(Sizes.seqP sz))
      + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(Sizes.seqP sz)))
      = 2 * ∫ ω, C.cen ω * F ω ∂(Sizes.seqP sz)
        + ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP sz) := by
    have hstep : ∀ k : κ, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
          + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(Sizes.seqP sz))
        + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
          + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(Sizes.seqP sz)))
        = 2 * ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(Sizes.seqP sz)
          + (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP sz) := by
      intro k
      rw [MeasureTheory.integral_add (((C.tamedA k).mul (hFA k)).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG)]
      ring
    rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_add_distrib, ← Finset.mul_sum, hcen]
  rw [hrearr] at hkey
  have := hkey
  linear_combination this

end IBP

/-! #### The two quadratic sums -/

theorem eps_sq_complex (k : κ) : ((C.eps k : ℂ)) ^ 2 = 1 := by
  have h := C.eps_sq k
  have h2 : ((C.eps k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [h]
  push_cast at h2
  exact h2

theorem sg_complex (k : κ) : ((C.sg k : ℝ) : ℂ) = 2 * (C.r : ℂ) ^ 2 * ((C.w k : ℝ) : ℂ) := by
  show ((2 * C.r ^ 2 * C.w k : ℝ) : ℂ) = _
  push_cast; ring

theorem conj_dA (ω : Sizes.SeqΩ sz) (k : κ) : (starRingEnd ℂ) (C.dA ω k)
    = (C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) ((C.r : ℂ) * (C.U ω k + C.V ω k)) = _
  simp [Complex.conj_ofReal]

theorem conj_dB (ω : Sizes.SeqΩ sz) (k : κ) : (starRingEnd ℂ) (C.dB ω k)
    = (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
      ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) = _
  simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `∑_k w_k ((∂_{a_k}Q)² + (∂_{b_k}Q)²) = 2 R`. -/
theorem sum_w_sq (ω : Sizes.SeqΩ sz) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2) = 2 * C.Rq ω := by
  have hR : (2 : ℂ) * C.Rq ω = ∑ k, 2 * (((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) := by
    show (2 : ℂ) * (∑ k, ((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) = _
    rw [Finset.mul_sum]
  rw [hR]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hes := C.eps_sq_complex k
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [C.sg_complex k]
  show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) ^ 2
      + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) ^ 2) = _
  linear_combination (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2
      * (C.eps k : ℂ) ^ 2) * hI
    - (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2) * hes

/-- `∑_k w_k (|∂_{a_k}Q|² + |∂_{b_k}Q|²) = T`. -/
theorem sum_w_normSq (ω : Sizes.SeqΩ sz) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) = ((C.Tq ω : ℝ) : ℂ) := by
  have hstep : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))
      = ((C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) := by
    intro k
    have hU : ((‖C.U ω k‖ ^ 2 : ℝ) : ℂ) = C.U ω k * (starRingEnd ℂ) (C.U ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have hV : ((‖C.V ω k‖ ^ 2 : ℝ) : ℂ) = C.V ω k * (starRingEnd ℂ) (C.V ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    rw [Complex.ofReal_mul, Complex.ofReal_add, hU, hV, C.sg_complex k, C.conj_dA, C.conj_dB]
    have hes := C.eps_sq_complex k
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) *
          ((C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)))
        + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) *
          ((-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
            ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) = _
    linear_combination (-(((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.eps k : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k))))) * hI
      + (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) * hes
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Complex.ofReal_sum]
  rfl

theorem tameRq : Tame sz C.Rq :=
  Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.sg k : ℝ) : ℂ)).mul (C.tameU k) |>.mul (C.tameV k)

theorem tameTq : Tame sz fun ω => ((C.Tq ω : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω : ℝ) : ℂ))
      = fun ω => ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
        + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) := by
    funext ω; rw [C.sum_w_normSq ω]
  rw [hfun]
  exact Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.w k : ℝ) : ℂ)).mul
    (((C.tamedA k).mul (C.tamedA k).conj).add ((C.tamedB k).mul (C.tamedB k).conj))

/-! #### The moment recursion -/

section Recursion

variable (hG : GaussIBP sz)
include hG

/-- **The moment recursion.**  Integration by parts once in each row coordinate, applied to
`F = Q^q \bar Q^{q+1}`, gives

`2 E[|Q|^{2(q+1)}] = 2q E[R Q^{q-1} \bar Q^{q+1}] + (q+1) E[T Q^q \bar Q^q]`,

with `R = ∑_k σ_k U_k V_k` and `T = ∑_k σ_k (|U_k|² + |V_k|²)`.  Since `‖R‖ ≤ T/2` this is the
Hanson–Wright recursion `E|Q|^{2p} ≤ (2p-1)/2 · E[T |Q|^{2p-2}]`. -/
theorem moment_recursion (q : ℕ) :
    2 * ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(Sizes.seqP sz)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(Sizes.seqP sz)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(Sizes.seqP sz) := by
  classical
  set F : Sizes.SeqΩ sz → ℂ :=
    fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) with hFdef
  set FA : κ → Sizes.SeqΩ sz → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dA ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dA ω k)) with hFAdef
  set FB : κ → Sizes.SeqΩ sz → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dB ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dB ω k)) with hFBdef
  have hFt : Tame sz F := (C.tamechaos.pow q).mul (C.tamechaos.conj.pow (q + 1))
  have hFAt : ∀ k, Tame sz (FA k) := fun k =>
    ((((Tame.const (sz := sz) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedA k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((Tame.const (sz := sz) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedA k).conj))
  have hFBt : ∀ k, Tame sz (FB k) := fun k =>
    ((((Tame.const (sz := sz) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedB k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((Tame.const (sz := sz) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedB k).conj))
  have hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)) := by
    intro k ω
    have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_true k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false)) := by
    intro k ω
    have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_false k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hmain := C.integral_chaos_mul hG hFt hFAt hFBt hdFA hdFB
  -- the left-hand side
  have hL : ∫ ω, C.chaos ω * F ω ∂(Sizes.seqP sz)
      = ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(Sizes.seqP sz) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show C.chaos ω * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) = _
    ring
  -- the right-hand side, pointwise
  have hptw : ∀ ω : Sizes.SeqΩ sz, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
      = 2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
        + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q)) := by
    intro ω
    have hsplit : ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
        = ((q : ℂ) * (C.chaos ω ^ (q - 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2))
          + (((q + 1 : ℕ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
                + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hFAdef, hFBdef]
      ring
    rw [hsplit, C.sum_w_sq ω, C.sum_w_normSq ω]
    push_cast
    ring
  -- assemble
  have htR : Tame sz fun ω => C.Rq ω * (C.chaos ω ^ (q - 1)
      * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) :=
    C.tameRq.mul ((C.tamechaos.pow (q - 1)).mul (C.tamechaos.conj.pow (q + 1)))
  have htT : Tame sz fun ω => ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
      * (starRingEnd ℂ) (C.chaos ω) ^ q) :=
    C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))
  have htk : ∀ k : κ, Tame sz fun ω =>
      ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) := fun k =>
    (Tame.const (sz := sz) ((C.w k : ℝ) : ℂ)).mul
      (((C.tamedA k).mul (hFAt k)).add ((C.tamedB k).mul (hFBt k)))
  have hR : ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP sz)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(Sizes.seqP sz)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(Sizes.seqP sz) := by
    calc ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP sz)
        = ∑ k, ∫ ω, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP sz) :=
          Finset.sum_congr rfl fun k _ => (MeasureTheory.integral_const_mul _ _).symm
      _ = ∫ ω, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(Sizes.seqP sz) :=
          (MeasureTheory.integral_finsetSum _ fun k _ => (htk k).integrable hG).symm
      _ = ∫ ω, (2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
              * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
              * (starRingEnd ℂ) (C.chaos ω) ^ q))) ∂(Sizes.seqP sz) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = _ := by
          rw [MeasureTheory.integral_add
            (((Tame.const (sz := sz) (2 * (q : ℂ))).mul htR).integrable hG)
            (((Tame.const (sz := sz) ((q : ℕ) + 1 : ℂ)).mul htT).integrable hG),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hL] at hmain
  rw [hmain, hR]

end Recursion

/-! #### The real form of the recursion -/

/-- `E|Q|^{2q}`. -/
noncomputable def mom (q : ℕ) : ℝ := ∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP sz)

/-- `E[T |Q|^{2q}]`, the right-hand side of the recursion. -/
noncomputable def momT (q : ℕ) : ℝ := ∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP sz)

theorem ofReal_norm_pow (ω : Sizes.SeqΩ sz) (q : ℕ) :
    ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) = C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q := by
  have h2 : ((‖C.chaos ω‖ ^ 2 : ℝ) : ℂ) = C.chaos ω * (starRingEnd ℂ) (C.chaos ω) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [pow_mul, Complex.ofReal_pow, h2, mul_pow]

theorem tame_ofReal_norm_pow (q : ℕ) :
    Tame sz fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q :=
    funext fun ω => C.ofReal_norm_pow ω q
  rw [hfun]
  exact (C.tamechaos.pow q).mul (C.tamechaos.conj.pow q)

theorem tame_ofReal_Tq_mul (q : ℕ) :
    Tame sz fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => ((C.Tq ω : ℝ) : ℂ) *
        (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) := by
    funext ω
    rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]
  rw [hfun]
  exact C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))

omit [DecidableEq κ] in
theorem ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.sq_norm]

theorem mom_nonneg (q : ℕ) : 0 ≤ C.mom q :=
  MeasureTheory.integral_nonneg fun ω => by positivity

theorem momT_nonneg (q : ℕ) : 0 ≤ C.momT q :=
  MeasureTheory.integral_nonneg fun ω => mul_nonneg (C.Tq_nonneg ω) (by positivity)

omit [DecidableEq κ] in
theorem integral_ofReal' (f : Sizes.SeqΩ sz → ℝ) :
    ∫ ω, ((f ω : ℝ) : ℂ) ∂(Sizes.seqP sz) = ((∫ ω, f ω ∂(Sizes.seqP sz) : ℝ) : ℂ) := by
  have h := _root_.integral_ofReal (𝕜 := ℂ) (f := f) (μ := Sizes.seqP sz)
  simpa using h

theorem integral_chaos_pow (q : ℕ) :
    ∫ ω, C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q ∂(Sizes.seqP sz) = ((C.mom q : ℝ) : ℂ) := by
  show _ = ((∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP sz) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => ‖C.chaos ω‖ ^ (2 * q))]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun ω => (C.ofReal_norm_pow ω q).symm)

theorem integral_Tq_chaos_pow (q : ℕ) :
    ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(Sizes.seqP sz)
      = ((C.momT q : ℝ) : ℂ) := by
  show _ = ((∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(Sizes.seqP sz) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q)
    = ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]

section Real

variable (hG : GaussIBP sz)
include hG

theorem integrable_of_tame_ofReal {f : Sizes.SeqΩ sz → ℝ} (hf : Tame sz fun ω => ((f ω : ℝ) : ℂ)) :
    Integrable f (Sizes.seqP sz) := by
  simpa using (hf.integrable hG).re

theorem integrable_norm_pow (q : ℕ) :
    Integrable (fun ω => ‖C.chaos ω‖ ^ (2 * q)) (Sizes.seqP sz) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_norm_pow q)

theorem integrable_Tq_mul (q : ℕ) :
    Integrable (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)) (Sizes.seqP sz) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_Tq_mul q)

/-- The cross term of the recursion is dominated by half the control. -/
theorem norm_integral_Rq_le (p : ℕ) :
    ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(Sizes.seqP sz)‖
      ≤ C.momT (p + 1) / 2 := by
  have htR : Tame sz fun ω => C.Rq ω * (C.chaos ω ^ p
      * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) :=
    C.tameRq.mul ((C.tamechaos.pow p).mul (C.tamechaos.conj.pow (p + 2)))
  have hbnd : ∀ ω : Sizes.SeqΩ sz,
      ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖
        ≤ 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) := by
    intro ω
    have hnorm : ‖C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)‖
        = ‖C.chaos ω‖ ^ (2 * (p + 1)) := by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add]
      congr 1
      omega
    rw [norm_mul, hnorm]
    have h1 := C.norm_Rq_le ω
    have h2 : (0 : ℝ) ≤ ‖C.chaos ω‖ ^ (2 * (p + 1)) := by positivity
    nlinarith
  calc ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(Sizes.seqP sz)‖
      ≤ ∫ ω, ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖ ∂(Sizes.seqP sz) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) ∂(Sizes.seqP sz) :=
        MeasureTheory.integral_mono ((htR.integrable hG).norm)
          ((C.integrable_Tq_mul hG (p + 1)).const_mul _) hbnd
    _ = C.momT (p + 1) / 2 := by
        rw [MeasureTheory.integral_const_mul]
        show 1 / 2 * C.momT (p + 1) = _
        ring

/-- **The Hanson–Wright recursion, real form**:
`2 E|Q|^{2(q+1)} ≤ (2q+1) E[T |Q|^{2q}]`. -/
theorem two_mul_mom_succ_le (q : ℕ) :
    2 * C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) * C.momT q := by
  have hrec := C.moment_recursion hG q
  rw [C.integral_chaos_pow (q + 1), C.integral_Tq_chaos_pow q] at hrec
  set X : ℂ := ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
    * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(Sizes.seqP sz) with hX
  have hXb : 2 * (q : ℝ) * ‖X‖ ≤ (q : ℝ) * C.momT q := by
    rcases q with _ | p
    · simp
    · have hq : ‖X‖ ≤ C.momT (p + 1) / 2 := by
        rw [hX]
        have hidx : (p + 1 : ℕ) - 1 = p := by omega
        have hidx2 : (p + 1 : ℕ) + 1 = p + 2 := by omega
        rw [hidx, hidx2]
        exact C.norm_integral_Rq_le hG p
      have hm : 0 ≤ C.momT (p + 1) := C.momT_nonneg (p + 1)
      push_cast
      nlinarith [norm_nonneg X]
  have hnorm : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖
      ≤ 2 * (q : ℝ) * ‖X‖ + ((q : ℝ) + 1) * C.momT q := by
    rw [hrec]
    have h1 : ‖2 * (q : ℂ) * X + ((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖
        ≤ ‖2 * (q : ℂ) * X‖ + ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ := norm_add_le _ _
    have h2 : ‖2 * (q : ℂ) * X‖ = 2 * (q : ℝ) * ‖X‖ := by
      rw [norm_mul, norm_mul]
      simp
    have h3 : ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ = ((q : ℝ) + 1) * C.momT q := by
      have hc : ((q : ℕ) + 1 : ℂ) = (((q : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (C.momT_nonneg q),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)]
    linarith
  have hlhs : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖ = 2 * C.mom (q + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (C.mom_nonneg (q + 1))]
    simp
  rw [hlhs] at hnorm
  linarith

/-! #### The paper's right-hand side `Vq`

`Vq ω = ∑_{k,l} σ_k ‖B_{kl}‖² σ_l` is the random control of the paper's quadratic large deviation
estimate.  At `q = 0` the recursion is the identity `2 E|Q|² = E[T]`; the exact variance
`E|Q|² = E[Vq]` needs the row isometry and is not part of this file. -/

/-- The paper's right-hand side `∑_{k,l} σ_k ‖B_{kl}‖² σ_l` (a random quantity, since `B` is). -/
noncomputable def Vq (ω : Sizes.SeqΩ sz) : ℝ := ∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l

omit hG in
theorem Vq_complex (ω : Sizes.SeqΩ sz) : ((C.Vq ω : ℝ) : ℂ)
    = ∑ k, ∑ l, ((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ) *
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)) := by
  show ((∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ofReal_normSq]
  ring

omit hG in
theorem tame_ofReal_Vq : Tame sz fun ω => ((C.Vq ω : ℝ) : ℂ) := by
  rw [funext fun ω => C.Vq_complex ω]
  exact Tame.sum _ fun k _ => Tame.sum _ fun l _ =>
    (Tame.const (sz := sz) (((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ))).mul
      ((C.tameB k l).mul (C.tameB k l).conj)

omit hG in
theorem Tq_complex (ω : Sizes.SeqΩ sz) : ((C.Tq ω : ℝ) : ℂ)
    = ∑ k, ((C.sg k : ℝ) : ℂ) * (C.U ω k * (starRingEnd ℂ) (C.U ω k)
      + C.V ω k * (starRingEnd ℂ) (C.V ω k)) := by
  show ((∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_add, ofReal_normSq, ofReal_normSq]

/-! #### Closing the recursion: `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` -/

/-- `E[T^q]`, the positive-chaos moment that the recursion reduces everything to. -/
noncomputable def momTpow (q : ℕ) : ℝ := ∫ ω, C.Tq ω ^ q ∂(Sizes.seqP sz)

theorem integrable_Tq_pow (q : ℕ) : Integrable (fun ω => C.Tq ω ^ q) (Sizes.seqP sz) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω => ((C.Tq ω ^ q : ℝ) : ℂ)) = fun ω => ((C.Tq ω : ℝ) : ℂ) ^ q := by
    funext ω; rw [Complex.ofReal_pow]
  rw [hfun]
  exact C.tameTq.pow q

omit hG in
theorem momTpow_nonneg (q : ℕ) : 0 ≤ C.momTpow q :=
  MeasureTheory.integral_nonneg fun ω => pow_nonneg (C.Tq_nonneg ω) q

/-- **Hanson–Wright, the moment bound.**  `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` for `p ≥ 1`.

The recursion `2E|Q|^{2(q+1)} ≤ (2q+1)E[T|Q|^{2q}]` is closed by the pointwise Young inequality
`RBM.Green.young_pow` with the *rational* parameter `K = 2q+1`, which keeps every exponent a
natural number and needs no Hölder inequality.

What remains, to reach the paper's `∑_{k,l}σ_k‖B_{kl}‖²σ_l`, is the positive-chaos bound
`E[T^p] ≤ C_p E[Vq^p]`; see the file header. -/
theorem mom_succ_le (q : ℕ) :
    C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1) := by
  set K : ℝ := 2 * (q : ℝ) + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  -- the pointwise Young inequality
  have hpt : ∀ ω : Sizes.SeqΩ sz, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1)) := by
    intro ω
    have hT := C.Tq_nonneg ω
    have hy := young_pow q (mul_nonneg hT hK0.le) (sq_nonneg ‖C.chaos ω‖)
    rw [mul_pow] at hy
    have hg : ∀ j : ℕ, ‖C.chaos ω‖ ^ (2 * j) = (‖C.chaos ω‖ ^ 2) ^ j := fun j => pow_mul _ 2 j
    rw [hg q, hg (q + 1)]
    have hmul : (0 : ℝ) < ((q : ℝ) + 1) * K := by positivity
    refine le_of_mul_le_mul_left ?_ hmul
    have hleft : ((q : ℝ) + 1) * K * (C.Tq ω * (‖C.chaos ω‖ ^ 2) ^ q)
        = ((q : ℝ) + 1) * (C.Tq ω * K * (‖C.chaos ω‖ ^ 2) ^ q) := by ring
    have hrhs : ((q : ℝ) + 1) * K * ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
          + ((q : ℝ) / (((q : ℝ) + 1) * K)) * (‖C.chaos ω‖ ^ 2) ^ (q + 1))
        = C.Tq ω ^ (q + 1) * K ^ (q + 1) + (q : ℝ) * (‖C.chaos ω‖ ^ 2) ^ (q + 1) := by
      field_simp
      ring
    rw [hleft, hrhs]
    exact hy
  -- integrate
  have hi1 := C.integrable_Tq_pow hG (q + 1)
  have hi2 := C.integrable_norm_pow hG (q + 1)
  have hmomT : C.momT q ≤ (K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
      + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1) := by
    calc C.momT q ≤ ∫ ω, ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
            + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1))) ∂(Sizes.seqP sz) :=
          MeasureTheory.integral_mono (C.integrable_Tq_mul hG q)
            ((hi1.const_mul _).add (hi2.const_mul _)) hpt
      _ = _ := by
          rw [MeasureTheory.integral_add (hi1.const_mul _) (hi2.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
  -- close the recursion
  have hrec := C.two_mul_mom_succ_le hG q
  rw [← hKdef] at hrec
  have hm := C.mom_nonneg (q + 1)
  have ht := C.momTpow_nonneg (q + 1)
  have hKmul : K * ((K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1))
      = (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    field_simp
    ring
  have hchain : 2 * C.mom (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    refine hrec.trans ?_
    rw [← hKmul]
    exact mul_le_mul_of_nonneg_left hmomT hK0.le
  have hB : (q : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hq1]; linarith
  have hA : K ^ (q + 1) / ((q : ℝ) + 1) ≤ K ^ (q + 1) := by
    rw [div_le_iff₀ hq1]
    nlinarith [pow_nonneg hK0.le (q + 1), Nat.cast_nonneg (α := ℝ) q]
  have h1 : (q : ℝ) / ((q : ℝ) + 1) * C.mom (q + 1) ≤ C.mom (q + 1) := by
    nlinarith [hm, hB]
  have h3 : K ^ (q + 1) / ((q : ℝ) + 1) * C.momTpow (q + 1)
      ≤ K ^ (q + 1) * C.momTpow (q + 1) := mul_le_mul_of_nonneg_right hA ht
  linarith

end Real

/-! #### The shape of `RBM.Green.ldeQuadLHS` and `RBM.Green.ldeQuadRHS`

The chaos and its control are literally the two sides of the quadratic large deviation estimate
`RBM.Green.LDEQuad` (`RBM3D/Green/EntryCore.lean`), once the row chaos is indexed by
`{k // k ≠ i}` with `h_k = H_{ik}` and `σ_k = t S_{ik}`.  These two lemmas are pure reindexing
(`Finset.sum_subtype`) and contain no analysis; they are the interface through which a
concrete instance meets `RBM.Green.LDEQuad`. -/

section LDEShape

variable {n : Type*} [Fintype n] [DecidableEq n] {i : n}

omit [DecidableEq κ] in
theorem sum_erase_eq {M : Type*} [AddCommMonoid M] (f : n → M) :
    ∑ k ∈ Finset.univ.erase i, f k = ∑ k : {k : n // k ≠ i}, f k.1 :=
  Finset.sum_subtype _ (fun x => by simp [Finset.mem_erase]) _

/-- **The chaos is the left-hand side of (4.7).** -/
theorem norm_chaos_sq_eq_ldeQuadLHS (C : RowChaos sz {k : n // k ≠ i}) (ω : Sizes.SeqΩ sz)
    (H G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hh : ∀ k : {k : n // k ≠ i}, C.h ω k = H i k.1)
    (hhc : ∀ k : {k : n // k ≠ i}, (starRingEnd ℂ) (C.h ω k) = H k.1 i)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1) :
    ‖C.chaos ω‖ ^ 2 = ldeQuadLHS H G S t i := by
  have e1 : ∑ k ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
        H i k * greenMinor G i k l * H l i
      = ∑ k : {k : n // k ≠ i}, ∑ l : {k : n // k ≠ i},
        C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    rw [sum_erase_eq (i := i)
      fun k => ∑ l ∈ Finset.univ.erase i, H i k * greenMinor G i k l * H l i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_erase_eq (i := i) fun l => H i k.1 * greenMinor G i k.1 l * H l i]
    exact Finset.sum_congr rfl fun l _ => by rw [hh k, hB k l, hhc l]
  have e2 : (t : ℂ) * ∑ k ∈ Finset.univ.erase i, (S i k : ℂ) * greenMinor G i k k
      = ∑ k : {k : n // k ≠ i}, ((C.sg k : ℝ) : ℂ) * C.B ω k k := by
    rw [sum_erase_eq (i := i) fun k => (S i k : ℂ) * greenMinor G i k k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB k k, hsg k, Complex.ofReal_mul]
    ring
  show ‖C.chaos ω‖ ^ 2 = ‖_ - _‖ ^ 2
  rw [e1, e2]
  rfl

/-- **`Vq` is the right-hand side of (4.7)**, up to the factor `t²` coming from
`E|H_{ik}|² = t S_{ik}`. -/
theorem Vq_eq_ldeQuadRHS (C : RowChaos sz {k : n // k ≠ i}) (ω : Sizes.SeqΩ sz)
    (G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1)
    (hsg' : ∀ k : {k : n // k ≠ i}, C.sg k = t * S k.1 i) :
    C.Vq ω = t ^ 2 * ldeQuadRHS S G i := by
  show ∑ k : {k : n // k ≠ i}, ∑ l : {k : n // k ≠ i},
      C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l = _
  rw [show ldeQuadRHS S G i = ∑ k ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i from rfl,
    sum_erase_eq (i := i) fun k => ∑ l ∈ Finset.univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_erase_eq (i := i) fun l => S i k.1 * ‖greenMinor G i k.1 l‖ ^ 2 * S l i,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hB k l, hsg k, hsg' l]
  ring

end LDEShape

end RowChaos


/-! ### Compile checks: a three-dimensional row chaos indexed by `{k : Fin 3 // k ≠ 0}`

`SizesInst.sz0` of `RBM3D/Defs/Sizes.lean` at `d = 3`, slice `n = 0` (`L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`).  The index type of the matrix is `n = Fin 3`, the row is `i = 0`, so
`κ = {k : Fin 3 // k ≠ 0}` has two elements; the row of the lattice is `x = 0`, the column
`k = 1` is the point `(1,0,0)` (same block as `x`) and `k = 2` the point `(32,0,0)` (the
neighbouring block `(1,0,0)` of `Z_4^3`); both have a nonzero variance profile.  `eps = 1`,
`r = 1`, `t = 1`; the matrix `G = diag(1, [[2,1],[0,3]])` on `Fin 3` has `G^{(0)}_{kl} = G_{kl}` and
`B ω k l = G^{(0)}_{kl}` (constant, `Ifree = ∅`, `Bbd = 3`); `S a b = S_{xy}` is the variance
profile of the lattice points `pos a`, `pos b` (`pos = ![x, (1,0,0), (32,0,0)]`), symmetrised
through the row so that `S 0 k = S k 0 = σ_k`.  `GaussIBP sz0` (S1-19) stays a hypothesis of the
examples. -/

section Checks

open SizesInst

/-- The lattice points of the three matrix indices: the row `x = 0`, then `(1,0,0)` and
`(32,0,0)`. -/
private noncomputable def chkMPos : Fin 3 → Idx 3 (sz0.L 0) (sz0.W 0) :=
  ![0, ![1, 0, 0], ![32, 0, 0]]

private theorem chkMPos_injective : Function.Injective chkMPos := by
  intro a b h
  revert a b
  decide

/-- The two coordinates of each column index. -/
private noncomputable def chkMCo (k : {k : Fin 3 // k ≠ 0}) (b : Bool) : Sizes.SeqCoord sz0 :=
  ⟨0, (chkMPos 0, chkMPos k.1, b)⟩

/-- The matrix `G = diag(1, [[2,1],[0,3]])`. -/
private def chkMG : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 2, 1; 0, 0, 3]

private theorem chkM_green (k l : Fin 3) : ‖greenMinor chkMG 0 k l‖ ≤ 3 := by
  fin_cases k <;> fin_cases l <;> simp [greenMinor, chkMG] <;> norm_num

private theorem chkMCo_injective :
    Function.Injective fun p : {k : Fin 3 // k ≠ 0} × Bool => chkMCo p.1 p.2 := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  simp only [chkMCo, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨hy, hb⟩ := h
  rw [Subtype.ext (chkMPos_injective hy), hb]

/-- The row chaos on `{k : Fin 3 // k ≠ 0}`. -/
private noncomputable def chkMChaos : RowChaos sz0 {k : Fin 3 // k ≠ 0} where
  co := chkMCo
  co_inj := chkMCo_injective
  gvar_tag _ := rfl
  eps _ := 1
  eps_sq _ := by norm_num
  r := 1
  B _ k l := greenMinor chkMG 0 k.1 l.1
  B_cont _ _ := continuous_const
  Bbd := 3
  B_bdd _ k l := chkM_green k.1 l.1
  Ifree := ∅
  Ifree_free _ _ := Finset.notMem_empty _
  B_free _ _ _ := rfl

/-- The variance profile of the lattice points `pos a`, `pos b`, symmetrised through the row. -/
private noncomputable def chkMS (a b : Fin 3) : ℝ :=
  svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkMPos 0) (chkMPos (if a = 0 then b else a))

private theorem chkM_gvarF_offDiag (i j : Idx 3 (sz0.L 0) (sz0.W 0)) (b : Bool) (hij : i ≠ j) :
    (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (i, j, b) : ℝ) =
      svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j / 2 := by
  change (if i = j then svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j
    else svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j / 2) = _
  simp [hij]

/-- **Check (nondegeneracy).** Same-block column: `S_{xy} = (W^3)⁻¹ (1 + 6 g²)⁻¹` with
`W = 32`, `g = 1/64`. -/
private theorem chkM_svarF_one :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkMPos 0) (chkMPos 1) =
      ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹ := by
  have h1 : (split 3 (sz0.L 0) (sz0.W 0) (chkMPos 0)).1 = 0 := by decide
  have h2 : (split 3 (sz0.L 0) (sz0.W 0) (chkMPos 1)).1 = 0 := by decide
  have h3 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have h4 : sz0.W 0 = 32 := sz0_values.2.1
  simp only [svarF, SBR, Matrix.of_apply, h1, h2, sub_self, sbKernelR, h3, h4, ite_true]
  norm_num

/-- **Check (nondegeneracy).** Neighbouring-block column:
`S_{xy} = (W^3)⁻¹ g² (1 + 6 g²)⁻¹` with `W = 32`, `g = 1/64`. -/
private theorem chkM_svarF_two :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkMPos 0) (chkMPos 2) =
      ((32 : ℝ) ^ 3)⁻¹ * ((1 / 64 : ℝ) ^ 2 * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹) := by
  have h1 : (split 3 (sz0.L 0) (sz0.W 0) (chkMPos 0)).1 = 0 := by decide
  have h2 : (split 3 (sz0.L 0) (sz0.W 0) (chkMPos 2)).1 = ![1, 0, 0] := by decide
  have h3 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have h4 : sz0.W 0 = 32 := sz0_values.2.1
  have h5 : zdistD 3 (sz0.L 0) (-(![1, 0, 0] : Zd 3 (sz0.L 0))) = 1 := by decide
  have h6 : (-(![1, 0, 0] : Zd 3 (sz0.L 0))) ≠ 0 := by decide
  simp only [svarF, SBR, Matrix.of_apply, h1, h2, zero_sub, sbKernelR, h3, h4, h5, h6, ite_false,
    ite_true, zero_add]
  norm_num

/-- `σ_k = 2 r² w_k = S_{x, pos k}` for the private chaos. -/
private theorem chkM_sg (k : {k : Fin 3 // k ≠ 0}) :
    chkMChaos.sg k = chkMS 0 k.1 := by
  have hne : chkMPos 0 ≠ chkMPos k.1 := fun h => k.2 (chkMPos_injective h).symm
  have hw : chkMChaos.w k = svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkMPos 0) (chkMPos k.1) / 2 :=
    chkM_gvarF_offDiag _ _ true hne
  have hr : chkMChaos.r = 1 := rfl
  rw [RowChaos.sg, hw, hr]
  simp only [chkMS, ite_true]
  ring

private theorem chkM_sg' (k : {k : Fin 3 // k ≠ 0}) :
    chkMChaos.sg k = chkMS k.1 0 := by
  rw [chkM_sg]
  simp [chkMS, k.2]

/-- **Check (nondegeneracy).** Both columns have `σ_k > 0`. -/
private theorem chkM_sg_pos (k : {k : Fin 3 // k ≠ 0}) : 0 < chkMChaos.sg k := by
  rw [chkM_sg]
  obtain ⟨k, hk⟩ := k
  simp only [chkMS, ite_true]
  fin_cases k
  · exact absurd rfl hk
  · change 0 < svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkMPos 0) (chkMPos 1)
    rw [chkM_svarF_one]; norm_num
  · change 0 < svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkMPos 0) (chkMPos 2)
    rw [chkM_svarF_two]; norm_num

section Instances

variable (hG : GaussIBP sz0)
include hG

/-- **Instance of `integrable_norm_pow`** (`GaussIBP sz0` a hypothesis, S1-19). -/
example (q : ℕ) : Integrable (fun ω => ‖chkMChaos.chaos ω‖ ^ (2 * q)) (Sizes.seqP sz0) :=
  chkMChaos.integrable_norm_pow hG q

/-- **Instance of `mom_succ_le`** at `p = 1, 2` (`q = 0, 1`): `E|Q|² ≤ 1 · E[T]` and
`E|Q|⁴ ≤ 9 · E[T²]`. -/
example : chkMChaos.mom 1 ≤ 1 * chkMChaos.momTpow 1 ∧ chkMChaos.mom 2 ≤ 9 * chkMChaos.momTpow 2 := by
  have h1 := chkMChaos.mom_succ_le hG 0
  have h2 := chkMChaos.mom_succ_le hG 1
  norm_num at h1 h2
  exact ⟨by simpa using h1, h2⟩

/-- **Instance of `two_mul_mom_succ_le`** at `q = 0` and `q = 1`. -/
example :
    2 * chkMChaos.mom 1 ≤ (2 * ((0 : ℕ) : ℝ) + 1) * chkMChaos.momT 0 ∧
      2 * chkMChaos.mom 2 ≤ (2 * ((1 : ℕ) : ℝ) + 1) * chkMChaos.momT 1 :=
  ⟨chkMChaos.two_mul_mom_succ_le hG 0, chkMChaos.two_mul_mom_succ_le hG 1⟩

/-- **Instance of `integral_chaos_mul`** with `F = 1`, `FA = FB = 0`. -/
example :
    2 * ∫ ω, chkMChaos.chaos ω * (fun _ => (1 : ℂ)) ω ∂(Sizes.seqP sz0)
      = ∑ k, (chkMChaos.w k : ℂ) * ∫ ω, (chkMChaos.dA ω k * (fun _ _ => (0 : ℂ)) k ω
          + chkMChaos.dB ω k * (fun _ _ => (0 : ℂ)) k ω) ∂(Sizes.seqP sz0) :=
  chkMChaos.integral_chaos_mul hG (Tame.const 1) (fun _ => Tame.const 0) (fun _ => Tame.const 0)
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => hasDerivAt_const _ _)

/-- **Instance of `moment_recursion`** at `q = 0`. -/
example :
    2 * ∫ ω, chkMChaos.chaos ω ^ (0 + 1) * (starRingEnd ℂ) (chkMChaos.chaos ω) ^ (0 + 1)
        ∂(Sizes.seqP sz0)
      = 2 * ((0 : ℕ) : ℂ) * ∫ ω, chkMChaos.Rq ω * (chkMChaos.chaos ω ^ (0 - 1)
          * (starRingEnd ℂ) (chkMChaos.chaos ω) ^ (0 + 1)) ∂(Sizes.seqP sz0)
        + (((0 : ℕ) : ℕ) + 1 : ℂ) * ∫ ω, ((chkMChaos.Tq ω : ℝ) : ℂ) * (chkMChaos.chaos ω ^ 0
          * (starRingEnd ℂ) (chkMChaos.chaos ω) ^ 0) ∂(Sizes.seqP sz0) :=
  chkMChaos.moment_recursion hG 0

end Instances

/-- **Instance of `Vq_eq_ldeQuadRHS`** at the private chaos, `G = diag(1, [[2,1],[0,3]])`,
`t = 1` and the lattice variance profile `S = chkMS` (every hypothesis discharged). -/
example (ω : Sizes.SeqΩ sz0) :
    chkMChaos.Vq ω = 1 ^ 2 * ldeQuadRHS chkMS chkMG (0 : Fin 3) :=
  RowChaos.Vq_eq_ldeQuadRHS (i := 0) chkMChaos ω chkMG chkMS 1
    (fun _ _ => rfl) (fun k => by rw [chkM_sg, one_mul]) (fun k => by rw [chkM_sg', one_mul])

/-- The row matrix `H_{0k} = h_k(ω)`, `H_{k0} = \bar h_k(ω)`, zero elsewhere. -/
private noncomputable def chkMH (ω : Sizes.SeqΩ sz0) : Matrix (Fin 3) (Fin 3) ℂ := fun a b =>
  if ha : a = 0 then (if hb : b = 0 then 0 else chkMChaos.h ω ⟨b, hb⟩)
  else if b = 0 then (starRingEnd ℂ) (chkMChaos.h ω ⟨a, ha⟩) else 0

/-- **Instance of `norm_chaos_sq_eq_ldeQuadLHS`** at the private chaos, the row matrix
`chkMH ω`, `G = diag(1, [[2,1],[0,3]])` and `t = 1` (every hypothesis discharged). -/
example (ω : Sizes.SeqΩ sz0) :
    ‖chkMChaos.chaos ω‖ ^ 2 = ldeQuadLHS (chkMH ω) chkMG chkMS 1 0 :=
  RowChaos.norm_chaos_sq_eq_ldeQuadLHS (i := 0) chkMChaos ω (chkMH ω) chkMG chkMS 1
    (fun k => by simp [chkMH, k.2])
    (fun k => by simp [chkMH, k.2])
    (fun _ _ => rfl) (fun k => by rw [chkM_sg, one_mul])

end Checks

end RBM.Green
