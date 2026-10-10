/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.HypB
import RBM3D.Universality.GUEPhase.BoundsA
import RBM3D.Universality.GUEPhase.DuhamelC
import RBM3D.Universality.GUEPhase.EntryGrid
import RBM3D.Universality.GUEPhase.BootstrapAt
import RBM3D.Universality.GUEPhase.ProcK

/-!
# The output of the §7.2 random layer on the grid: `gueGrid_pathBounds`, `d ≥ 3` (T2361, UN-50b)

Port of RBM2D `Universality/GUEPhase/PathBounds.lean` (532 lines, `9e0f275`).  Under the
hypotheses of `gueGrid_pathBounds`, the GUE-phase grid path `gueH` satisfies `GUEPathBounds`
(`Grid.lean`): (7.28) at every grid time `k ≤ K n` for `1 ≤ m ≤ n₀` against the primitive family
`Kt`, and `‖G̃ − m‖_max ≺ (N η_u)^{-1/2}`, `N = sz.size n = (W L)^d`, on the size scale.

## Contents

* `gueBds_h745E`, `gueBds_h746` (public): the inputs `h745`, `h746` of the size-scale bootstraps
  `eq727GEAt` (at `2 n₀`) and `eq728GAt` (`BootstrapAt.lean`) for the stopped, interpolated
  processes `gueLproc`, `gueDproc` (`Proc.lean`) with `δ = gueDelta sz τU`, `K = gueGridK sz n₀`;
* `gueGrid_pathBounds` (public): the two bootstraps, the entry bound at `δ = gueDelta sz τU`,
  `c₀ = τU/4`, the step-`0` local law, the truncation `gue_highProb_incr_le`, and the pathwise
  unfreezing `Bounds_path` on their intersection, concluded by
  `BoundsACheck.pathBounds_of_forall_highProbAt`;
* `PathBounds_init_loops`, `PathBounds_init_local` (private): the step-`0` laws;
* `PathBoundsInst`: compiled nonempty instances.

## Port map (`d = 2` to `d ≥ 3`) and statement differences (paper-delta candidates `T2361a-c`)

`d : Sizes` becomes `sz : Sizes d`; `Z2 L` becomes `Zd d L`; `spectralZ/spectralM` become `zt/mE`;
`gloop … (blockMat M)` becomes `loopL d L W (blockMat d L W M)`; `KLoop.Kcal` becomes `sz.STKloop`
(on `loopOf`, as the merged `Hyp_Kt_detDom`); `N = (W L)^2` becomes `N = (W L)^d = sz.size n`.

* `T2361a`.  The loop estimate `RBM.Ind.MLConcl d E t1` has no twin; its two consumed conjuncts
  `InitLK`, `InitLocal` are `hLK : sz.STLK E t1` and `hLoc : sz.STLocalEntry E t1` (conclusions
  of `UNMLOut`, `Universality/Pins.lean:432`, at the flow `(E, t₁)`).  The scale `scaleM = N η_{t₁}`
  (with `ℓ_{t₁} = L`, `d = 2`) becomes the inequality `W^{-d} B_{t₁,0} ≤ 2 (N η_{t₁})⁻¹` under
  `hell : L^d (1 - t₁) ≤ ilambda²` (`PathBounds_Bctl_le`), the constant `2` absorbed in `N^τ`.
  The union over `(σ, a)` and `(x, y)` is inside `Prec` (`STLK`, `STLocalEntry`), so the
  counting lemmas of the source are not needed.
* `T2361b`.  `gueGrid_pathBounds` carries the extra hypothesis `hell1 : L^d (1 - t₁) ≤ 1`: the
  merged `Bounds_path` has `hellN : L^d (1 - t₁) ≤ 1` while `(eq:WO)` gives only
  `ilambda ≤ 𝔡⁻¹`, so `hell : L^d (1 - t₁) ≤ ilambda²` does not imply it.  `gueBds_h745E`,
  `gueBds_h746` do not need it.
* `T2361c`.  `h𝔠 : 0 < 𝔠` and `Admissible 𝔠 d` of the source become `hd : 3 ≤ d` and
  `hadm : sz.Admissible 𝔠 𝔡` (the merged `gueGrid_entry_bound`); in `gueBds_h746` the source's
  `hsz` is replaced by `hadm` (`ilambda ≤ 𝔡⁻¹` gives the constant `A = 1 + 2 ilambda²` of the
  `hbig` threshold of `HypB_fixed`, merged departure T2354a).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### The step-0 laws (private) -/

section PathBoundsInit

/-- The step-`0` marginal of the grid measure is the band law `seqP sz`. -/
private theorem PathBounds_map_eval0 :
    (Pgue sz).map (fun ω : PathΩ sz => ω 0) = Sizes.seqP sz := by
  unfold Pgue
  rw [Measure.infinitePi_map_eval]
  rfl

/-- A bad set at step `0` is bounded by its image under the coordinate marginal, with no
measurability (`Measure.le_map_apply`). -/
private theorem PathBounds_step0_le (B : Set (Sizes.SeqΩ sz)) :
    Pgue sz ((fun ω : PathΩ sz => ω 0) ⁻¹' B) ≤ Sizes.seqP sz B := by
  have h := Measure.le_map_apply (μ := Pgue sz) (measurable_pi_apply (0 : ℕ)).aemeasurable B
  rwa [PathBounds_map_eval0] at h

/-- `H_0 = H^{band}_{t₁}(ω 0)` (the pointwise identity inside `map_gueH_zero`). -/
private theorem PathBounds_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ω : PathΩ sz) :
    gueH sz t1 t0 K n 0 ω = Sizes.seqHflow sz n (t1 n) (ω 0) := by
  unfold gueH
  simp [Sizes.seqHflow_eq_smul]

/-- The conversion `W^{-d} B_{t,0} ≤ 2 (N η_t)⁻¹` under the zero-mode condition
`L^d (1 - t) ≤ ilambda²` (`hell`): `(ilambda² + x)⁻¹ ≤ (L^d x)⁻¹`, so
`Bctl ≤ 2 W^{-d} (L^d x)⁻¹ = 2 (N x)⁻¹ ≤ 2 (N x Im m)⁻¹` (`Im m ≤ 1`).  It replaces
`scaleM = N η` of the source (`d = 2`); a private re-derivation of the private `Hyp_Bctl_le`
(`HypA.lean:494`). -/
private theorem PathBounds_Bctl_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hell : ((sz.L n : ℕ) : ℝ) ^ d * (1 - t) ≤ sz.lam n ^ 2) :
    sz.Bctl n t ≤ 2 * (((sz.size n : ℕ) : ℝ) * etaT E t)⁻¹ := by
  have hx : 0 < 1 - t := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by rw [hsize]; positivity
  have hηpos : 0 < etaT E t := etaT_pos hE ht
  have hmim : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  have hηle : etaT E t ≤ 1 - t := by
    unfold etaT
    calc (1 - t) * (mE E).im ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left hmim hx.le
      _ = 1 - t := mul_one _
  have h1 : (sz.lam n ^ 2 + (1 - t))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ :=
    inv_anti₀ (mul_pos hLd hx) (by nlinarith [sq_nonneg (sz.lam n)])
  have hB : Bparam d (sz.L n) (sz.lam n) t 0 ≤ 2 * (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ := by
    unfold Bparam
    rw [abs_of_pos hx]
    have e : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
    rw [e, mul_one]
    linarith
  have hNx : (((sz.size n : ℕ) : ℝ) * (1 - t))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * etaT E t)⁻¹ :=
    inv_anti₀ (mul_pos hN hηpos) (mul_le_mul_of_nonneg_left hηle hN.le)
  have hid : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹)
      = 2 * (((sz.size n : ℕ) : ℝ) * (1 - t))⁻¹ := by
    rw [hsize]
    field_simp
  unfold Sizes.Bctl
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) t 0
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹) :=
        mul_le_mul_of_nonneg_left hB (inv_nonneg.2 hWd.le)
    _ = 2 * (((sz.size n : ℕ) : ℝ) * (1 - t))⁻¹ := hid
    _ ≤ 2 * (((sz.size n : ℕ) : ℝ) * etaT E t)⁻¹ := by linarith

/-- `Bctl ≥ 0`. -/
private theorem PathBounds_Bctl_nonneg (n : ℕ) (t : ℝ) : 0 ≤ sz.Bctl n t := by
  unfold Sizes.Bctl Bparam
  positivity

/-- `STWB_{t,K} ≤ Bctl_t` (`((K + 1)^{d-2})⁻¹ ≤ 1`, no hypothesis on `d`). -/
private theorem PathBounds_STWB_le (n : ℕ) (t : ℝ) (K : ℕ) : sz.STWB n t K ≤ sz.Bctl n t := by
  unfold Sizes.STWB Sizes.Bctl Bparam
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
  have h0 : 0 ≤ (sz.lam n ^ 2 + |1 - t|)⁻¹ := by positivity
  have e : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
  rw [e, mul_one]
  have := mul_le_mul_of_nonneg_left h1 h0
  rw [mul_one] at this
  linarith

/-- The loop of the band flow is the list-based loop on `blockMat`. -/
private theorem PathBounds_Lloop_eq (n : ℕ) (E t : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) (ω : Sizes.SeqΩ sz) :
    sz.Lloop n E t σ a ω =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n t ω))
        (zt E t) (loopOf σ a) :=
  loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a

/-- `Gres H z true = green H z` (a private twin of `HypB_Gres_true`). -/
private theorem PathBounds_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, Matrix.nonsing_inv_eq_ringInverse, ite_true]

/-- `STGM` is the entry `(G − m)_{xy}` of the band flow at `t`. -/
private theorem PathBounds_STGM_eq (n : ℕ) (E t : ℝ) (ω : Sizes.SeqΩ sz)
    (x y : Idx d (sz.L n) (sz.W n)) :
    sz.STGM n E t ω x y =
      (green (Sizes.seqHflow sz n t ω) (zt E t) -
        mE E • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) x y := by
  unfold Sizes.STGM Sizes.Gt
  rw [PathBounds_Gres_true]
  by_cases h : x = y
  · subst h; simp [Matrix.sub_apply, Matrix.smul_apply]
  · simp [h, Matrix.sub_apply, Matrix.smul_apply]

/-- **The loops at step `0`**: the step-`0` input `‖L_0 − K̃_{t₁}‖ ≺ (N η_{t₁})^{-k}` on `Pgue`,
from `STLK` at `t₁` (a conclusion of `UNMLOut`) transferred through the coordinate marginal, with
`K̃_{t₁} = STKloop` (`hKinit`) and `W^{-d} B_{t₁,0} ≤ 2 (N η_{t₁})⁻¹` (`hell`).  The union over
`(σ, a)` is inside `STLK`. -/
private theorem PathBounds_init_loops {E t1 : ℕ → ℝ} (t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (hsz : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hLK : sz.STLK E t1) (k : ℕ) (hk : 1 ≤ k) :
    StochDomAt (Pgue sz) sz.size
      (fun n (x : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
            (zt (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
          Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖)
      (fun n _ _ => (gueScale sz E n (t1 n))⁻¹ ^ k) := by
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hLK k hk (τ / 2) hτ2 D hD, hell,
    hsz.eventually (eventually_le_rpow ((2 : ℝ) ^ k) hτ2),
    hsz.eventually (eventually_ge_atTop 1)] with n hn hellN h2k hN1
  refine le_trans (measure_mono ?_) (le_trans (PathBounds_step0_le sz _) hn)
  intro ω hω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_preimage] at hω ⊢
  obtain ⟨x, hx⟩ := hω
  refine ⟨x, ?_⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hlt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hB := PathBounds_Bctl_le sz n (hE n) hlt hellN
  have hB0 := PathBounds_Bctl_nonneg sz n (t1 n)
  have hΛ : (gueScale sz E n (t1 n))⁻¹ = (((sz.size n : ℕ) : ℝ) * etaT (E n) (t1 n))⁻¹ := rfl
  have hpow : sz.Bctl n (t1 n) ^ k ≤ (2 : ℝ) ^ k * (gueScale sz E n (t1 n))⁻¹ ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB0 (by rw [hΛ]; exact hB) k
  have hΛ0 : 0 ≤ (gueScale sz E n (t1 n))⁻¹ ^ k := by
    have : 0 < gueScale sz E n (t1 n) := mul_pos hN0 (etaT_pos (hE n) hlt)
    positivity
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hc0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  have hkey : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (t1 n) ^ k ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n (t1 n))⁻¹ ^ k := by
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (t1 n) ^ k
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((2 : ℝ) ^ k * (gueScale sz E n (t1 n))⁻¹ ^ k) :=
          mul_le_mul_of_nonneg_left hpow hc0
      _ = ((2 : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) * (gueScale sz E n (t1 n))⁻¹ ^ k := by
          ring
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) *
            (gueScale sz E n (t1 n))⁻¹ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ hΛ0
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2k hc0
      _ = ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n (t1 n))⁻¹ ^ k := by rw [hrpow]
  have hgt : gridTime t1 t0 K n 0 = t1 n := by simp [gridTime]
  rw [PathBounds_gueH_zero, hgt, hKinit, ← PathBounds_Lloop_eq] at hx
  exact lt_of_le_of_lt hkey hx

/-- **The local law at step `0`**: `STLocalEntry` at `t₁` (a conclusion of `UNMLOut`) transferred
to `Pgue` through the coordinate marginal: `‖(G − m)_{xy}‖² ≺ STWB(K) ≤ Bctl ≤ 2 (N η_{t₁})⁻¹`
(`hell`), so `‖(G − m)_{xy}‖ ≺ (N η_{t₁})^{-1/2}` with the factor `2` absorbed in `N^τ`; the union
over `(x, y)` is inside `STLocalEntry`. -/
private theorem PathBounds_init_local {E t1 : ℕ → ℝ} (t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (hsz : Tendsto sz.size atTop atTop) (hE : ∀ n, |E n| < 2)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hLoc : sz.STLocalEntry E t1) :
    StochDomAt (Pgue sz) sz.size
      (fun n (ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ω =>
        ‖(green (gueH sz t1 t0 K n 0 ω) (zt (E n) (t1 n)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
            ij.1 ij.2‖)
      (fun n _ _ => (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) := by
  intro τ hτ D hD
  filter_upwards [hLoc τ hτ D hD, hell, hsz.eventually (eventually_le_rpow (2 : ℝ) hτ),
    hsz.eventually (eventually_ge_atTop 1)] with n hn hellN h2 hN1
  refine le_trans (measure_mono ?_) (le_trans (PathBounds_step0_le sz _) hn)
  intro ω hω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_preimage] at hω ⊢
  obtain ⟨ij, hij⟩ := hω
  refine ⟨ij, ?_⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hlt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hB := PathBounds_Bctl_le sz n (hE n) hlt hellN
  have hW := PathBounds_STWB_le sz n (t1 n) (zdistInf d (sz.L n) (sz.STblk n ij.1 - sz.STblk n ij.2))
  have hsc : 0 < gueScale sz E n (t1 n) := mul_pos hN0 (etaT_pos (hE n) hlt)
  have hΛ : (gueScale sz E n (t1 n))⁻¹ = (((sz.size n : ℕ) : ℝ) * etaT (E n) (t1 n))⁻¹ := rfl
  have hΛ0 : 0 ≤ (gueScale sz E n (t1 n))⁻¹ := inv_nonneg.2 hsc.le
  have hcp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg hN0.le _
  have hsqrt : ((gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 = (gueScale sz E n (t1 n))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0]; norm_num
  have hrhs0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2) :=
    mul_nonneg hcp (Real.rpow_nonneg hΛ0 _)
  have hsq : (((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 <
      ‖(green (Sizes.seqHflow sz n (t1 n) (ω 0)) (zt (E n) (t1 n)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
          ij.1 ij.2‖ ^ 2 := by
    rw [PathBounds_gueH_zero] at hij
    exact pow_lt_pow_left₀ hij hrhs0 (by norm_num)
  rw [PathBounds_STGM_eq]
  refine lt_of_le_of_lt ?_ hsq
  rw [mul_pow, hsqrt, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have h2' : ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) ^ τ) =
      ((sz.size n : ℕ) : ℝ) ^ ((τ * (2 : ℕ)) : ℝ) := by
    rw [← Real.rpow_add hN0]; push_cast; ring_nf
  calc ((sz.size n : ℕ) : ℝ) ^ τ * sz.STWB n (t1 n) (zdistInf d (sz.L n) (sz.STblk n ij.1 - sz.STblk n ij.2))
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (2 * (gueScale sz E n (t1 n))⁻¹) :=
        mul_le_mul_of_nonneg_left (hW.trans (by rw [hΛ]; exact hB)) hcp
    _ = (((sz.size n : ℕ) : ℝ) ^ τ * 2) * (gueScale sz E n (t1 n))⁻¹ := by ring
    _ ≤ (((sz.size n : ℕ) : ℝ) ^ τ * ((sz.size n : ℕ) : ℝ) ^ τ) * (gueScale sz E n (t1 n))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hcp) hΛ0
    _ = _ := by rw [h2']

end PathBoundsInit

/-! ### (7.45)G and (7.46)G for the stopped, interpolated processes -/

section PathBoundsHyp

open RBM.Ind.PerTimeCalc

/-- `0 ≤ ilambda ≤ 𝔡⁻¹` eventually (from `(eq:WO)`, `hadm.2.2.2.2`). -/
private theorem PathBounds_lam_bd {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) :
    ∀ᶠ n in atTop, 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hadm.2.2.2.2] with n hn
  exact ⟨(Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hn.1, hn.2⟩

/-- The `hbig` threshold of `HypB_fixed` (`2 + 2^{2n₀} + (3 + 4A)(2n₀)² ≤ N^{τ/2}`, `A = 1 + 2 lam²`)
holds eventually: `lam ≤ 𝔡⁻¹` bounds `A` (the source has the constant `7`, `A = 3`). -/
private theorem PathBounds_hbig {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hsz : Tendsto sz.size atTop atTop) (n0 : ℕ) {τ2 : ℝ} (hτ2 : 0 < τ2) :
    ∀ᶠ n in atTop, 2 + 2 ^ (2 * n0) + (3 + 4 * (1 + 2 * sz.lam n ^ 2)) *
      ((2 * n0 : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ2 := by
  filter_upwards [hsz.eventually (eventually_le_rpow
    (2 + 2 ^ (2 * n0) + (3 + 4 * (1 + 2 * (𝔡⁻¹) ^ 2)) * ((2 * n0 : ℕ) : ℝ) ^ 2) hτ2),
    PathBounds_lam_bd sz hadm] with n h1 h2
  refine le_trans ?_ h1
  have : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ h2.1 h2.2 2
  gcongr

/-- **(7.45)G at even lengths `2 ≤ m ≤ 2n₀`** for the stopped, interpolated processes: the `h745`
of `eq727GEAt` (with `n₀' = 2 n₀`), over the whole interval `[t₁, t₀]`, on `Pgue sz` and the size
scale.  The step-`0` input is `STLK` at `t₁` (the loop conclusion of `UNMLOut`, in place of
`InitLK` of `MLConcl`); `Admissible 𝔠 𝔡` gives `sz.size → ∞`, `ilambda ≤ 𝔡⁻¹` and the hypothesis
of `gueGrid_entry_bound`; constants and counts are on `N = sz.size n` (`HypB_*`). -/
theorem gueBds_h745E (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (_hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hLK : sz.STLK E t1) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : TimeIcc t1 t0 n × {m : ℕ // m ∈ Set.Icc 2 (2 * n0) ∧ Even m}) ω =>
        gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n p.2.1 p.1 ω)
      (fun n p ω => rhs745G ((sz.size n : ℕ) : ℝ) (etaT (E n)) (t1 n)
        (fun m t => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n m t ω)
        (fun m t => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω) p.2.1 p.1) := by
  classical
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hadm.2.2.1
  have hEb : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hI := fun k (hk : 1 ≤ k) =>
    PathBounds_init_loops sz t0 (gueGridK sz n0) hsz hEb ht10 ht0 hell Kt hKinit hLK k hk
  have hKtd := Hyp_Kt_detDom sz hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hell hKb Kt hKinit hK
  have hD4 := gueGrid_entry_bound sz hd hadm hκ n0 hE ht1 ht10 ht0 (δ := gueDelta sz τU)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := τU / 4) (by positivity)
    (Eventually.of_forall fun n => le_of_eq rfl)
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 _ => perTimeCalc_highProbAt_of_stochDomAt (hI k h1) hτ2)
  have hG2 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 h2 => perTimeCalc_highProbAt_of_stochDomAt
      (gueGrid_loop_duhamel sz hκ hτU n0 hsz hE ht1 ht10 ht0 hscale k h1 h2) hτ2)
  have hG3 := perTimeCalc_highProbAt_of_stochDomAt hD4 hτ2
  filter_upwards [(perTimeCalc_highProbAt_inter hsz (perTimeCalc_highProbAt_inter hsz hG1 hG2) hG3)
      D hD, hKtd (τ / 2) hτ2, hKtd (τU / 2) (by positivity), hell, hscale, h730,
    HypB_ev_grid sz hsz n0, HypB_ev_delta sz hκ hτU hsz hE,
    PathBounds_hbig sz hadm hsz n0 hτ2,
    hsz.eventually (eventually_ge_atTop 1)]
    with n hGn hKtN hKt1N hellN hscaleN h730N hgridN hδN hbigN hN1
  refine (measure_mono ?_).trans hGn
  rintro ω ⟨⟨⟨t, ht⟩, ⟨m, ⟨hm2, hmn⟩, heven⟩⟩, hp⟩ hω
  obtain ⟨⟨hω1, hω2⟩, hω3⟩ := hω
  obtain ⟨l, hl⟩ := heven
  have hnl : m = 2 * l := by omega
  subst hnl
  have hl1 : 1 ≤ l := by omega
  refine absurd hp (not_lt.2 ?_)
  have hω1' := hω1 (2 * l) (by omega) hmn
  have hω2' := hω2 (2 * l) (by omega) hmn
  simp only [Set.mem_ofPred_eq] at hω1' hω2' hω3
  have hN1R : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hc1 : (1 : ℝ) ≤ N ^ (τ / 2) := Real.one_le_rpow hN1R hτ2.le
  have hS0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA1 : (1 : ℝ) ≤ 1 + 2 * sz.lam n ^ 2 := by nlinarith [sq_nonneg (sz.lam n)]
  exact HypB_fixed sz hτ n0 τU Kt hK n (2 * l) ω
    (fun u => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n 2 u ω *
      gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (2 * l) u ω)
    (fun u => Real.sqrt (N⁻¹ * (etaT (E n) u)⁻¹ ^ 2) *
      gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (2 * l) u ω)
    (Ce := ((2 * l : ℕ) : ℝ) * (1 + 2 * sz.lam n ^ 2) * N ^ (τ / 2) * N)
    (hEb n) (ht1 n) (ht10 n) (ht0 n) (by omega) hmn
    (HypB_step_le sz n0 n (hEb n) (ht10 n) (ht0 n) h730N hτU) hgridN.1 hgridN.2
    (HypB_Kt_le_one sz hτU n0 n Kt (hEb n) (ht0 n)
      (fun p => hKt1N p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) hscaleN)
    hKtN hbigN (by positivity)
    (by
      have hl' : (1 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * l)
      have hc0 : (0 : ℝ) ≤ N ^ (τ / 2) := by linarith
      have h1 : ((2 * l : ℕ) : ℝ) ≤ 4 * ((2 * l : ℕ) : ℝ) ^ 2 := by nlinarith
      have h2 : 0 ≤ (1 + 2 * sz.lam n ^ 2) * N ^ (τ / 2) * N :=
        mul_nonneg (mul_nonneg (by linarith) hc0) hS0
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      nlinarith)
    (fun u _ => mul_nonneg (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _)
      (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    ((gueLproc_continuousOn _ _ _ _ _ _ _ _ _).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    ((HypB_sqrt_cont sz n (hEb n) (ht0 n)).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun j hj => by
      rw [HypB_Lproc_grid sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (2 * l) j ω (ht10 n) hj]
      exact HypB_q_745 ((gueH_isHermitian sz t1 t0 (gueGridK sz n0) n j ω).submatrix _) _
        (by positivity) hl1)
    (fun j hj x => by
      rw [HypB_Lproc_grid sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n 2 j ω (ht10 n) hj,
        HypB_Lproc_grid sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (2 * l) j ω (ht10 n) hj]
      exact HypB_eG_745 sz (gueGridK sz n0) n j ω hc1 hl1
        (fun q => HypB_entry_le sz (by omega) hκ n0 hE ht10 ht0 n hellN hδN ω (by linarith)
          (fun k i j' => hω3 (k, (i, j'))) hj q) x)
    ht

/-- **(7.46)G at lengths `1 ≤ m ≤ n₀`** for the stopped, interpolated processes: the `h746` of
`eq728GAt`, over the whole interval `[t₁, t₀]`.  The step-`0` input is `STLK` at `t₁`; the entry
bound is not needed; `Admissible 𝔠 𝔡` gives `sz.size → ∞` and `ilambda ≤ 𝔡⁻¹` (the constant of
`hbig`). -/
theorem gueBds_h746 {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hLK : sz.STLK E t1) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 1 n0) ω =>
        gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n p.2 p.1 ω)
      (fun n p ω => rhs746G ((sz.size n : ℕ) : ℝ) (etaT (E n)) (t1 n)
        (fun m t => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n m t ω)
        (fun m t => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω) p.2 p.1) := by
  classical
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hadm.2.2.1
  have hEb : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hI := fun k (hk : 1 ≤ k) =>
    PathBounds_init_loops sz t0 (gueGridK sz n0) hsz hEb ht10 ht0 hell Kt hKinit hLK k hk
  have hKtd := Hyp_Kt_detDom sz hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hell hKb Kt hKinit hK
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 _ => perTimeCalc_highProbAt_of_stochDomAt (hI k h1) hτ2)
  have hG2 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 h2 => perTimeCalc_highProbAt_of_stochDomAt
      (gueGrid_loop_duhamel sz hκ hτU n0 hsz hE ht1 ht10 ht0 hscale k h1 h2) hτ2)
  filter_upwards [(perTimeCalc_highProbAt_inter hsz hG1 hG2) D hD, hKtd (τ / 2) hτ2,
    hKtd (τU / 2) (by positivity), hscale, h730, HypB_ev_grid sz hsz n0,
    PathBounds_hbig sz hadm hsz n0 hτ2,
    hsz.eventually (eventually_ge_atTop 1)]
    with n hGn hKtN hKt1N hscaleN h730N hgridN hbigN hN1
  refine (measure_mono ?_).trans hGn
  rintro ω ⟨⟨⟨t, ht⟩, ⟨m, hmem⟩⟩, hp⟩ hω
  have hm1 : 1 ≤ m := hmem.1
  have hmn : m ≤ n0 := hmem.2
  obtain ⟨hω1, hω2⟩ := hω
  refine absurd hp (not_lt.2 ?_)
  have hm' : m ≤ 2 * n0 := by omega
  have hω1' := hω1 m hm1 hm'
  have hω2' := hω2 m hm1 hm'
  have hN1R : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hc1 : (1 : ℝ) ≤ N ^ (τ / 2) := Real.one_le_rpow hN1R hτ2.le
  have hS0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA1 : (1 : ℝ) ≤ 1 + 2 * sz.lam n ^ 2 := by nlinarith [sq_nonneg (sz.lam n)]
  exact HypB_fixed sz hτ n0 τU Kt hK n m ω
    (fun u => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n 1 u ω *
      gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (m + 1) u ω)
    (fun u => Real.sqrt (N⁻¹ * (etaT (E n) u)⁻¹ ^ 2) *
      Real.sqrt (gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (2 * m) u ω))
    (Ce := (m : ℝ) * N)
    (hEb n) (ht1 n) (ht10 n) (ht0 n) hm1 hm'
    (HypB_step_le sz n0 n (hEb n) (ht10 n) (ht0 n) h730N hτU) hgridN.1 hgridN.2
    (HypB_Kt_le_one sz hτU n0 n Kt (hEb n) (ht0 n)
      (fun p => hKt1N p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) hscaleN)
    hKtN hbigN (by positivity)
    (by
      have hn1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hc0 : (0 : ℝ) ≤ N ^ (τ / 2) := by linarith
      have h1 : (m : ℝ) ≤ 4 * (1 + 2 * sz.lam n ^ 2) * (m : ℝ) ^ 2 * N ^ (τ / 2) := by
        have hAc : (1 : ℝ) ≤ (1 + 2 * sz.lam n ^ 2) * N ^ (τ / 2) := by nlinarith
        nlinarith
      calc (m : ℝ) * N ≤ (4 * (1 + 2 * sz.lam n ^ 2) * (m : ℝ) ^ 2 * N ^ (τ / 2)) * N :=
            mul_le_mul_of_nonneg_right h1 hS0
        _ = _ := by ring)
    (fun u _ => mul_nonneg (gueDproc_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (gueLproc_nonneg _ _ _ _ _ _ _ _ _ _))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    ((gueDproc_continuousOn _ _ _ _ _ _ _ _ _ _).mul (gueLproc_continuousOn _ _ _ _ _ _ _ _ _))
    ((HypB_sqrt_cont sz n (hEb n) (ht0 n)).mul
      (Real.continuous_sqrt.comp_continuousOn (gueLproc_continuousOn _ _ _ _ _ _ _ _ _)))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun j hj => by
      rw [HypB_Lproc_grid sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (2 * m) j ω (ht10 n) hj,
        ← Real.sqrt_mul (by positivity)])
    (fun j hj x => by
      rw [HypB_Dproc_grid sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n 1 j ω (ht10 n) hj,
        HypB_Lproc_grid sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n (m + 1) j ω (ht10 n) hj]
      exact HypB_eG_746 sz (gueGridK sz n0) n0 (by omega) Kt hKinit hK n j m
        (Hyp_time_mem (ht10 n) (gueGridK_ne_zero sz n0 n)
          ((le_of_lt hj).trans (firstHit_le _ _ _ ω))) ω x)
    ht

end PathBoundsHyp

/-! ### The main statement -/

section PathBoundsMain

open RBM.Ind.PerTimeCalc

/-- **The output of the §7.2 random layer on the grid**: under the hypotheses of the theorem,
the GUE-phase grid path `gueH` satisfies `GUEPathBounds`: (7.28) at every grid time `k ≤ K n` for
`1 ≤ m ≤ n₀` against the primitive family `Kt`, and `‖G̃ − m‖_max ≺ (N η_u)^{-1/2}`.

Proof: the two bootstraps `eq727GEAt` (at `2 n₀`, with the processes of `Proc.lean`,
`gueBds_h745E`) and `eq728GAt` (`gueBds_h746`); the other random inputs (the entry bound
`gueGrid_entry_bound` at `δ = gueDelta sz τU`, `c₀ = τU/4`, the step-`0` local law, the increment
truncation `gue_highProb_incr_le`); the pathwise unfreezing `Bounds_path` on their intersection
(`τ₁ = min(τ, τU)/16`); `BoundsACheck.pathBounds_of_forall_highProbAt`.

Here `hLK : sz.STLK E t1` and `hLoc : sz.STLocalEntry E t1` (conclusions of `UNMLOut`) replace the
loop estimate `MLConcl d E t1` of the source: `STLK` gives the step-`0` loops, `STLocalEntry` the
step-`0` local law; `Admissible 𝔠 𝔡` gives `sz.size → ∞`, `ilambda ≤ 𝔡⁻¹` and the hypothesis of the
entry bound; the size scale `N = sz.size n = (W L)^d` is used throughout;
`hsmallN : N^{2τ₁ − τU/2} ≤ 1/32`, `h4N : 2 ≤ N^{τ − τ₁}` as in `Bounds_path`.  `hell1` (`T2361b`)
is the hypothesis `hellN` of `Bounds_path`. -/
theorem gueGrid_pathBounds (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hell1 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hLK : sz.STLK E t1) (hLoc : sz.STLocalEntry E t1) :
    GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt := by
  classical
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hadm.2.2.1
  /- Deterministic facts on `η = etaT (E n)` (the side conditions of the bootstraps). -/
  have hEb : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hmim : ∀ n, 0 < (mE (E n)).im := fun n => mE_im_pos (hEb n)
  have hη : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), 0 < etaT (E n) t := fun n t ht =>
    mul_pos (by linarith [ht.2, ht0 n]) (hmim n)
  have hanti : ∀ n, ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ t ∈ Set.Icc (t1 n) (t0 n), u ≤ t →
      etaT (E n) t ≤ etaT (E n) u := fun n u _ t _ hut => by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (hmim n).le
  have hηc : ∀ n, ContinuousOn (etaT (E n)) (Set.Icc (t1 n) (t0 n)) := fun n => by
    unfold etaT
    exact ((continuous_const.sub continuous_id).mul continuous_const).continuousOn
  have hNpos : ∀ n, (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := fun n => by
    have h1 : 0 < sz.size n := by
      unfold Sizes.size
      have hW := sz.W_pos n
      have hL := sz.three_le_L n
      positivity
    exact_mod_cast h1
  have ht0mem : ∀ n, t0 n ∈ Set.Icc (t1 n) (t0 n) := fun n => ⟨ht10 n, le_rfl⟩
  have h730' : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n),
      t - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) t := by
    filter_upwards [h730] with n hN t ht
    have h1 := hanti n t ht (t0 n) (ht0mem n) ht.2
    calc t - t1 n ≤ t0 n - t1 n := by linarith [ht.2]
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n) := hN
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) t :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hscale' : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (((sz.size n : ℕ) : ℝ) * etaT (E n) t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := by
    filter_upwards [hscale] with n hN t ht
    refine le_trans ?_ hN
    unfold gueScale
    have h0 := hη n (t0 n) (ht0mem n)
    have h1 := hanti n t ht (t0 n) (ht0mem n) ht.2
    exact inv_anti₀ (mul_pos (hNpos n) h0) (mul_le_mul_of_nonneg_left h1 (hNpos n).le)
  /- The bootstraps: `eq727GEAt` at `2 n₀`, then `eq728GAt`. -/
  have h727 := eq727GEAt (Pgue sz) sz.size hsz (n0 := 2 * n0) (even_two_mul n0)
    (fun n => ((sz.size n : ℕ) : ℝ)) (fun n => etaT (E n)) t1 t0
    (fun n m t ω => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n m t ω)
    (fun n m t ω => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω)
    (fun n m t => gueKproc sz t1 t0 (gueGridK sz n0) Kt n m t)
    hNpos ht10 hη hanti hηc hτU h730' hscale'
    (fun n m t ω => gueLproc_nonneg sz E t1 t0 _ _ n m t ω)
    (fun n m t ω => gueDproc_nonneg sz E t1 t0 _ _ Kt n m t ω)
    (fun n ω m _ t _ => gueLproc_le sz E t1 t0 _ _ Kt n m t ω)
    (fun n ω m _ t _ => gueDproc_le sz E t1 t0 _ _ Kt n m t ω)
    (fun n ω l hl _ t _ => gueLproc_odd sz E t1 t0 _ _ n l hl t ω)
    (fun ε hε => (gueKproc_detDom sz hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hscale hell hKb Kt hKinit hK
      ε hε).mono fun n hn u => hn u.1 u.2)
    (perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun n ω _ m _ _ => gueLproc_continuousOn sz E t1 t0 _ _ n m ω))
    (gueBds_h745E sz hd hadm hκ hτU n0 hn0 hE ht1 ht10 ht0 h730 hscale hell hKb Kt hKinit hK hLK)
  have h728 := eq728GAt (Pgue sz) sz.size hsz (n0 := n0)
    (fun n => ((sz.size n : ℕ) : ℝ)) (fun n => etaT (E n)) t1 t0
    (fun n m t ω => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n m t ω)
    (fun n m t ω => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω)
    hNpos ht10 hη hanti hηc hτU h730' hscale'
    (fun n m t ω => gueLproc_nonneg sz E t1 t0 _ _ n m t ω)
    (fun n m t ω => gueDproc_nonneg sz E t1 t0 _ _ Kt n m t ω) h727
    (perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun n ω _ m _ => gueDproc_continuousOn sz E t1 t0 _ _ Kt n m ω))
    (gueBds_h746 sz hadm hκ hτU n0 hn0 hE ht1 ht10 ht0 h730 hscale hell hKb Kt hKinit hK hLK)
  /- The other random inputs: D4a with `δ = N^{-τU/4}`, the step-`0` local law, truncation. -/
  have hD4 := gueGrid_entry_bound sz hd hadm hκ n0 hE ht1 ht10 ht0 (δ := gueDelta sz τU)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := τU / 4) (by positivity)
    (Eventually.of_forall fun n => le_of_eq rfl)
  have hinit := PathBounds_init_local sz t0 (gueGridK sz n0) hsz hEb ht10 ht0 hell hLoc
  /- Unfreezing and conclusion on the intersection of the good events. -/
  have hmain : ∀ τ : ℝ, 0 < τ → HighProbAt (Pgue sz) sz.size
      (fun n => {ω : PathΩ sz | BoundsACheck.Concl sz E t1 t0 n0 Kt τ n ω}) := by
    intro τ hτ
    set τ₁ : ℝ := min τ τU / 16 with hτ₁
    have hτ₁0 : 0 < τ₁ := by have := lt_min hτ hτU; positivity
    have hτ₁τ : τ₁ < τ := by have := min_le_left τ τU; have := lt_min hτ hτU; linarith
    have hneg : 2 * τ₁ - τU / 2 < 0 := by have := min_le_right τ τU; linarith
    have hev := perTimeCalc_highProbAt_inter hsz
      (perTimeCalc_highProbAt_inter hsz
        (perTimeCalc_highProbAt_inter hsz
          (perTimeCalc_highProbAt_inter hsz
            (BoundsACheck.highProbAt_hA sz E t1 t0 n0 τU hτ₁0 h727)
            (BoundsACheck.highProbAt_hB sz E t1 t0 n0 τU hτ₁0 Kt h728))
          (BoundsACheck.highProbAt_HC sz E t1 t0 n0 τU hτ₁0 hD4))
        (BoundsACheck.highProbAt_hD sz E t1 t0 n0 hτ₁0 hinit))
      (BoundsACheck.highProbAt_hF sz n0 hsz)
    refine perTimeCalc_highProbAt_mono hev ?_
    filter_upwards [hscale', hell1,
      hsz.eventually (eventually_rpow_le_of_neg hneg (by norm_num : (0 : ℝ) < 1 / 32)),
      hsz.eventually (eventually_le_rpow 2 (sub_pos.2 hτ₁τ))]
      with n hscN hellN hsmallN h4N
    rintro ω ⟨⟨⟨⟨hA, hBω⟩, hC⟩, hD⟩, hFω⟩
    exact Bounds_path sz n0 hn0 Kt n hτU (hEb n) (ht1 n) (ht10 n) (ht0 n) hτ₁0 hτ₁τ hscN hellN
      hsmallN h4N ω hA hBω hC hD hFω
  exact BoundsACheck.pathBounds_of_forall_highProbAt sz E t1 t0 n0 Kt hmain

end PathBoundsMain

end RBM.Univ.GUEPhase

/-! ### Compiled nonempty instances of the three targets

Namespace `RBM.Univ.GUEPhase.PathBoundsInst`.  Data: the merged `SizesInst.sz0` (`Grid.lean`
§`GridCheck` sizes, `d = 3`, `L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`, `ilambda_n = (2 (n+1))^{-6}`,
`N_n = 8 (2 (n+1))^{18}`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `E_n = 0` (`Im m = 1`),
`κ = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10` (`sz0_admissible`), `τ_U = 1/1000`, `n₀ = 2`, and the window of
`HypAInst`: `1 - t₁ = y_n := ilambda²/L^3` (the boundary of `hell`), `t₀ - t₁ = y_n/(N+1)`,
`1 - t₀ = y_n N/(N+1)`; `Kt` is the band K-loops (`gueK_exists`), `hKb` the merged
`stKbound_holds`.  Every deterministic hypothesis is discharged (`hadm`, `hE`, `ht1`, `ht10`,
`ht0`, `h730`, `hscale`, `hell`, `hell1`, `hKb`, `hKinit`, `hK`); the hypotheses `hLK`, `hLoc` are
the conclusions of `UNMLOut` (another gate, `Universality/Pins.lean:432`) and stay hypotheses of
the examples.  At `n = 0`: `N η_{t₀} = 8 N/(N+1) ≈ 8`, `L^3 (1 - t₁) = ilambda² = 1/4096`. -/

namespace RBM.Univ.GUEPhase.PathBoundsInst

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open RBM.Gauss.SizesInst

private def Ei : ℕ → ℝ := fun _ => 0
private def Nn (n : ℕ) : ℝ := ((sz0.size n : ℕ) : ℝ)
private def yy (n : ℕ) : ℝ := sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3
private def tw1 (n : ℕ) : ℝ := 1 - yy n
private def tw0 (n : ℕ) : ℝ := 1 - yy n * Nn n / (Nn n + 1)

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem mE_zero_im : (mE 0).im = 1 := by
  have : mE 0 = Complex.I := by apply Complex.ext <;> simp [mE, sqrt_four]
  rw [this]; simp

private theorem Nn_ge_one (n : ℕ) : 1 ≤ Nn n := by
  have h1 : 0 < sz0.size n := by
    unfold Sizes.size
    have := sz0.W_pos n
    have := sz0.three_le_L n
    positivity
  unfold Nn
  exact Nat.one_le_cast.2 h1

private theorem lam_eq (n : ℕ) : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl

private theorem lam_nonneg (n : ℕ) : 0 ≤ sz0.lam n := by rw [lam_eq]; positivity

private theorem lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  rw [lam_eq]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))

private theorem yy_pos (n : ℕ) : 0 < yy n := by
  have hL : ((sz0.L n : ℕ) : ℝ) = 4 * ((n : ℝ) + 1) := by simp [sz0]
  unfold yy
  rw [lam_eq, hL]
  positivity

private theorem yy_le_one (n : ℕ) : yy n ≤ 1 := by
  have hL : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    have : (3 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast sz0.three_le_L n
    linarith
  unfold yy
  rw [div_le_one (by positivity)]
  nlinarith [one_le_pow₀ (n := 3) hL, pow_le_one₀ (n := 2) (lam_nonneg n) (lam_le_one n)]

private theorem tw1_nonneg (n : ℕ) : 0 ≤ tw1 n := by unfold tw1; linarith [yy_le_one n]

private theorem tw_frac (n : ℕ) : Nn n / (Nn n + 1) ≤ 1 := by
  have := Nn_ge_one n
  rw [div_le_one (by linarith)]; linarith

private theorem tw1_le_tw0 (n : ℕ) : tw1 n ≤ tw0 n := by
  unfold tw1 tw0
  have := mul_le_of_le_one_right (yy_pos n).le (tw_frac n)
  have e : yy n * Nn n / (Nn n + 1) = yy n * (Nn n / (Nn n + 1)) := by ring
  rw [e]; linarith

private theorem tw0_lt_one (n : ℕ) : tw0 n < 1 := by
  unfold tw0
  have := Nn_ge_one n
  have : 0 < yy n * Nn n / (Nn n + 1) := by have := yy_pos n; positivity
  linarith

private theorem etaT_tw0 (n : ℕ) : etaT 0 (tw0 n) = yy n * Nn n / (Nn n + 1) := by
  unfold etaT tw0; rw [mE_zero_im]; ring

private theorem h730_at (n : ℕ) :
    tw0 n - tw1 n ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 1000 : ℝ)) * etaT 0 (tw0 n) := by
  have hN := Nn_ge_one n
  have hN0 : 0 < Nn n := by linarith
  have h1 : (1 : ℝ) ≤ Nn n ^ (-(1 / 1000 : ℝ)) * Nn n := by
    rw [← Real.rpow_add_one hN0.ne']
    exact Real.one_le_rpow hN (by norm_num)
  rw [etaT_tw0]
  change _ ≤ Nn n ^ (-(1 / 1000 : ℝ)) * _
  have e : tw0 n - tw1 n = yy n / (Nn n + 1) := by unfold tw0 tw1; field_simp; ring
  rw [e]
  have hy := yy_pos n
  have : yy n / (Nn n + 1) * 1 ≤ yy n / (Nn n + 1) * (Nn n ^ (-(1 / 1000 : ℝ)) * Nn n) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc yy n / (Nn n + 1) = yy n / (Nn n + 1) * 1 := (mul_one _).symm
    _ ≤ _ := this
    _ = _ := by ring

private theorem hell_at (n : ℕ) : ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - tw1 n) ≤ sz0.lam n ^ 2 := by
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) ^ 3 := by
    have : (3 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast sz0.three_le_L n
    positivity
  have : 1 - tw1 n = yy n := by unfold tw1; ring
  rw [this]
  exact (mul_div_cancel₀ _ hL.ne').le

/-- `hell1` (`T2361b`): `L^3 (1 - t₁) = ilambda² ≤ 1` since `ilambda ≤ 1` at `sz0`. -/
private theorem hell1_at (n : ℕ) : ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - tw1 n) ≤ 1 :=
  (hell_at n).trans (pow_le_one₀ (lam_nonneg n) (lam_le_one n))

/-- `N · y = W^3 ilambda² = (2 (n+1))^3` at `sz0`. -/
private theorem Nn_yy (n : ℕ) : Nn n * yy n = (2 * ((n : ℝ) + 1)) ^ 3 := by
  have hL : ((sz0.L n : ℕ) : ℝ) = 4 * ((n : ℝ) + 1) := by simp [sz0]
  have hW : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
  have hN : Nn n = ((sz0.W n : ℕ) : ℝ) ^ 3 * ((sz0.L n : ℕ) : ℝ) ^ 3 := by
    unfold Nn Sizes.size; push_cast; ring
  unfold yy
  rw [hN, lam_eq, hL, hW]
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp

/-- `N = 8 (2 (n+1))^{18} ≤ (2 (n+1))^{21}` at `sz0`. -/
private theorem Nn_le (n : ℕ) : Nn n ≤ (2 * ((n : ℝ) + 1)) ^ 21 := by
  have hL : ((sz0.L n : ℕ) : ℝ) = 4 * ((n : ℝ) + 1) := by simp [sz0]
  have hW : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
  have hN : Nn n = ((sz0.W n : ℕ) : ℝ) ^ 3 * ((sz0.L n : ℕ) : ℝ) ^ 3 := by
    unfold Nn Sizes.size; push_cast; ring
  have hm : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set m : ℝ := 2 * ((n : ℝ) + 1) with hmdef
  have h4 : 4 * ((n : ℝ) + 1) = 2 * m := by rw [hmdef]; ring
  rw [hN, hL, hW, h4]
  have h8 : (8 : ℝ) ≤ m ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm 3]
  calc (m ^ 5) ^ 3 * (2 * m) ^ 3 = 8 * m ^ 18 := by ring
    _ ≤ m ^ 3 * m ^ 18 := mul_le_mul_of_nonneg_right h8 (by positivity)
    _ = m ^ 21 := by ring

/-- `hscale` at `sz0`: `N^{1/1000} ≤ 2 (n+1) ≤ (2 (n+1))^3 / 2 ≤ N η_{t₀}`. -/
private theorem hscale_at (n : ℕ) :
    (gueScale sz0 Ei n (tw0 n))⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hN := Nn_ge_one n
  have hN0 : 0 < Nn n := by linarith
  have hm : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set m : ℝ := 2 * ((n : ℝ) + 1) with hmdef
  have hm0 : 0 < m := by linarith
  have h1 : Nn n ^ (1 / 1000 : ℝ) ≤ m := by
    calc Nn n ^ (1 / 1000 : ℝ) ≤ (m ^ 21) ^ (1 / 1000 : ℝ) :=
          Real.rpow_le_rpow hN0.le (Nn_le n) (by norm_num)
      _ = m ^ ((21 : ℝ) / 1000) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
      _ ≤ m ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = m := Real.rpow_one m
  have h2 : m ≤ m ^ 3 / 2 := by nlinarith [sq_nonneg m]
  have h3 : m ^ 3 / 2 ≤ gueScale sz0 Ei n (tw0 n) := by
    have e : gueScale sz0 Ei n (tw0 n) = (Nn n * yy n) * (Nn n / (Nn n + 1)) := by
      change Nn n * etaT (Ei n) (tw0 n) = _
      rw [show Ei n = 0 from rfl, etaT_tw0]; ring
    rw [e, Nn_yy]
    have hfrac : 1 / 2 ≤ Nn n / (Nn n + 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    have hm3 : 0 ≤ m ^ 3 := by positivity
    nlinarith
  have hpos : 0 < Nn n ^ (1 / 1000 : ℝ) := Real.rpow_pos_of_pos hN0 _
  change (gueScale sz0 Ei n (tw0 n))⁻¹ ≤ Nn n ^ (-(1 / 1000 : ℝ))
  rw [Real.rpow_neg hN0.le]
  exact inv_anti₀ hpos (h1.trans (h2.trans h3))

private theorem hE_at : ∀ n, |Ei n| ≤ 2 - 1 / 10 := fun n => by norm_num [Ei]

/-- The stationary-free primitive family of the instance: the band K-loops (`gueK_exists`,
`g = ilambda_n`), loops up to length `4 n₀ = 8`. -/
private theorem exists_Kt :
    ∃ Kt : (n : ℕ) → ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ,
      (∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd 3 (sz0.L n)),
        Kt n (tw1 n) (loopOf σ a) = sz0.STKloop n (Ei n) (tw1 n) σ a) ∧
      (∀ n, ∀ t ∈ Set.Icc (tw1 n) (tw0 n), ∀ I : RBM.Loop.LoopIdx (Zd 3 (sz0.L n)), I.WF →
        1 ≤ I.length → I.length ≤ 4 * 2 →
        HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE 3 (sz0.L n) (sz0.W n) (Kt n t) I)
          (Set.Icc (tw1 n) (tw0 n)) t) := by
  choose Kt h1 h2 _ using fun n => RBM.Univ.GUEPhase.gueK_exists 3 (sz0.L n) (sz0.W n)
    (sz0.three_le_L n) (sz0.lam n) (E := Ei n) (by norm_num [Ei]) (tw1_nonneg n)
    (tw1_le_tw0 n) (tw0_lt_one n) (4 * 2)
  exact ⟨Kt, fun n k σ a => h1 n _, fun n t ht I hI h hl => h2 n t ht I hI h hl⟩

private def Kt0 : (n : ℕ) → ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ := exists_Kt.choose

private theorem Kt0_init : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd 3 (sz0.L n)),
    Kt0 n (tw1 n) (loopOf σ a) = sz0.STKloop n (Ei n) (tw1 n) σ a := exists_Kt.choose_spec.1

private theorem Kt0_deriv : ∀ n, ∀ t ∈ Set.Icc (tw1 n) (tw0 n),
    ∀ I : RBM.Loop.LoopIdx (Zd 3 (sz0.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * 2 →
    HasDerivWithinAt (fun s => Kt0 n s I) (primRhsGUE 3 (sz0.L n) (sz0.W n) (Kt0 n t) I)
      (Set.Icc (tw1 n) (tw0 n)) t := exists_Kt.choose_spec.2

/-- `STKbound` at `sz0`, `E = 0` (merged `Sizes.stKbound_holds`, `κ = 1/10`, `gmax = 1`). -/
private theorem hKb0 : sz0.STKbound Ei :=
  Sizes.stKbound_holds sz0 (le_refl 3) (κ := 1 / 10) (gmax := 1) (by norm_num) one_pos sz0_tendsto
    (Eventually.of_forall fun n => by norm_num [Ei])
    (Eventually.of_forall fun n => ⟨by
      change (0:ℝ) < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹; positivity, by
      change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ (1:ℝ)
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg n:(0:ℝ) ≤ n)]))⟩)

/-- **`gueBds_h745E` at `sz0`** (`d = 3`, `κ = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`, `τ_U = 1/1000`,
`n₀ = 2`, `E = 0`, the window above): every deterministic hypothesis is discharged; `hLK` (the
loop conclusion of `UNMLOut`) stays a hypothesis of the example. -/
example (hLK : sz0.STLK Ei tw1) :=
  gueBds_h745E sz0 (le_refl 3) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := 1 / 10) (τU := 1 / 1000)
    sz0_admissible (by norm_num) (by norm_num) 2 le_rfl (E := Ei) (t1 := tw1) (t0 := tw0)
    hE_at tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at)
    (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at) hKb0 Kt0 Kt0_init Kt0_deriv hLK

/-- **`gueBds_h746` at `sz0`** (same data; no `hd`, no entry bound). -/
example (hLK : sz0.STLK Ei tw1) :=
  gueBds_h746 sz0 (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := 1 / 10) (τU := 1 / 1000)
    sz0_admissible (by norm_num) (by norm_num) 2 le_rfl (E := Ei) (t1 := tw1) (t0 := tw0)
    hE_at tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at)
    (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at) hKb0 Kt0 Kt0_init Kt0_deriv hLK

/-- **`gueGrid_pathBounds` at `sz0`** (same data, plus `hell1`): `GUEPathBounds` for the window,
`n₀ = 2`, the band K-loops `Kt0`; `hLK`, `hLoc` (conclusions of `UNMLOut`) are hypotheses. -/
example (hLK : sz0.STLK Ei tw1) (hLoc : sz0.STLocalEntry Ei tw1) :
    GUEPathBounds sz0 Ei tw1 tw0 (gueGridK sz0 2) 2 Kt0 :=
  gueGrid_pathBounds sz0 (le_refl 3) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := 1 / 10) (τU := 1 / 1000)
    sz0_admissible (by norm_num) (by norm_num) 2 le_rfl (E := Ei) (t1 := tw1) (t0 := tw0)
    hE_at tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at)
    (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at)
    (Eventually.of_forall hell1_at) hKb0 Kt0 Kt0_init Kt0_deriv hLK hLoc

end RBM.Univ.GUEPhase.PathBoundsInst

end
