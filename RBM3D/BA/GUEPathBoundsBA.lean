/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEHypBBA
import RBM3D.BA.GUEDuhamelBA2
import RBM3D.Universality.GUEPhase.PathBounds

/-!
# The output of the random layer of [YY_25, §7.2] on the BA grid

Band counterpart: `Universality/GUEPhase/PathBounds.lean` (`PathBounds_init_loops`,
`PathBounds_init_local`,
`gueBds_h745E`, `gueBds_h746`, `gueGrid_pathBounds`).  Paper: the GUE phase of Theorem 2.4
(`Thm: B_Univ`; "essentially identical to [YY_25, Theorem 2.6]"),
`d ≥ 3`, block Anderson
`S^{(B)}(0) = 1`.  The equation numbers (7.28), (7.45), (7.46) below are those of [YY_25, §7.2].

Under the hypotheses of `gueGrid_pathBoundsBA` the BA grid path `gueHBA` (`g Ψ_I + H_k`) satisfies
`GUEPathBoundsBA`
(`BA/GUEProcBA`) on the grid `gueGridK sz 4` with `n₀ = 4`: (7.28) at every
grid time `k ≤ K n` for
`1 ≤ l ≤ 4` against the primitive family `Kt`, and `‖G̃ - M‖_max ≺ (N η_u)^{-1/2}` against the
deterministic
`M = Mres (g Ψ_I) E m = M^{(B)} ⊗ 1`, `η_u = (1 - u) Im m`, on the size scale `N = (W L)^d`.

What changes from the band (statements at the flow datum `(g, E, m)`; the data are
real-axis solutions, `BAReal`
at every `n`, and the coupling window `0 < g n ≤ 𝔡⁻¹` is eventual):

* the step-`0` inputs `hLK : STLKgL (baFM sz g E) (seqP (sz.withLam 0)) t₁`,
  `hLoc : STLocalEntrygL …` are on the BA carrier at the
  flow parameters `(g, E)` (the first and second conjuncts of `BAMO`, `BA/RandomLayerBGBA`); the
  path at step `0` is the BA flow
  matrix `seqHflowBA g n t₁ (ω 0)`, and `m = BAm d L g E` by the uniqueness of the real-axis
  solution (`BASelf_unique`);
* the K-bound is the conclusion of `Hyp_Kt_detDomBA` (`BAKFam` clauses, guarded by
  `0 < g n`), no `STKbound`;
* the entry bound is `gueGrid_entry_boundBA'` (the eventual window), the Duhamel remainder
  `gueGrid_loop_duhamelBA`,
  the pathwise assembly `HypB_entry_leBA`, `HypB_eG_745BA`, `HypB_eG_746BA`, `HypB_fixedBA`, `Bounds_pathBA` (`BA/GUEHypBBA`);
* the constant of the band, `1 + 2 lam²`, is `A = 1 + 4/κ²` (`GUEHypBBA`), a number: no
  `hellN`-type hypothesis on `g`;
* the K-lemmas of `BA/GUEHypABA` need `L^d (1 - t₁) ≤ 2 g²` (`hellg`); at `g = √t₀ lam` it follows from
  `hell`, `hell1`
  (`GUEHypABA_hell_of_hell`).

The band privates without a band token (`PathBounds_map_eval0`, `PathBounds_step0_le`,
`PathBounds_gueH_zero`,
`PathBounds_Gres_true`, `PathBounds_Bctl_nonneg`, `PathBounds_STWB_le`) are used through `open private`.

* §1 `GUEPathBoundsBA_init_loops`, `GUEPathBoundsBA_init_local` (the step-`0` laws), the conversion
  `Bctl ≤ 2 (N η)⁻¹`;
* §2 `gueBds_h745EBA`, `gueBds_h746BA` (the inputs `h745`, `h746` of `eq727GEAt`, `eq728GAt`);
* §3 `gueGrid_pathBoundsBA`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private PathBounds_map_eval0 PathBounds_step0_le PathBounds_gueH_zero PathBounds_Gres_true PathBounds_Bctl_nonneg
  PathBounds_STWB_le from RBM3D.Universality.GUEPhase.PathBounds

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

/-! ## 1. The step-0 laws -/

section PathBoundsBAInit

variable {d : ℕ} (sz : Sizes d)

/-- At the real-axis datum `m` is the solution `BAm` (`BASelf_unique`). -/
private theorem GUEPathBoundsBA_m_eq {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    m = BAm d L g (E : ℂ) :=
  BASelf_unique d L g (E : ℂ) m _ (by simp) hr.1 (BAm_spec ⟨m, hr.1⟩)

/-- The BA grid path at step `0` is the BA flow matrix at `t₁` (`H_0 = seqHflowBA g n t₁ (ω 0)`). -/
private theorem GUEPathBoundsBA_gueHBA_zero (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ω : PathΩ (sz.withLam 0)) :
    gueHBA sz g t1 t0 K n 0 ω = sz.seqHflowBA g n (t1 n) (ω 0) := by
  unfold gueHBA Sizes.seqHflowBA
  rw [PathBounds_gueH_zero (sz.withLam 0)]
  rfl

/-- The conversion `W^{-d} B_{t,0} ≤ 2 (N η_t)⁻¹` under the zero-mode condition `L^d (1 - t) ≤ lam²` (`hell`), at
`η_t = (1 - t) Im m` with `0 < Im m ≤ 1` (the analogue of `PathBounds_Bctl_le`). -/
private theorem GUEPathBoundsBA_Bctl_le (n : ℕ) {m : ℂ} (hm : 0 < m.im) (hm1 : ‖m‖ ≤ 1) {t : ℝ} (ht : t < 1)
    (hell : ((sz.L n : ℕ) : ℝ) ^ d * (1 - t) ≤ sz.lam n ^ 2) :
    sz.Bctl n t ≤ 2 * (((sz.size n : ℕ) : ℝ) * etaOf m t)⁻¹ := by
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
  have hηpos : 0 < etaOf m t := by unfold etaOf; exact mul_pos hx hm
  have hmim := HypBBA_im_le_one hm1
  have hηle : etaOf m t ≤ 1 - t := by
    unfold etaOf
    calc (1 - t) * m.im ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left hmim hx.le
      _ = 1 - t := mul_one _
  have h1 : (sz.lam n ^ 2 + (1 - t))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ :=
    inv_anti₀ (mul_pos hLd hx) (by nlinarith [sq_nonneg (sz.lam n)])
  have hB : Bparam d (sz.L n) (sz.lam n) t 0 ≤ 2 * (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ := by
    unfold Bparam
    rw [abs_of_pos hx]
    have e : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
    rw [e, mul_one]
    linarith
  have hNx : (((sz.size n : ℕ) : ℝ) * (1 - t))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * etaOf m t)⁻¹ :=
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
    _ ≤ 2 * (((sz.size n : ℕ) : ℝ) * etaOf m t)⁻¹ := by linarith

/-- **The loops at step `0`** (the analogue of `PathBounds_init_loops`): the step-`0` input `‖L_0 - K̃_{t₁}‖ ≺ (N η_{t₁})^{-k}`
on `Pgue (sz.withLam 0)`, from `STLKgL` of the BA carrier at `(g, E)` at `t₁` transferred through the coordinate marginal, with
`K̃_{t₁} = BAKsol` (`hKinit`, guarded by `0 < g n`) and `W^{-d} B_{t₁,0} ≤ 2 (N η_{t₁})⁻¹` (`hell`). -/
private theorem GUEPathBoundsBA_init_loops {κ : ℝ} {g E t1 : ℕ → ℝ} {m : ℕ → ℂ} (t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (hsz : Tendsto sz.size atTop atTop) (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))
    (hg : ∀ᶠ n in atTop, 0 < g n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hLK : STLKgL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1) (k : ℕ) (hk : 1 ≤ k) :
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (x : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n 0 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
          Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖)
      (fun n _ _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n))⁻¹ ^ k) := by
  obtain rfl : m = BAmF sz g E := funext fun n => GUEPathBoundsBA_m_eq (hr n)
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hLK k hk (τ / 2) hτ2 D hD, hell, hg,
    hsz.eventually (eventually_le_rpow ((2 : ℝ) ^ k) hτ2), hsz.eventually (eventually_ge_atTop 1)]
    with n hn hellN hgn h2k hN1
  refine le_trans (measure_mono ?_) (le_trans (PathBounds_step0_le (sz.withLam 0) _) hn)
  intro ω hω
  simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨x, hx⟩ := hω
  refine ⟨x, ?_⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hlt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hm : 0 < (BAmF sz g E n).im := (hr n).1.1
  have hm1 : ‖BAmF sz g E n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) _ (by simp) (hr n).1
  have hB := GUEPathBoundsBA_Bctl_le sz n hm hm1 hlt hellN
  have hB0 := PathBounds_Bctl_nonneg sz n (t1 n)
  have hΛ0 : 0 ≤ (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ k := by
    have : 0 < ((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n) := by
      unfold etaOf; exact mul_pos hN0 (mul_pos (by linarith) hm)
    positivity
  have hpow : sz.Bctl n (t1 n) ^ k ≤ (2 : ℝ) ^ k * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB0 hB k
  have hrpow : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hc0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  have hkey : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (t1 n) ^ k ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ k := by
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (t1 n) ^ k
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((2 : ℝ) ^ k * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ k) :=
          mul_le_mul_of_nonneg_left hpow hc0
      _ = ((2 : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ k := by
          ring
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) *
            (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ hΛ0
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2k hc0
      _ = ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ k := by rw [hrpow]
  have hgt : gridTime t1 t0 K n 0 = t1 n := by simp [gridTime]
  rw [GUEPathBoundsBA_gueHBA_zero, hgt, hKinit n hgn, ← loopM_eq_loopL] at hx
  exact lt_of_le_of_lt hkey hx

/-- **The local law at step `0`** (the analogue of `PathBounds_init_local`): `STLocalEntrygL` of the BA carrier at `t₁`
transferred to `Pgue (sz.withLam 0)` through the coordinate marginal: `‖(G - M)_{xy}‖² ≺ STWB ≤ Bctl ≤ 2 (N η_{t₁})⁻¹` (`hell`), so
`‖(G - M)_{xy}‖ ≺ (N η_{t₁})^{-1/2}`, `M = Mres (g Ψ_I) E m`; the factor `2` is absorbed in `N^τ`. -/
private theorem GUEPathBoundsBA_init_local {κ : ℝ} {g E t1 : ℕ → ℝ} {m : ℕ → ℂ} (t0 : ℕ → ℝ) (K : ℕ → ℕ)
    (hsz : Tendsto sz.size atTop atTop) (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hLoc : STLocalEntrygL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1) :
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ω =>
        ‖(green (gueHBA sz g t1 t0 K n 0 ω) (ztOf (m n) (E n) (t1 n)) -
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) ij.1 ij.2‖)
      (fun n _ _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) := by
  obtain rfl : m = BAmF sz g E := funext fun n => GUEPathBoundsBA_m_eq (hr n)
  intro τ hτ D hD
  filter_upwards [hLoc τ hτ D hD, hell, hsz.eventually (eventually_le_rpow (2 : ℝ) hτ),
    hsz.eventually (eventually_ge_atTop 1)] with n hn hellN h2 hN1
  refine le_trans (measure_mono ?_) (le_trans (PathBounds_step0_le (sz.withLam 0) _) hn)
  intro ω hω
  simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨ij, hij⟩ := hω
  refine ⟨ij, ?_⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hlt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hm : 0 < (BAmF sz g E n).im := (hr n).1.1
  have hm1 : ‖BAmF sz g E n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) _ (by simp) (hr n).1
  have hB := GUEPathBoundsBA_Bctl_le sz n hm hm1 hlt hellN
  have hW := PathBounds_STWB_le sz n (t1 n) (zdistInf d (sz.L n) (sz.STblk n ij.1 - sz.STblk n ij.2))
  have hsc : 0 < ((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n) := by
    unfold etaOf; exact mul_pos hN0 (mul_pos (by linarith) hm)
  have hΛ0 : 0 ≤ (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ := inv_nonneg.2 hsc.le
  have hcp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg hN0.le _
  have hsqrt : ((((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 =
      (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0]; norm_num
  have hrhs0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ ((1 : ℝ) / 2) :=
    mul_nonneg hcp (Real.rpow_nonneg hΛ0 _)
  have hsq : (((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) ^ 2 <
      ‖(green (sz.seqHflowBA g n (t1 n) (ω 0)) (ztOf (BAmF sz g E n) (E n) (t1 n)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (BAmF sz g E n)) ij.1 ij.2‖ ^ 2 := by
    rw [GUEPathBoundsBA_gueHBA_zero] at hij
    exact pow_lt_pow_left₀ hij hrhs0 (by norm_num)
  have hGM : ‖(baFM sz g E).GM n (t1 n) (ω 0) ij.1 ij.2‖ =
      ‖(green (sz.seqHflowBA g n (t1 n) (ω 0)) (ztOf (BAmF sz g E n) (E n) (t1 n)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (BAmF sz g E n)) ij.1 ij.2‖ := by
    change ‖Gres (sz.seqHflowBA g n (t1 n) (ω 0)) (ztOf (BAmF sz g E n) (E n) (t1 n)) true ij.1 ij.2 -
      Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (BAmF sz g E n) ij.1 ij.2‖ = _
    rw [PathBounds_Gres_true]
    rfl
  change _ < ‖(baFM sz g E).GM n (t1 n) (ω 0) ij.1 ij.2‖ ^ 2
  rw [hGM]
  refine lt_of_le_of_lt ?_ hsq
  rw [mul_pow, hsqrt, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have h2' : ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) ^ τ) =
      ((sz.size n : ℕ) : ℝ) ^ ((τ * (2 : ℕ)) : ℝ) := by
    rw [← Real.rpow_add hN0]; push_cast; ring_nf
  calc ((sz.size n : ℕ) : ℝ) ^ τ * sz.STWB n (t1 n) (zdistInf d (sz.L n) (sz.STblk n ij.1 - sz.STblk n ij.2))
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (2 * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹) :=
        mul_le_mul_of_nonneg_left (hW.trans hB) hcp
    _ = (((sz.size n : ℕ) : ℝ) ^ τ * 2) * (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ := by ring
    _ ≤ (((sz.size n : ℕ) : ℝ) ^ τ * ((sz.size n : ℕ) : ℝ) ^ τ) *
          (((sz.size n : ℕ) : ℝ) * etaOf (BAmF sz g E n) (t1 n))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hcp) hΛ0
    _ = _ := by rw [h2']

end PathBoundsBAInit

/-! ## 2. (7.45)G and (7.46)G for the stopped, interpolated processes at BA -/

section PathBoundsBAHyp

open RBM.Ind.PerTimeCalc

variable {d : ℕ} (sz : Sizes d)

/-- **(7.45)G at even lengths `2 ≤ l ≤ 2n₀`** for the stopped, interpolated BA processes (the analogue of `gueBds_h745E`): the
`h745` of `eq727GEAt` (with `n₀' = 2 n₀`), over the whole interval `[t₁, t₀]`, on `Pgue (sz.withLam 0)` and the size scale.  The
step-`0` input is `STLKgL` of the BA carrier at `(g, E)` at `t₁`; the K-bound is `Hyp_Kt_detDomBA`, the entry-bound input
`gueGrid_entry_boundBA'` (the coupling window is eventual, `BAReal` at every `n`), the Duhamel remainder
`gueGrid_loop_duhamelBA`.  The constant is `A = 1 + 4/κ²`. -/
theorem gueBds_h745EBA (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (_hn0 : 2 ≤ n0) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (hlam : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹)
    (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hellg : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t)
    (hLK : STLKgL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1) :
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : TimeIcc t1 t0 n × {l : ℕ // l ∈ Set.Icc 2 (2 * n0) ∧ Even l}) ω =>
        gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n p.2.1 p.1 ω)
      (fun n p ω => rhs745G ((sz.size n : ℕ) : ℝ) (etaOf (m n)) (t1 n)
        (fun l t => gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n l t ω)
        (fun l t => gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l t ω) p.2.1 p.1) := by
  classical
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hadm.2.2.1
  have hm : ∀ n, 0 < (m n).im := fun n => (hr n).1.1
  have hm1 : ∀ n, ‖m n‖ ≤ 1 := fun n => BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) (hr n).1
  have hI := fun k (hk : 1 ≤ k) =>
    GUEPathBoundsBA_init_loops sz t0 (gueGridK sz n0) hsz hr (hlam.mono fun n h => h.1) ht10 ht0 hell Kt hKinit hLK k hk
  have hKtd := Hyp_Kt_detDomBA hd sz hκ (inv_pos.2 hadm.2.1) hτU n0 hr hlam ht1 ht10 ht0 hsz h730 hellg Kt hKinit hK
  have hD4 := gueGrid_entry_boundBA' sz hd hadm hκ n0 hr hlam ht1 ht10 ht0 (δ := gueDelta sz τU)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := τU / 4) (by positivity)
    (Eventually.of_forall fun n => le_of_eq rfl)
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 _ => perTimeCalc_highProbAt_of_stochDomAt (hI k h1) hτ2)
  have hG2 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 h2 => perTimeCalc_highProbAt_of_stochDomAt
      (gueGrid_loop_duhamelBA sz hτU n0 (g := g) (E := E) (t1 := t1) (t0 := t0) (m := m) hsz hm hm1 ht1 ht10 ht0 hscale k h1 h2)
        hτ2)
  have hG3 := perTimeCalc_highProbAt_of_stochDomAt hD4 hτ2
  filter_upwards [(perTimeCalc_highProbAt_inter hsz (perTimeCalc_highProbAt_inter hsz hG1 hG2) hG3) D hD,
    hKtd (τ / 2) hτ2, hKtd (τU / 2) (by positivity), hscale, h730, HypB_ev_grid sz hsz n0,
    HypBBA_ev_delta sz hκ hτU hsz,
    hlam,
    hsz.eventually (eventually_le_rpow (2 + 2 ^ (2 * n0) + (3 + 4 * (1 + 4 / κ ^ 2)) * ((2 * n0 : ℕ) : ℝ) ^ 2) hτ2),
    hsz.eventually (eventually_ge_atTop 1)]
    with n hGn hKtN hKt1N hscaleN h730N hgridN hδN hgn hbigN hN1
  refine (measure_mono ?_).trans hGn
  rintro ω ⟨⟨⟨t, ht⟩, ⟨l, ⟨hl2, hln⟩, heven⟩⟩, hp⟩ hω
  obtain ⟨⟨hω1, hω2⟩, hω3⟩ := hω
  obtain ⟨j, hj⟩ := heven
  have hnl : l = 2 * j := by omega
  subst hnl
  have hj1 : 1 ≤ j := by omega
  refine absurd hp (not_lt.2 ?_)
  have hω1' := hω1 (2 * j) (by omega) hln
  have hω2' := hω2 (2 * j) (by omega) hln
  simp only [Set.mem_ofPred_eq] at hω1' hω2' hω3
  have hN1R : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hc1 : (1 : ℝ) ≤ N ^ (τ / 2) := Real.one_le_rpow hN1R hτ2.le
  have hS0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ 4 / κ ^ 2 := by positivity
  have hA1 : (1 : ℝ) ≤ 1 + 4 / κ ^ 2 := by linarith
  exact HypB_fixedBA sz hτ n0 τU (A := 1 + 4 / κ ^ 2) (by linarith) Kt n (2 * j) ω
    (fun u => gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n 2 u ω *
      gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (2 * j) u ω)
    (fun u => Real.sqrt (N⁻¹ * (etaOf (m n) u)⁻¹ ^ 2) *
      gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (2 * j) u ω)
    (Ce := ((2 * j : ℕ) : ℝ) * (1 + 4 / κ ^ 2) * N ^ (τ / 2) * N)
    (hK n hgn.1) (hm n) (hm1 n) (ht1 n) (ht10 n) (ht0 n) (by omega) hln
    (HypBBA_step_le sz n0 n (hm n) (hm1 n) (ht10 n) (ht0 n) h730N hτU) hgridN.1 hgridN.2
    (HypBBA_Kt_le_one sz hτU n0 n Kt (hm n) (ht0 n) hKt1N hscaleN)
    hKtN hbigN (by positivity)
    (by
      have hl' : (1 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * j)
      have hc0 : (0 : ℝ) ≤ N ^ (τ / 2) := by linarith
      have h1 : ((2 * j : ℕ) : ℝ) ≤ 4 * ((2 * j : ℕ) : ℝ) ^ 2 := by nlinarith
      have h2 : 0 ≤ (1 + 4 / κ ^ 2) * N ^ (τ / 2) * N :=
        mul_nonneg (mul_nonneg (by linarith) hc0) hS0
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      nlinarith)
    (fun u _ => mul_nonneg (gueLprocBA_nonneg sz g E t1 t0 m _ _ n _ u ω) (gueLprocBA_nonneg sz g E t1 t0 m _ _ n _ u ω))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (gueLprocBA_nonneg sz g E t1 t0 m _ _ n _ u ω))
    ((gueLprocBA_continuousOn sz g E t1 t0 m _ _ n _ ω).mul (gueLprocBA_continuousOn sz g E t1 t0 m _ _ n _ ω))
    ((HypBBA_sqrt_cont sz n (hm n) (ht0 n)).mul (gueLprocBA_continuousOn sz g E t1 t0 m _ _ n _ ω))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun i hi => by
      rw [HypBBA_Lproc_grid sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (2 * j) i ω (ht10 n) hi]
      exact HypB_q_745 ((gueHBA_isHermitian sz g t1 t0 (gueGridK sz n0) n i ω).submatrix _) _
        (by positivity) hj1)
    (fun i hi x => by
      rw [HypBBA_Lproc_grid sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n 2 i ω (ht10 n) hi,
        HypBBA_Lproc_grid sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (2 * j) i ω (ht10 n) hi]
      exact HypB_eG_745BA sz (gueGridK sz n0) n i (hr n).1 ω hc1 hA1 hj1
        (fun q => HypB_entry_leBA sz hκ n0 n (hr n) hδN ω (by linarith)
          (fun k i' j' => hω3 (k, (i', j'))) hi q) x)
    ht

/-- **(7.46)G at lengths `1 ≤ l ≤ n₀`** for the stopped, interpolated BA processes (the analogue of `gueBds_h746`): the `h746`
of `eq728GAt`, over the whole interval `[t₁, t₀]`.  The step-`0` input is `STLKgL` at `t₁`; the entry bound is not needed; `K̃ = m_σ`
at length `1` is `Hyp_Kt_oneBA`. -/
theorem gueBds_h746BA (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (hlam : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹)
    (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hellg : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t)
    (hLK : STLKgL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1) :
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 1 n0) ω =>
        gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n p.2 p.1 ω)
      (fun n p ω => rhs746G ((sz.size n : ℕ) : ℝ) (etaOf (m n)) (t1 n)
        (fun l t => gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n l t ω)
        (fun l t => gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l t ω) p.2 p.1) := by
  classical
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hadm.2.2.1
  have hm : ∀ n, 0 < (m n).im := fun n => (hr n).1.1
  have hm1 : ∀ n, ‖m n‖ ≤ 1 := fun n => BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) (hr n).1
  have hI := fun k (hk : 1 ≤ k) =>
    GUEPathBoundsBA_init_loops sz t0 (gueGridK sz n0) hsz hr (hlam.mono fun n h => h.1) ht10 ht0 hell Kt hKinit hLK k hk
  have hKtd := Hyp_Kt_detDomBA hd sz hκ (inv_pos.2 hadm.2.1) hτU n0 hr hlam ht1 ht10 ht0 hsz h730 hellg Kt hKinit hK
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := by positivity
  have hG1 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 _ => perTimeCalc_highProbAt_of_stochDomAt (hI k h1) hτ2)
  have hG2 := HypB_highProb_range sz hsz (2 * n0) _
    (fun k h1 h2 => perTimeCalc_highProbAt_of_stochDomAt
      (gueGrid_loop_duhamelBA sz hτU n0 (g := g) (E := E) (t1 := t1) (t0 := t0) (m := m) hsz hm hm1 ht1 ht10 ht0 hscale k h1 h2)
        hτ2)
  filter_upwards [(perTimeCalc_highProbAt_inter hsz hG1 hG2) D hD, hKtd (τ / 2) hτ2, hKtd (τU / 2) (by positivity),
    hscale, h730, HypB_ev_grid sz hsz n0, hlam,
    hsz.eventually (eventually_le_rpow (2 + 2 ^ (2 * n0) + (3 + 4 * (1 + 4 / κ ^ 2)) * ((2 * n0 : ℕ) : ℝ) ^ 2) hτ2),
    hsz.eventually (eventually_ge_atTop 1)]
    with n hGn hKtN hKt1N hscaleN h730N hgridN hgn hbigN hN1
  refine (measure_mono ?_).trans hGn
  rintro ω ⟨⟨⟨t, ht⟩, ⟨l, hmem⟩⟩, hp⟩ hω
  have hl1 : 1 ≤ l := hmem.1
  have hln : l ≤ n0 := hmem.2
  obtain ⟨hω1, hω2⟩ := hω
  refine absurd hp (not_lt.2 ?_)
  have hl' : l ≤ 2 * n0 := by omega
  have hω1' := hω1 l hl1 hl'
  have hω2' := hω2 l hl1 hl'
  have hN1R : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hc1 : (1 : ℝ) ≤ N ^ (τ / 2) := Real.one_le_rpow hN1R hτ2.le
  have hS0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ 4 / κ ^ 2 := by positivity
  exact HypB_fixedBA sz hτ n0 τU (A := 1 + 4 / κ ^ 2) (by linarith) Kt n l ω
    (fun u => gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n 1 u ω *
      gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (l + 1) u ω)
    (fun u => Real.sqrt (N⁻¹ * (etaOf (m n) u)⁻¹ ^ 2) *
      Real.sqrt (gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (2 * l) u ω))
    (Ce := (l : ℝ) * N)
    (hK n hgn.1) (hm n) (hm1 n) (ht1 n) (ht10 n) (ht0 n) hl1 hl'
    (HypBBA_step_le sz n0 n (hm n) (hm1 n) (ht10 n) (ht0 n) h730N hτU) hgridN.1 hgridN.2
    (HypBBA_Kt_le_one sz hτU n0 n Kt (hm n) (ht0 n) hKt1N hscaleN)
    hKtN hbigN (by positivity)
    (by
      have hn1' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
      have hc0 : (0 : ℝ) ≤ N ^ (τ / 2) := by linarith
      have h1 : (l : ℝ) ≤ 4 * (1 + 4 / κ ^ 2) * (l : ℝ) ^ 2 * N ^ (τ / 2) := by
        have hAc : (1 : ℝ) ≤ (1 + 4 / κ ^ 2) * N ^ (τ / 2) := by nlinarith
        nlinarith
      calc (l : ℝ) * N ≤ (4 * (1 + 4 / κ ^ 2) * (l : ℝ) ^ 2 * N ^ (τ / 2)) * N :=
            mul_le_mul_of_nonneg_right h1 hS0
        _ = _ := by ring)
    (fun u _ => mul_nonneg (gueDprocBA_nonneg sz g E t1 t0 m _ _ Kt n _ u ω) (gueLprocBA_nonneg sz g E t1 t0 m _ _ n _ u ω))
    (fun u _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    ((gueDprocBA_continuousOn sz g E t1 t0 m _ _ Kt n _ ω).mul (gueLprocBA_continuousOn sz g E t1 t0 m _ _ n _ ω))
    ((HypBBA_sqrt_cont sz n (hm n) (ht0 n)).mul
      (Real.continuous_sqrt.comp_continuousOn (gueLprocBA_continuousOn sz g E t1 t0 m _ _ n _ ω)))
    (fun x => hω1' x)
    (fun k hk x => hω2' (⟨k, Nat.lt_succ_of_le hk⟩, x))
    (fun i hi => by
      rw [HypBBA_Lproc_grid sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (2 * l) i ω (ht10 n) hi,
        ← Real.sqrt_mul (by positivity)])
    (fun i hi x => by
      rw [HypBBA_Dproc_grid sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n 1 i ω (ht10 n) hi,
        HypBBA_Lproc_grid sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n (l + 1) i ω (ht10 n) hi]
      exact HypB_eG_746BA sz (gueGridK sz n0) Kt n i l ω
        (fun σ a => Hyp_Kt_oneBA sz hκ n0 (by omega) Kt hr ht1 ht10 ht0 hKinit hK n hgn.1
          (Hyp_time_mem (ht10 n) (gueGridK_ne_zero sz n0 n) ((le_of_lt hi).trans (firstHit_le _ _ _ ω))) σ a) x)
    ht

end PathBoundsBAHyp

/-! ## 3. The main statement -/

section PathBoundsBAMain

open RBM.Ind.PerTimeCalc

variable {d : ℕ} (sz : Sizes d)

/-- The proof of `gueGrid_pathBoundsBA` at a general `n₀ ≥ 2` (the public theorem is the case `n₀ = 4`): the two
bootstraps `eq727GEAt` (at `2 n₀`, `gueBds_h745EBA`) and `eq728GAt` (`gueBds_h746BA`); the other random inputs (the entry bound
`gueGrid_entry_boundBA'` at `δ = gueDelta sz τU`, `c₀ = τU/4`, the step-`0` local law, the increment truncation
`gue_highProb_incr_le`); the pathwise unfreezing `Bounds_pathBA` on their intersection (`τ₁ = min(τ, τU)/16`);
`pathBounds_of_forall_highProbAtBA`. -/
private theorem GUEPathBoundsBA_main (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (hlam : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹)
    (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hell1 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1)
    (hellg : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t)
    (hLK : STLKgL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1)
    (hLoc : STLocalEntrygL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1) :
    GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz n0) n0 Kt := by
  classical
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hadm.2.2.1
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 hadm.2.1
  have hm : ∀ n, 0 < (m n).im := fun n => (hr n).1.1
  have hm1 : ∀ n, ‖m n‖ ≤ 1 := fun n => BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) (hr n).1
  /- Deterministic facts on `η = etaOf (m n)` (the side conditions of the bootstraps). -/
  have hη : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), 0 < etaOf (m n) t := fun n t ht => by
    unfold etaOf; exact mul_pos (by linarith [ht.2, ht0 n]) (hm n)
  have hanti : ∀ n, ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ t ∈ Set.Icc (t1 n) (t0 n), u ≤ t →
      etaOf (m n) t ≤ etaOf (m n) u := fun n u _ t _ hut => by
    unfold etaOf
    exact mul_le_mul_of_nonneg_right (by linarith) (hm n).le
  have hηc : ∀ n, ContinuousOn (etaOf (m n)) (Set.Icc (t1 n) (t0 n)) := fun n => by
    unfold etaOf
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
      t - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) t := by
    filter_upwards [h730] with n hN t ht
    have h1 := hanti n t ht (t0 n) (ht0mem n) ht.2
    calc t - t1 n ≤ t0 n - t1 n := by linarith [ht.2]
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n) := hN
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) t :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hscale' : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := by
    filter_upwards [hscale] with n hN t ht
    refine le_trans ?_ hN
    have h0 := hη n (t0 n) (ht0mem n)
    have h1 := hanti n t ht (t0 n) (ht0mem n) ht.2
    exact inv_anti₀ (mul_pos (hNpos n) h0) (mul_le_mul_of_nonneg_left h1 (hNpos n).le)
  /- The bootstraps: `eq727GEAt` at `2 n₀`, then `eq728GAt`. -/
  have h727 := eq727GEAt (Pgue (sz.withLam 0)) sz.size hsz (n0 := 2 * n0) (even_two_mul n0)
    (fun n => ((sz.size n : ℕ) : ℝ)) (fun n => etaOf (m n)) t1 t0
    (fun n l t ω => gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n l t ω)
    (fun n l t ω => gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l t ω)
    (fun n l t => gueKproc sz t1 t0 (gueGridK sz n0) Kt n l t)
    hNpos ht10 hη hanti hηc hτU h730' hscale'
    (fun n l t ω => gueLprocBA_nonneg sz g E t1 t0 m _ _ n l t ω)
    (fun n l t ω => gueDprocBA_nonneg sz g E t1 t0 m _ _ Kt n l t ω)
    (fun n ω l _ t _ => gueLprocBA_le sz g E t1 t0 m _ _ Kt n l t ω)
    (fun n ω l _ t _ => gueDprocBA_le sz g E t1 t0 m _ _ Kt n l t ω)
    (fun n ω l hl _ t _ => gueLprocBA_odd sz g E t1 t0 m _ _ n l hl t ω)
    (fun ε hε => (gueKproc_detDomBA hd sz hκ hΛ hτU n0 hr hlam ht1 ht10 ht0 hsz h730 hellg Kt hKinit hK
      ε hε).mono fun n hn u => hn u.1 u.2)
    (perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun n ω _ l _ _ => gueLprocBA_continuousOn sz g E t1 t0 m _ _ n l ω))
    (gueBds_h745EBA sz hd hadm hκ hτU n0 hn0 hr hlam ht1 ht10 ht0 h730 hscale hell hellg Kt hKinit hK hLK)
  have h728 := eq728GAt (Pgue (sz.withLam 0)) sz.size hsz (n0 := n0)
    (fun n => ((sz.size n : ℕ) : ℝ)) (fun n => etaOf (m n)) t1 t0
    (fun n l t ω => gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n l t ω)
    (fun n l t ω => gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l t ω)
    hNpos ht10 hη hanti hηc hτU h730' hscale'
    (fun n l t ω => gueLprocBA_nonneg sz g E t1 t0 m _ _ n l t ω)
    (fun n l t ω => gueDprocBA_nonneg sz g E t1 t0 m _ _ Kt n l t ω) h727
    (perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun n ω _ l _ => gueDprocBA_continuousOn sz g E t1 t0 m _ _ Kt n l ω))
    (gueBds_h746BA sz hd hadm hκ hτU n0 hn0 hr hlam ht1 ht10 ht0 h730 hscale hell hellg Kt hKinit hK hLK)
  /- The other random inputs: the entry bound with `δ = N^{-τU/4}`, the step-`0` local law, truncation. -/
  have hD4 := gueGrid_entry_boundBA' sz hd hadm hκ n0 hr hlam ht1 ht10 ht0 (δ := gueDelta sz τU)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := τU / 4) (by positivity)
    (Eventually.of_forall fun n => le_of_eq rfl)
  have hinit := GUEPathBoundsBA_init_local sz t0 (gueGridK sz n0) hsz hr ht10 ht0 hell hLoc
  /- Unfreezing and conclusion on the intersection of the good events. -/
  have hmain : ∀ τ : ℝ, 0 < τ → HighProbAt (Pgue (sz.withLam 0)) sz.size
      (fun n => {ω : PathΩ (sz.withLam 0) | BoundsBA_Concl sz g E t1 t0 m n0 Kt τ n ω}) := by
    intro τ hτ
    set τ₁ : ℝ := min τ τU / 16 with hτ₁
    have hτ₁0 : 0 < τ₁ := by have := lt_min hτ hτU; positivity
    have hτ₁τ : τ₁ < τ := by have := min_le_left τ τU; have := lt_min hτ hτU; linarith
    have hneg : 2 * τ₁ - τU / 2 < 0 := by have := min_le_right τ τU; linarith
    have hev := perTimeCalc_highProbAt_inter hsz
      (perTimeCalc_highProbAt_inter hsz
        (perTimeCalc_highProbAt_inter hsz
          (perTimeCalc_highProbAt_inter hsz
            (perTimeCalc_highProbAt_of_stochDomAt h727 hτ₁0)
            (perTimeCalc_highProbAt_of_stochDomAt h728 hτ₁0))
          (perTimeCalc_highProbAt_mono (perTimeCalc_highProbAt_of_stochDomAt hD4 hτ₁0)
            (Eventually.of_forall fun _ _ hω k i j => hω (k, (i, j)))))
        (perTimeCalc_highProbAt_mono (perTimeCalc_highProbAt_of_stochDomAt hinit hτ₁0)
          (Eventually.of_forall fun _ _ hω i j => hω (i, j))))
      (gue_highProb_incr_le (sz.withLam 0) n0 hsz)
    refine perTimeCalc_highProbAt_mono hev ?_
    filter_upwards [hscale', hell1,
      hsz.eventually (eventually_rpow_le_of_neg hneg (by norm_num : (0 : ℝ) < 1 / 32)),
      hsz.eventually (eventually_le_rpow 2 (sub_pos.2 hτ₁τ))]
      with n hscN hellN hsmallN h4N
    rintro ω ⟨⟨⟨⟨hA, hBω⟩, hC⟩, hD⟩, hFω⟩
    exact Bounds_pathBA sz n0 hn0 Kt n hτU (hm n) (hm1 n) (ht1 n) (ht10 n) (ht0 n) hτ₁0 hτ₁τ hscN hellN
      hsmallN h4N ω hA hBω hC hD hFω
  exact pathBounds_of_forall_highProbAtBA sz g E t1 t0 m n0 Kt hmain

/-- **`gueGrid_pathBoundsBA`: the output of the random layer of [YY_25, §7.2] on the BA grid** (the analogue of `gueGrid_pathBounds`,
at `n₀ = 4`): under the hypotheses of the theorem the BA grid path `gueHBA` (`g Ψ_I + H_k`)
satisfies `GUEPathBoundsBA` on the grid `gueGridK sz 4`: (7.28) at every grid time `k ≤ K n` for `1 ≤ l ≤ 4` against the primitive
family `Kt`, and `‖G̃ - M‖_max ≺ (N η_u)^{-1/2}` against `M = Mres (g Ψ_I) E m`, `η_u = (1 - u) Im m`.  Flow datum `(g, E, m)`:
`BAReal` at every `n`, the window `0 < g n ≤ 𝔡⁻¹` eventually.  The step-`0` inputs `hLK`, `hLoc` are the first two
conjuncts of `BAMO` (`STLKgL`, `STLocalEntrygL` on the BA carrier at `(g, E)`); the K-family is `BAKFam`'s clauses (`hKinit`, `hK`,
guarded by `0 < g n`); `hell`, `hell1` are the zero-mode premises of `RBG_Prod` and `hellg : L^d (1 - t₁) ≤ 2 g²` the form the
K-lemmas of `BA/GUEHypABA` take (`GUEHypABA_hell_of_hell` at `g = √t₀ lam`). -/
theorem gueGrid_pathBoundsBA (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (hlam : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ 𝔡⁻¹)
    (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hell1 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1)
    (hellg : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * 4 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t)
    (hLK : STLKgL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1)
    (hLoc : STLocalEntrygL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1) :
    GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz 4) 4 Kt :=
  GUEPathBoundsBA_main sz hd hadm hκ hτU 4 (by norm_num) hr hlam ht1 ht10 ht0 h730 hscale hell hell1 hellg Kt hKinit hK
    hLK hLoc

end PathBoundsBAMain


end RBM.BA

end
