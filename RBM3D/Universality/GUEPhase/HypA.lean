/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Proc
import RBM3D.Universality.GUEPhase.EntryTailMain
import RBM3D.Loop.KBound
import RBM3D.Loop.KLFinal

/-!
# (7.45)G and (7.46)G for the stopped GUE-phase processes, part I: the deterministic inputs
(`d ≥ 3`; T2352, UN-48)

Port of RBM2D `Universality/GUEPhase/HypA.lean` (1010 lines, `9e0f275`).  The real-analysis
helpers, the loop-level helpers, the deterministic `K̃` and the discrete Duhamel formula on the
grid.  The pathwise assembly (`HypB.lean`, UN-49) is written against the public declarations below.

Proof idea.  On the good event, pathwise, the discrete Duhamel formula `Hyp_grid` holds at every
grid time `k ≤ σ*` (`σ* = gueStop`) with the initial term `h0`, the martingale remainder
`hM`/`hq`, the drift terms `hF` (bilinear, `primRhsGUE_sub`, `norm_primBilGUE_le`), `heG`
(`norm_egtNGUE_le`) and the deterministic discretization error of `K̃` (`Hyp_Kt_disc`); off the
grid the exact linear interpolation of the affine prefactor `u_k - t₁` and the concavity of `√·`
(`Hyp_interp_bound`).

## Contents

* `Hyp_step_nonneg`, `Hyp_time_ge`, `Hyp_time_le`, `Hyp_time_mem`: grid-time facts;
  `Hyp_interp_bound`: interpolation of a grid bound;
* `Hyp_exists_loopOf`, `Hyp_eps_le_dev`, `Hyp_trace_eq_gloop_one`, `Hyp_cutGlue_le`: loop-level
  helpers;
* `Hyp_Kt_detDom`, `Hyp_Kt_one`, `Hyp_Kt_disc`: the deterministic `K̃` (the bound (7.36) at every
  `t ∈ [t₁, t₀]`, the one-loop value, the discretization error);
* `Hyp_grid`: the discrete Duhamel formula;
* `HypAInst`: compiled nonempty instances of every target.

## Port map (`d = 2` to `d ≥ 3`; the renaming of the merged `Proc.lean`, `Bootstrap.lean`)

`d : Sizes` becomes `sz : Sizes d`; `Z2 L` becomes `Zd d L`; `BlockIndex L W` becomes `Vtx d L W`;
`Idx L W` becomes `Idx d L W`; `spectralZ`/`spectralM` become `zt`/`mE`; `Gsig` becomes `Gres`;
`gloop L W (blockMat M)` becomes `loopL d L W (blockMat d L W M)`; `RBM.Ind.LLf L W E u M` becomes
`loopL d L W (blockMat d L W M) (zt E u)`; `RBM.Ind.loopMax L W` becomes `RBM.Ind.loopMax d L W`;
`KLoop.mSig` becomes `mSigma`; `((W:ℂ)⁻¹)^2` (the weight of `E_a`) becomes `((W:ℂ)^d)⁻¹`;
`N = (W L)^2` becomes `N = (W L)^d = sz.size n`.  The sites of a block number `W^d`
(`Eblk = W^{-d}` on a block, `Hierarchy/ContractionBasic.lean:52` `trace_mul_Eblk`), the
one-step constant `3 M⁶ N² (v - u)²` of `Hyp_Kt_disc` has no `d` besides `N`.

The one departure (DECISIONS §141, as the merged `ProcK.lean`): RBM2D's `Proc_initial` uses
`KLoop.Kbound_prec_uncond` and the scale conversion `kloop_Mt_eq`, `ellT_eq_L`, which have no RBM3D
twin.  At `d ≥ 3` the initial values of `K̃` at `t₁` are the band K-loops `STKloop`
(`hKinit`), their bound is the pin `sz.STKbound E` (`hKb`), and the conversion
`Bctl ≤ 2 (N η_{t₁})⁻¹` needs `L^d (1 - t₁) ≤ ilambda²` (`hell`, the zero-mode regime; the
`d = 2` hypothesis `L² (1 - t₁) ≤ 1` is the case `ilambda = 1`).  It affects `Hyp_Kt_detDom` and
`Hyp_Kt_one` (the `hKinit` form).  The helpers carry the prefix `Hyp_` and are `private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)
/-! ### Real-analysis helpers -/

section HypReal

/-- Concavity of `√·` on two points. -/
private theorem Hyp_sqrt_convex {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (1 - θ) * Real.sqrt a + θ * Real.sqrt b ≤ Real.sqrt ((1 - θ) * a + θ * b) := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have h0a := Real.sqrt_nonneg a
  have h0b := Real.sqrt_nonneg b
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have hkey : 0 ≤ θ * (1 - θ) * (Real.sqrt a - Real.sqrt b) ^ 2 :=
    mul_nonneg (mul_nonneg hθ0 (by linarith)) (sq_nonneg _)
  nlinarith [hkey]

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

theorem Hyp_step_nonneg (ht10 : t1 n ≤ t0 n) : 0 ≤ gridStep t1 t0 K n :=
  div_nonneg (by linarith) (Nat.cast_nonneg _)

private theorem Hyp_time_mono (ht10 : t1 n ≤ t0 n) {i j : ℕ} (hij : i ≤ j) :
    gridTime t1 t0 K n i ≤ gridTime t1 t0 K n j := by
  unfold gridTime
  have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  nlinarith [Hyp_step_nonneg (K := K) ht10]

private theorem Hyp_time_sub (k : ℕ) :
    gridTime t1 t0 K n k - t1 n = (k : ℝ) * gridStep t1 t0 K n := by
  unfold gridTime; ring

private theorem Hyp_time_zero : gridTime t1 t0 K n 0 = t1 n := by
  unfold gridTime; simp

theorem Hyp_time_ge (ht10 : t1 n ≤ t0 n) (k : ℕ) : t1 n ≤ gridTime t1 t0 K n k := by
  have := Hyp_time_mono (K := K) ht10 (Nat.zero_le k)
  rwa [Hyp_time_zero] at this

theorem Hyp_time_le (ht10 : t1 n ≤ t0 n) (hK : K n ≠ 0) {k : ℕ} (hk : k ≤ K n) :
    gridTime t1 t0 K n k ≤ t0 n := by
  have := Hyp_time_mono (K := K) ht10 hk
  rwa [gridTime_last t1 t0 K n hK] at this

theorem Hyp_time_mem (ht10 : t1 n ≤ t0 n) (hK : K n ≠ 0) {k : ℕ} (hk : k ≤ K n) :
    gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n) :=
  ⟨Hyp_time_ge ht10 k, Hyp_time_le ht10 hK hk⟩

/-- The tent weights at a point of `[u_k, u_{k+1}]`. -/
private theorem Hyp_tent_eq (hΔ : 0 < gridStep t1 t0 K n) {k : ℕ} {t : ℝ}
    (h1 : gridTime t1 t0 K n k ≤ t) (h2 : t ≤ gridTime t1 t0 K n (k + 1)) (j : ℕ) :
    gueTent t1 t0 K n j t =
      if j = k then 1 - (t - gridTime t1 t0 K n k) / gridStep t1 t0 K n
      else if j = k + 1 then (t - gridTime t1 t0 K n k) / gridStep t1 t0 K n else 0 := by
  set Δ := gridStep t1 t0 K n with hΔdef
  set θ := (t - gridTime t1 t0 K n k) / Δ with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hΔ.le
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hΔ]
    have : gridTime t1 t0 K n (k + 1) = gridTime t1 t0 K n k + Δ := by
      unfold gridTime; push_cast; ring
    linarith
  have hval : (t - gridTime t1 t0 K n j) / Δ = θ + ((k : ℝ) - (j : ℝ)) := by
    rw [hθdef]; unfold gridTime; rw [← hΔdef]; field_simp; ring
  have habs : |t - gridTime t1 t0 K n j| / Δ = |θ + ((k : ℝ) - (j : ℝ))| := by
    rw [← hval, abs_div, abs_of_pos hΔ]
  change max 0 (1 - |t - gridTime t1 t0 K n j| / Δ) = _
  rw [habs]
  by_cases hjk : j = k
  · subst hjk
    simp only [sub_self, add_zero, ite_true, abs_of_nonneg hθ0]
    exact max_eq_right (by linarith)
  · by_cases hjk1 : j = k + 1
    · subst hjk1
      simp only [hjk, ite_false, ite_true]
      push_cast
      rw [show θ + ((k : ℝ) - ((k : ℝ) + 1)) = θ - 1 by ring, abs_of_nonpos (by linarith)]
      rw [max_eq_right (by linarith)]
      ring
    · simp only [hjk, hjk1, ite_false]
      apply max_eq_left
      rcases Nat.lt_or_gt_of_ne hjk with hlt | hgt
      · have : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (k : ℝ) + 2 ≤ (j : ℝ) := by
          have : k + 2 ≤ j := by omega
          exact_mod_cast this
        rw [abs_of_nonpos (by linarith)]; linarith

/-- On `[u_k, u_{k+1}]`, `k < K`, the interpolation is `(1-θ) f_k + θ f_{k+1}`. -/
private theorem Hyp_interp_eq (f : ℕ → ℝ) (hΔ : 0 < gridStep t1 t0 K n) {k : ℕ}
    (hk : k < K n) {t : ℝ} (h1 : gridTime t1 t0 K n k ≤ t)
    (h2 : t ≤ gridTime t1 t0 K n (k + 1)) :
    gueInterp t1 t0 K n f t =
      (1 - (t - gridTime t1 t0 K n k) / gridStep t1 t0 K n) * f k +
        (t - gridTime t1 t0 K n k) / gridStep t1 t0 K n * f (k + 1) := by
  unfold gueInterp
  simp only [hΔ.ne', ite_false]
  simp_rw [Hyp_tent_eq hΔ h1 h2]
  rw [Finset.sum_eq_add_of_mem k (k + 1) (Finset.mem_range.2 (by omega))
    (Finset.mem_range.2 (by omega)) (by omega)]
  · simp only [ite_true, show k + 1 ≠ k by omega, ite_false]
    ring
  · intro c _ hc
    simp [hc.1, hc.2]

/-- For `t ∈ [t₁, t₀]` and `Δ > 0` there is a grid cell `[u_k, u_{k+1}]`, `k < K`, containing
`t`. -/
private theorem Hyp_exists_cell (hΔ : 0 < gridStep t1 t0 K n) (hK : K n ≠ 0) {t : ℝ}
    (ht : t ∈ Set.Icc (t1 n) (t0 n)) :
    ∃ k : ℕ, k < K n ∧ gridTime t1 t0 K n k ≤ t ∧ t ≤ gridTime t1 t0 K n (k + 1) := by
  set Δ := gridStep t1 t0 K n with hΔdef
  set s := (t - t1 n) / Δ with hsdef
  have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) hΔ.le
  have hts : t = t1 n + s * Δ := by rw [hsdef]; field_simp; ring
  refine ⟨min ⌊s⌋₊ (K n - 1), by omega, ?_, ?_⟩
  · have h1 : ((min ⌊s⌋₊ (K n - 1) : ℕ) : ℝ) ≤ s :=
      le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le hs0)
    unfold gridTime
    rw [← hΔdef]
    nlinarith
  · by_cases hc : ⌊s⌋₊ ≤ K n - 1
    · rw [min_eq_left hc]
      have h2 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
      unfold gridTime
      rw [← hΔdef]
      push_cast
      nlinarith
    · rw [min_eq_right (by omega), show K n - 1 + 1 = K n by omega,
        gridTime_last t1 t0 K n hK]
      exact ht.2

/-- **Interpolation of a grid bound with an affine and a square-root prefactor.** If the grid
values `f k`, `k ≤ σ`, obey `f k ≤ P + Q λ(u_k) + A (u_k - t₁) + B √(u_k - t₁)` whenever all
earlier grid times are `≤ t`, then the stopped interpolant at `t` obeys the same bound with
`u_k` replaced by `t` (and `λ(u_k)` by `C λ(t)`). -/
theorem Hyp_interp_bound (f : ℕ → ℝ) {σ : ℕ} (hσ : σ ≤ K n) (hK : K n ≠ 0)
    (ht10 : t1 n ≤ t0 n) {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) (lam : ℝ → ℝ)
    {P Q A B C : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlam : ∀ k ≤ K n, gridTime t1 t0 K n k ≤ t + gridStep t1 t0 K n →
      lam (gridTime t1 t0 K n k) ≤ C * lam t)
    (hgrid : ∀ k ≤ σ, (∀ j < k, gridTime t1 t0 K n j ≤ t) →
      f k ≤ P + Q * lam (gridTime t1 t0 K n k) + A * (gridTime t1 t0 K n k - t1 n)
        + B * Real.sqrt (gridTime t1 t0 K n k - t1 n)) :
    gueInterp t1 t0 K n (fun k => f (min k σ)) t ≤
      P + Q * (C * lam t) + A * (t - t1 n) + B * Real.sqrt (t - t1 n) := by
  have hΔ0 := Hyp_step_nonneg (K := K) ht10
  rcases hΔ0.lt_or_eq with hΔ | hΔ
  · obtain ⟨k, hkK, hk1, hk2⟩ := Hyp_exists_cell hΔ hK ht
    rw [Hyp_interp_eq _ hΔ hkK hk1 hk2]
    set Δ := gridStep t1 t0 K n with hΔdef
    set θ := (t - gridTime t1 t0 K n k) / Δ with hθdef
    have hsucc : gridTime t1 t0 K n (k + 1) = gridTime t1 t0 K n k + Δ := by
      unfold gridTime; rw [← hΔdef]; push_cast; ring
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hΔ.le
    have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hΔ]; linarith
    have hge := Hyp_time_ge (K := K) ht10 k
    by_cases hσk : σ ≤ k
    · simp only [min_eq_right hσk, min_eq_right (le_trans hσk (Nat.le_succ k))]
      have hσt : gridTime t1 t0 K n σ ≤ t := le_trans (Hyp_time_mono ht10 hσk) hk1
      have hf := hgrid σ le_rfl fun j hj =>
        le_trans (Hyp_time_mono ht10 (le_of_lt (lt_of_lt_of_le hj hσk))) hk1
      have hl := hlam σ hσ (by linarith)
      have hgeσ := Hyp_time_ge (K := K) ht10 σ
      have hsq : Real.sqrt (gridTime t1 t0 K n σ - t1 n) ≤ Real.sqrt (t - t1 n) :=
        Real.sqrt_le_sqrt (by linarith)
      have e1 : Q * lam (gridTime t1 t0 K n σ) ≤ Q * (C * lam t) :=
        mul_le_mul_of_nonneg_left hl hQ
      have e2 : A * (gridTime t1 t0 K n σ - t1 n) ≤ A * (t - t1 n) :=
        mul_le_mul_of_nonneg_left (by linarith) hA
      have e3 := mul_le_mul_of_nonneg_left hsq hB
      linarith
    · push Not at hσk
      simp only [min_eq_left hσk.le, min_eq_left (Nat.succ_le_of_lt hσk)]
      have hfk := hgrid k hσk.le fun j hj => le_trans (Hyp_time_mono ht10 hj.le) hk1
      have hfk1 := hgrid (k + 1) (Nat.succ_le_of_lt hσk) fun j hj =>
        le_trans (Hyp_time_mono ht10 (Nat.lt_succ_iff.1 hj)) hk1
      have hlk := hlam k hkK.le (by linarith)
      have hlk1 := hlam (k + 1) hkK (by linarith)
      have hsq := Hyp_sqrt_convex (a := gridTime t1 t0 K n k - t1 n)
        (b := gridTime t1 t0 K n (k + 1) - t1 n) (by linarith) (by linarith) hθ0 hθ1
      have hθΔ : θ * Δ = t - gridTime t1 t0 K n k := by rw [hθdef]; field_simp
      have haff : (1 - θ) * (gridTime t1 t0 K n k - t1 n) +
          θ * (gridTime t1 t0 K n (k + 1) - t1 n) = t - t1 n := by
        rw [hsucc]; linear_combination hθΔ
      rw [haff] at hsq
      have h1θ : 0 ≤ 1 - θ := by linarith
      have a1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlk hQ) h1θ
      have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlk1 hQ) hθ0
      have eS := mul_le_mul_of_nonneg_left hsq hB
      have c1 := mul_le_mul_of_nonneg_left hfk h1θ
      have c2 := mul_le_mul_of_nonneg_left hfk1 hθ0
      have eA : (1 - θ) * (A * (gridTime t1 t0 K n k - t1 n)) +
          θ * (A * (gridTime t1 t0 K n (k + 1) - t1 n)) = A * (t - t1 n) := by
        rw [← haff]; ring
      have eB : (1 - θ) * (B * Real.sqrt (gridTime t1 t0 K n k - t1 n)) +
          θ * (B * Real.sqrt (gridTime t1 t0 K n (k + 1) - t1 n)) =
          B * ((1 - θ) * Real.sqrt (gridTime t1 t0 K n k - t1 n) +
            θ * Real.sqrt (gridTime t1 t0 K n (k + 1) - t1 n)) := by ring
      have eQ : (1 - θ) * (Q * (C * lam t)) + θ * (Q * (C * lam t)) = Q * (C * lam t) := by ring
      have eP : (1 - θ) * P + θ * P = P := by ring
      nlinarith
  · -- `Δ = 0`: the interval is a point
    have hstep0 : gridStep t1 t0 K n = 0 := hΔ.symm
    have ht10' : t0 n = t1 n := by
      have hKR : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
      have := hstep0
      unfold gridStep at this
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · linarith
      · exact absurd h hKR
    have htt1 : t = t1 n := le_antisymm (ht10' ▸ ht.2) ht.1
    unfold gueInterp
    simp only [hstep0, ite_true, Nat.zero_min]
    have hf := hgrid 0 (Nat.zero_le _) fun j hj => absurd hj (Nat.not_lt_zero j)
    have hl := hlam 0 (Nat.zero_le _) (by rw [Hyp_time_zero, hstep0, htt1]; linarith)
    rw [Hyp_time_zero, sub_self, Real.sqrt_zero, mul_zero, mul_zero, add_zero,
      add_zero] at hf
    rw [Hyp_time_zero] at hl
    rw [htt1, sub_self, Real.sqrt_zero, mul_zero, mul_zero, add_zero, add_zero]
    rw [htt1] at hl
    nlinarith [mul_le_mul_of_nonneg_left hl hQ]

end HypReal

/-! ### Loop-level helpers -/

section HypLoop

/-- Every well-formed loop index is `loopOf` of a sign vector and a label vector. -/
theorem Hyp_exists_loopOf {d L : ℕ} [NeZero L] (J : RBM.Loop.LoopIdx (Zd d L)) (hJ : J.WF) :
    ∃ x : (Fin J.length → Bool) × (Fin J.length → Zd d L), loopOf x.1 x.2 = J := by
  obtain ⟨σ, a⟩ := J
  simp only [RBM.Loop.LoopIdx.WF] at hJ
  simp only [RBM.Loop.LoopIdx.length]
  refine ⟨(fun i => σ.get (Fin.cast hJ.symm i), fun i => a.get i), ?_⟩
  have hσ' : List.ofFn (fun i : Fin a.length => σ.get (Fin.cast hJ.symm i)) = σ := by
    apply List.ext_get <;> simp [hJ]
  have ha' : List.ofFn (fun i : Fin a.length => a.get i) = a := List.ofFn_get a
  simp only [loopOf, hσ', ha']

/-- `|⟨M E_a⟩| ≤ max_p |M_{pp}|` (`d ≥ 3`: the block has `W^d` sites, each of weight `W^{-d}`;
through the merged `trace_mul_Eblk`, `Hierarchy/ContractionBasic.lean:52`; RBM2D
`Hyp_norm_trace_Eblk_le` `:329`). -/
private theorem Hyp_norm_trace_Eblk_le {d L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) {c : ℝ}
    (hc : ∀ p, ‖M p p‖ ≤ c) : ‖Matrix.trace (M * Eblk d L W a)‖ ≤ c := by
  have hW0 : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have hc0 : 0 ≤ c :=
    (norm_nonneg _).trans (hc (a, (⟨0, pow_pos hW0 d⟩ : Fin (W ^ d))))
  rw [trace_mul_Eblk, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((W : ℝ) ^ d)⁻¹ * ‖∑ α : Fin (W ^ d), M (a, α) (a, α)‖
      ≤ ((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), c :=
        mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => hc (a, α)))
          (inv_nonneg.2 hWd.le)
    _ = c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp

/-- `Gres H z σ` has the conjugate transpose `Gres H z (!σ)` for Hermitian `H` (private twin of
the merged private `Gres_conjTranspose`, `Induction/Split.lean:250`; RBM2D `Gsig_conjTranspose`
`Hierarchy/Loops.lean:68`). -/
private theorem Hyp_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

/-- **`ε ≤ ‖G - m‖_max`**: the `E^{(G)}` weight `avgErr = ⟨(G_σ - m_σ) E_a⟩` is a block average of
the diagonal of `G - m` (for `σ = -`, of its complex conjugate); stated on the fine lattice
`Idx d L W` (the entries of `gueDev`) and reindexed by `mixEntry_greenBlk_eq`. -/
theorem Hyp_eps_le_dev {d L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (E u : ℝ) {c : ℝ}
    (hc : ∀ i : Idx d L W,
      ‖(green M (zt E u) - mE E • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) i i‖ ≤ c)
    (σ : Bool) (a : Zd d L) : ‖RBM.Green.avgErr d L W E u M σ a‖ ≤ c := by
  unfold RBM.Green.avgErr
  refine Hyp_norm_trace_Eblk_le _ a fun p => ?_
  have hblk : RBM.Green.greenBlk d L W E u M true =
      (green M (zt E u)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm :=
    mixEntry_greenBlk_eq E u M
  have hentry : ‖(RBM.Green.greenBlk d L W E u M true - mSigma E true •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p p‖ ≤ c := by
    have h := hc ((splitEquiv d L W).symm p)
    rw [hblk]
    simpa [mSigma, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.one_apply] using h
  cases σ
  · have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
    have hconj : RBM.Green.greenBlk d L W E u M false = (RBM.Green.greenBlk d L W E u M true)ᴴ :=
      (Hyp_Gres_conjTranspose hH (zt E u) true).symm
    have e : (RBM.Green.greenBlk d L W E u M false - mSigma E false •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p p =
        star ((RBM.Green.greenBlk d L W E u M true - mSigma E true •
          (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p p) := by
      rw [hconj]
      simp [mSigma, Matrix.sub_apply, Matrix.conjTranspose_apply]
    rw [e, norm_star]
    exact hentry
  · exact hentry

/-- `⟨(G_σ - m_σ) E_a⟩ = L_{(σ),(a)} - m_σ`. -/
theorem Hyp_trace_eq_gloop_one {d L W : ℕ} [NeZero L] [NeZero W]
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (m : Bool → ℂ) (σ : Bool)
    (a : Zd d L) :
    Matrix.trace ((Gres H z σ - m σ •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Eblk d L W a) =
      loopL d L W H z ⟨[σ], [a]⟩ - m σ := by
  have hg : loopL d L W H z ⟨[σ], [a]⟩ = Matrix.trace (Gres H z σ * Eblk d L W a) := by
    simp [loopL]
  rw [hg, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, trace_Eblk, smul_eq_mul, mul_one]

/-- The operation `cutGlue` adds exactly one Green edge (private twin of
`Path/OneStep.lean:318`; RBM2D `LoopIdx.length_cutGlue`, `Hierarchy/Operations.lean:48`). -/
private theorem Hyp_length_cutGlue {α : Type*} (I : RBM.Loop.LoopIdx α) (b : α) {k : ℕ}
    (hk : k ≤ I.length) : (I.cutGlue k b).length = I.length + 1 := by
  simp only [RBM.Loop.LoopIdx.length, RBM.Loop.LoopIdx.cutGlue, List.length_append,
    List.length_take, List.length_cons, List.length_drop] at hk ⊢
  omega

/-- A valid one-based cut preserves well-formedness (private twin of `Path/OneStep.lean:325`;
RBM2D `LoopIdx.WF.cutGlue`, `Hierarchy/Operations.lean:56`). -/
private theorem Hyp_wf_cutGlue {α : Type*} {I : RBM.Loop.LoopIdx α} (hI : I.WF) (b : α) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ I.length) : (I.cutGlue k b).WF := by
  simp only [RBM.Loop.LoopIdx.WF, RBM.Loop.LoopIdx.length, RBM.Loop.LoopIdx.cutGlue,
    List.length_append, List.length_take, List.length_cons, List.length_drop] at hI hk ⊢
  omega

/-- An `(n+1)`-loop obtained by cutting and gluing is bounded by `L^{(n+1)}`. -/
theorem Hyp_cutGlue_le {d L W : ℕ} [NeZero L]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} {I : RBM.Loop.LoopIdx (Zd d L)}
    (hI : I.WF) {k : ℕ} (hk : k ∈ Finset.Icc 1 I.length) (b : Zd d L) :
    ‖loopL d L W H z (I.cutGlue k b)‖ ≤ RBM.Ind.loopMax d L W H z (I.length + 1) := by
  rw [Finset.mem_Icc] at hk
  have hwf := Hyp_wf_cutGlue hI b hk.1 hk.2
  have hlen := Hyp_length_cutGlue I b hk.2
  exact RBM.Ind.norm_gloop_le_loopMax _ (by rw [hwf]; exact hlen) hlen

end HypLoop

/-! ### The deterministic `K̃` -/

section HypKt

private theorem Hyp_size_pos (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.size n := by
    unfold Sizes.size
    have hW := sz.W_pos n
    have hL := sz.three_le_L n
    positivity
  exact_mod_cast h1


private theorem Hyp_etaT_anti (e : ℝ) {u t : ℝ} (hut : u ≤ t) : etaT e t ≤ etaT e u := by
  unfold etaT
  have h2 : 0 ≤ (mE e).im := by rw [mE_im]; positivity
  nlinarith

private theorem Hyp_im_le_one (e : ℝ) : (mE e).im ≤ 1 := by
  rw [mE_im]
  have : Real.sqrt (4 - e ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg e]⟩
  linarith

private theorem Hyp_gueScale_pos {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ)
    (n : ℕ) {t : ℝ} (ht : t < 1) : 0 < gueScale sz E n t := by
  have h2 : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  unfold gueScale
  exact mul_pos (Hyp_size_pos sz n) (etaT_pos h2 ht)

private theorem Hyp_ofFn_getD {α : Type*} (l : List α) (dflt : α) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i dflt) = l := by
  subst h
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp

/-- A well-formed loop is `loopOf` of its own signs and labels (RBM2D `Proc_loopOf_eq` `:1120`). -/
private theorem Hyp_loopOf_eq {d L : ℕ} [NeZero L] (J : RBM.Loop.LoopIdx (Zd d L)) (hJ : J.WF) :
    loopOf (fun i : Fin J.length => J.σ.getD i false)
      (fun i : Fin J.length => J.a.getD i (0 : Zd d L)) = J := by
  obtain ⟨σ', a'⟩ := J
  simp only [RBM.Loop.LoopIdx.WF] at hJ
  simp only [loopOf, RBM.Loop.LoopIdx.length]
  rw [Hyp_ofFn_getD σ' false a'.length hJ, Hyp_ofFn_getD a' 0 a'.length rfl]

/-- The deterministic content of `STKbound` at one time sequence `τ`: `≺` of a deterministic
quantity is a deterministic inequality (the bad event is `∅` or the whole space, and
`P(bad) ≤ N^{-1} < 1` once `N ≥ 2`; cf. the merged private `gdn_STKbound_win`). -/
private theorem Hyp_stKbound_eventually {E : ℕ → ℝ} (hKb : sz.STKbound E)
    (hsz : Tendsto sz.size atTop atTop) (τ : ℕ → ℝ) (hτ0 : ∀ n, 0 ≤ τ n) (hτ1 : ∀ n, τ n < 1)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖sz.STKloop n (E n) (τ n) σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (τ n)) ^ (k - 1) := by
  have hprec := hKb τ hτ0 hτ1 k hk ε hε 1 one_pos
  filter_upwards [hprec, hsz.eventually (eventually_ge_atTop 2)] with n hn2 hn3
  intro σ a
  by_contra hcon
  have hσa := not_le.1 hcon
  have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
    refine (measure_univ (μ := Sizes.seqP sz)).symm.le.trans ((measure_mono ?_).trans hn2)
    intro ω _
    exact ⟨(σ, a), hσa⟩
  have h2 := ENNReal.one_le_ofReal.1 h1
  rw [Real.rpow_neg_one] at h2
  have hn3' : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn3
  have h3 : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hn3'
  linarith [h3, show (2 : ℝ)⁻¹ < 1 by norm_num]

/-- **The conversion** `W^{-d} B_{t,0} ≤ 2 (N η_t)⁻¹` under the zero-mode condition
`L^d (1 - t) ≤ ilambda²` (`hell`): `(ilambda² + x)⁻¹ ≤ (L^d x)⁻¹`, so
`Bctl ≤ 2 W^{-d} (L^d x)⁻¹ = 2 (N x)⁻¹ ≤ 2 (N x Im m)⁻¹` (`Im m ≤ 1`). -/
private theorem Hyp_Bctl_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hell : ((sz.L n : ℕ) : ℝ) ^ d * (1 - t) ≤ sz.lam n ^ 2) :
    sz.Bctl n t ≤ 2 * (((sz.size n : ℕ) : ℝ) * etaT E t)⁻¹ := by
  have hx : 0 < 1 - t := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := Hyp_size_pos sz n
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have hηpos : 0 < etaT E t := etaT_pos hE ht
  have hηle : etaT E t ≤ 1 - t := by
    unfold etaT
    calc (1 - t) * (mE E).im ≤ (1 - t) * 1 :=
          mul_le_mul_of_nonneg_left (Hyp_im_le_one E) hx.le
      _ = 1 - t := mul_one _
  have h1 : (sz.lam n ^ 2 + (1 - t))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ :=
    inv_anti₀ (mul_pos hLd hx) (by nlinarith [sq_nonneg (sz.lam n)])
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ := le_rfl
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

/-- The initial data of `K̃` at `t₁`: `‖K̃_{t₁, I}‖ ≤ N^{τ'} (N η_{t₁})^{-|I|+1}` for loops of length
in `[2, 2 n₀]`, from `STKbound E` at the sequence `t₁` (`hKb`), the identification `hKinit` with
the band K-loop and the conversion `Hyp_Bctl_le` (`hell`); the `≺` is unfolded
(`Hyp_stKbound_eventually`), the finitely many lengths are intersected, and
`Tendsto sz.size atTop atTop` turns the `∀ᶠ` along `sz.size` into `∀ᶠ n`.  (RBM2D `Proc_initial`
`:1133`, from `Kbound_prec_uncond`.) -/
private theorem Hyp_initial {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop)
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ n : ℕ in atTop, ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length →
      I.length ≤ 2 * n0 →
      ‖Kt n (t1 n) I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1) := by
  have hall : ∀ᶠ n : ℕ in atTop, ∀ ℓ ∈ Finset.Icc 2 (2 * n0),
      ∀ (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d (sz.L n)),
        ‖sz.STKloop n (E n) (t1 n) σ a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * (sz.Bctl n (t1 n)) ^ (ℓ - 1) :=
    (Filter.eventually_all_finset _).2 fun ℓ hℓ =>
      Hyp_stKbound_eventually sz hKb hsz t1 ht1 (fun n => lt_of_le_of_lt (ht10 n) (ht0 n)) ℓ
        (by have := (Finset.mem_Icc.1 hℓ).1; omega) (half_pos hτ')
  have hpow : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (2 * n0) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) :=
    hsz.eventually (eventually_le_rpow ((2 : ℝ) ^ (2 * n0)) (half_pos hτ'))
  filter_upwards [hall, hpow, hell] with n hn hp hellN I hWF h2 h2n
  have ht1lt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hE2 : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  have hIlen : I.length ∈ Finset.Icc 2 (2 * n0) := Finset.mem_Icc.2 ⟨h2, h2n⟩
  have hb := hn I.length hIlen (fun i : Fin I.length => I.σ.getD i false)
    (fun i : Fin I.length => I.a.getD i (0 : Zd d (sz.L n)))
  rw [← hKinit n, Hyp_loopOf_eq I hWF] at hb
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := Hyp_size_pos sz n
  have hBle : sz.Bctl n (t1 n) ≤ 2 * (gueScale sz E n (t1 n))⁻¹ :=
    Hyp_Bctl_le sz n hE2 ht1lt hellN
  have hB0 : 0 ≤ sz.Bctl n (t1 n) := by
    have hx : 0 < 1 - t1 n := by linarith
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hx]
    positivity
  have hsc : 0 < gueScale sz E n (t1 n) := Hyp_gueScale_pos sz hE hκ n ht1lt
  have hinv1 : 1 ≤ ((gueScale sz E n (t1 n))⁻¹) ^ 0 := by simp
  have hpow2 : (sz.Bctl n (t1 n)) ^ (I.length - 1)
      ≤ (2 : ℝ) ^ (2 * n0) * (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1) := by
    calc (sz.Bctl n (t1 n)) ^ (I.length - 1)
        ≤ (2 * (gueScale sz E n (t1 n))⁻¹) ^ (I.length - 1) := pow_le_pow_left₀ hB0 hBle _
      _ = 2 ^ (I.length - 1) * (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1) := mul_pow _ _ _
      _ ≤ 2 ^ (2 * n0) * (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hNpow : ((sz.size n : ℕ) : ℝ) ^ τ'
      = ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hNn : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) := Real.rpow_nonneg hN0.le _
  have hinvnn : (0 : ℝ) ≤ (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1) := by positivity
  calc ‖Kt n (t1 n) I‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * (sz.Bctl n (t1 n)) ^ (I.length - 1) := hb
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
          ((2 : ℝ) ^ (2 * n0) * (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1)) :=
        mul_le_mul_of_nonneg_left hpow2 hNn
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) *
          (((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hinvnn) hNn
    _ = ((sz.size n : ℕ) : ℝ) ^ τ' * (gueScale sz E n (t1 n))⁻¹ ^ (I.length - 1) := by
        rw [hNpow]; ring

/-- (7.36) on the size scale: for every `τ > 0`, eventually in `n`, `‖K̃_{t,I}‖ ≤ N^τ (N η_t)^{-|I|+1}`
on `[t₁, t₀]` for loops of length in `[2, 2 n₀]`.  The scale-free `eq736` is applied at each `n`
with `A = N^{τ'}`, `ε = N^{-τ_U}`; the three index-scale thresholds (`eventually_small`,
`2 ≤ N^{τ-τ'}`, and the initial bound) are transferred along `sz.size`. -/
private theorem Hyp_hbase {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length →
      I.length ≤ 2 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      2 ≤ I.length → I.length ≤ 2 * n0 →
      ‖Kt n t I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n t)⁻¹ ^ (I.length - 1) := by
  set τ' := min τ τU / 2 with hτ'
  have hτ'0 : 0 < τ' := by have := lt_min hτ hτU; positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : τ' < τU := by have := min_le_right τ τU; linarith
  filter_upwards [Hyp_initial sz hκ n0 hE ht1 ht10 ht0 hsz hell hKb Kt hKinit hτ'0, h730,
    hsz.eventually (eventually_small (n := 2 * n0) hτ'U),
    hsz.eventually (eventually_le_rpow 2 (sub_pos.2 hτ'τ))] with n hinit h730n hε h2
  intro t ht I hWF h2I hIn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := Hyp_size_pos sz n
  have ht1lt : ∀ u ∈ Set.Icc (t1 n) (t0 n), u < 1 := fun u hu => lt_of_le_of_lt hu.2 (ht0 n)
  have hlam : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < gueScale sz E n u := fun u hu =>
    Hyp_gueScale_pos sz hE hκ n (ht1lt u hu)
  have hanti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ v ∈ Set.Icc (t1 n) (t0 n), u ≤ v →
      gueScale sz E n v ≤ gueScale sz E n u := by
    intro u _ v _ huv
    unfold gueScale
    exact mul_le_mul_of_nonneg_left (Hyp_etaT_anti (E n) huv) hN0.le
  have hlamc : ContinuousOn (gueScale sz E n) (Set.Icc (t1 n) (t0 n)) := by
    have heq : gueScale sz E n = fun t => ((sz.size n : ℕ) : ℝ) * ((1 - t) * (mE (E n)).im) :=
      rfl
    rw [heq]
    fun_prop
  have hA : 0 < ((sz.size n : ℕ) : ℝ) ^ τ' := Real.rpow_pos_of_pos hN0 _
  have hsmall : ∀ u ∈ Set.Icc (t1 n) (t0 n),
      (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) * (u - t1 n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * gueScale sz E n u := by
    intro u hu
    have h1 : u - t1 n ≤ t0 n - t1 n := by linarith [hu.2]
    have h2' : etaT (E n) (t0 n) ≤ etaT (E n) u := Hyp_etaT_anti (E n) hu.2
    have hNpow : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := Real.rpow_nonneg hN0.le _
    have h3 : u - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) u :=
      le_trans h1 (le_trans h730n (mul_le_mul_of_nonneg_left h2' hNpow))
    have e : (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) := rfl
    rw [e]
    unfold gueScale
    calc ((sz.size n : ℕ) : ℝ) * (u - t1 n)
        ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) u) :=
          mul_le_mul_of_nonneg_left h3 hN0.le
      _ = ((sz.size n : ℕ) : ℝ) ^ (-τU) * (((sz.size n : ℕ) : ℝ) * etaT (E n) u) := by ring
  have key := eq736 d (sz.L n) (sz.W n) (Kt n) (n := 2 * n0) (ht10 n) (gueScale sz E n) hlam hanti
    hlamc (hK n) hA (fun J hJ h2J hJn => hinit J hJ h2J hJn) hsmall hε t ht I hWF h2I hIn
  have hx : 0 ≤ (gueScale sz E n t)⁻¹ ^ (I.length - 1) :=
    pow_nonneg (inv_pos.2 (hlam t ht)).le _
  have hsplit : ((sz.size n : ℕ) : ℝ) ^ τ
      = ((sz.size n : ℕ) : ℝ) ^ (τ - τ') * ((sz.size n : ℕ) : ℝ) ^ τ' := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [hsplit]
  have : 2 * ((sz.size n : ℕ) : ℝ) ^ τ' * (gueScale sz E n t)⁻¹ ^ (I.length - 1)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - τ') * ((sz.size n : ℕ) : ℝ) ^ τ' *
        (gueScale sz E n t)⁻¹ ^ (I.length - 1) := by
    gcongr
  linarith

/-- `F = primRhsGUE` vanishes on loops of length `1`. -/
private theorem Hyp_primRhs_one {d L W : ℕ} [NeZero L] (K : RBM.Loop.LoopIdx (Zd d L) → ℂ)
    (I : RBM.Loop.LoopIdx (Zd d L)) (hI : I.length = 1) : primRhsGUE d L W K I = 0 := by
  unfold primRhsGUE primBilGUE
  rw [hI]
  simp

/-- **The bound (7.36) at every `t ∈ [t₁, t₀]`, deterministic**: `‖K̃_t(J)‖ ≺ (N η_t)^{-|J|+1}`,
uniformly in `t ∈ [t₁, t₀]` and the well-formed loops `2 ≤ |J| ≤ 2n₀`, in the explicit size-scale
form (`N = sz.size n = (W L)^d`).  This is the public form of the private `ProcK_hbase`
(`ProcK.lean`), without the interpolation; `hK` is required for `1 ≤ |I| ≤ 4n₀`, the statement is
the explicit `∀ ε > 0, ∀ᶠ n`, and `hsz`, `ht1` are hypotheses.  The departure from RBM2D (the
initial data `hKinit` at `STKloop`, the pin `hKb : sz.STKbound E`, `hell : L^d (1 - t₁) ≤ ilambda²`)
is the one of `gueKproc_detDom` (DECISIONS §141). -/
theorem Hyp_Kt_detDom {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hsz : Tendsto sz.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n),
      ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)),
      I.WF → 2 ≤ I.length → I.length ≤ 2 * n0 →
      ‖Kt n t I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (gueScale sz E n t)⁻¹ ^ (I.length - 1) :=
  fun _ hτ => Hyp_hbase sz hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hell hKb Kt hKinit
    (fun n t ht I hI h2 hlen => hK n t ht I hI (by omega) (by omega)) hτ

/-- At length `1`, `K̃_t = m_σ` on `[t₁, t₀]` (the primitive equation has zero right side). -/
theorem Hyp_Kt_one {E t1 t0 : ℕ → ℝ} (n0 : ℕ) (hn0 : 1 ≤ n0)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (t1 n) (t0 n)) (s : Bool) (a : Zd d (sz.L n)) :
    Kt n u ⟨[s], [a]⟩ = mSigma (E n) s := by
  have hI : (⟨[s], [a]⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n))).length = 1 := rfl
  have hWF : (⟨[s], [a]⟩ : RBM.Loop.LoopIdx (Zd d (sz.L n))).WF := rfl
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun r => Kt n r ⟨[s], [a]⟩)
    (f' := fun r => primRhsGUE d (sz.L n) (sz.W n) (Kt n r) ⟨[s], [a]⟩) (C := 0)
    (fun r hr => hK n r hr _ hWF (by rw [hI]) (by rw [hI]; omega))
    (fun r _ => by rw [Hyp_primRhs_one _ _ hI, norm_zero]) u hu
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hmvt
  have h1 := hKinit n (k := 1) (fun _ => s) (fun _ => a)
  have e : (loopOf (fun _ : Fin 1 => s) (fun _ : Fin 1 => a) :
      RBM.Loop.LoopIdx (Zd d (sz.L n))) = ⟨[s], [a]⟩ := by
    simp [loopOf]
  rw [e] at h1
  rw [hmvt, h1]
  change RBM.Loop.KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (t1 n)
    ⟨List.ofFn (fun _ : Fin 1 => s), List.ofFn (fun _ : Fin 1 => a)⟩ = mSigma (E n) s
  have e2 : (⟨List.ofFn (fun _ : Fin 1 => s), List.ofFn (fun _ : Fin 1 => a)⟩ :
      RBM.Loop.LoopIdx (Zd d (sz.L n))) = ⟨[s], [a]⟩ := by simp
  rw [e2]
  exact RBM.Loop.KLK_one d (sz.L n) (sz.lam n) (sz.W n) (E n) (t1 n) s a

/-- `n² S ∑_{j=2}^n x ≤ M³ S x` for `n ≤ M`, `x ≥ 0`. -/
private theorem Hyp_card_bound {n M : ℕ} (hnM : n ≤ M) {S x : ℝ} (hS : 0 ≤ S) (hx : 0 ≤ x) :
    (n : ℝ) ^ 2 * S * ∑ _j ∈ Finset.Icc 2 n, x ≤ (M : ℝ) ^ 3 * S * x := by
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have h1 : ((n + 1 - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n + 1 - 2 ≤ n)
  have h2 : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h3 : (n : ℝ) ^ 2 * ((n + 1 - 2 : ℕ) : ℝ) ≤ (M : ℝ) ^ 3 := by
    calc (n : ℝ) ^ 2 * ((n + 1 - 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 * n :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (n : ℝ) ^ 3 := by ring
      _ ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ hn0 h2 3
  have := mul_le_mul_of_nonneg_right h3 (mul_nonneg hS hx)
  nlinarith [this]

/-- **The discretization error, one step**: `‖K̃_v − K̃_u − (v−u) F(K̃_u)‖ ≤ 3 M⁶ N² (v−u)²` on a
sub-interval `[u, v]`, if `‖K̃‖ ≤ 1` on loops of length `2..M` and `M³ N (v−u) ≤ 1`,
`N = (W L)^d`. -/
private theorem Hyp_Kt_step {d L W : ℕ} [NeZero L] (Kt : ℝ → RBM.Loop.LoopIdx (Zd d L) → ℂ)
    {M : ℕ} {u v : ℝ} (huv : u ≤ v)
    (hK : ∀ t ∈ Set.Icc u v, ∀ I : RBM.Loop.LoopIdx (Zd d L), I.WF → 1 ≤ I.length →
      I.length ≤ M →
      HasDerivWithinAt (fun s => Kt s I) (primRhsGUE d L W (Kt t) I) (Set.Icc u v) t)
    (hbd : ∀ t ∈ Set.Icc u v, ∀ J : RBM.Loop.LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      J.length ≤ M → ‖Kt t J‖ ≤ 1)
    (hsmall : (M : ℝ) ^ 3 * (((W * L) ^ d : ℕ) : ℝ) * (v - u) ≤ 1)
    (I : RBM.Loop.LoopIdx (Zd d L)) (hI : I.WF) (hI1 : 1 ≤ I.length) (hIM : I.length ≤ M) :
    ‖Kt v I - Kt u I - ((v - u : ℝ) : ℂ) * primRhsGUE d L W (Kt u) I‖ ≤
      3 * (M : ℝ) ^ 6 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * (v - u) ^ 2 := by
  set S : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hSdef
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have huv' : 0 ≤ v - u := by linarith
  -- step A: `‖K̃_r − K̃_u‖ ≤ M³ S (r − u)` on loops of length `2..M`
  have hA : ∀ r ∈ Set.Icc u v, ∀ J : RBM.Loop.LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      J.length ≤ M → ‖Kt r J - Kt u J‖ ≤ (M : ℝ) ^ 3 * S * (r - u) := by
    intro r hr J hJ hJ2 hJM
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => Kt s J) (f' := fun s => primRhsGUE d L W (Kt s) J)
      (C := (M : ℝ) ^ 3 * S)
      (fun s hs => hK s hs J hJ (by omega) hJM)
      (fun s hs => by
        have hs' : s ∈ Set.Icc u v := Set.Ico_subset_Icc_self hs
        have h := norm_primRhsGUE_le d L W (Kt s) (fun _ => 1) J hJ
          (fun J' hJ' h2 hJ'J => hbd s hs' J' hJ' h2 (hJ'J.trans hJM)) (fun _ => zero_le_one)
        refine h.trans ?_
        have := Hyp_card_bound (n := J.length) (M := M) hJM hS zero_le_one
        simp only [mul_one] at this ⊢
        exact this) r hr
    simpa using hmvt
  -- step B: the derivative of `φ(r) = K̃_r − (r − u) F(K̃_u)` is `F(K̃_r) − F(K̃_u)`
  set e : ℝ := (M : ℝ) ^ 3 * S * (v - u) with hedef
  have he0 : 0 ≤ e := by positivity
  have hbil : ∀ r ∈ Set.Ico u v,
      ‖primRhsGUE d L W (Kt r) I - primRhsGUE d L W (Kt u) I‖ ≤
        3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) := by
    intro r hr
    have hr' : r ∈ Set.Icc u v := Set.Ico_subset_Icc_self hr
    have hu' : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
    rw [primRhsGUE_sub]
    have hD : ∀ J : RBM.Loop.LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖(Kt r - Kt u) J‖ ≤ e := by
      intro J hJ hJ2 hJI
      rw [Pi.sub_apply]
      refine (hA r hr' J hJ hJ2 (hJI.trans hIM)).trans ?_
      rw [hedef]
      exact mul_le_mul_of_nonneg_left (by linarith [hr'.2]) (by positivity)
    have hB1 : ∀ J : RBM.Loop.LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖Kt u J‖ ≤ 1 := fun J hJ h2 hJI => hbd u hu' J hJ h2 (hJI.trans hIM)
    have b1 := norm_primBilGUE_le d L W (Kt u) (Kt r - Kt u) (fun _ => 1) (fun _ => e)
      I hI hB1 hD (fun _ => zero_le_one) (fun _ => he0)
    have b2 := norm_primBilGUE_le d L W (Kt r - Kt u) (Kt u) (fun _ => e) (fun _ => 1)
      I hI hD hB1 (fun _ => he0) (fun _ => zero_le_one)
    have b3 := norm_primBilGUE_le d L W (Kt r - Kt u) (Kt r - Kt u) (fun _ => e)
      (fun _ => e) I hI hD hD (fun _ => he0) (fun _ => he0)
    have c1 := Hyp_card_bound (n := I.length) (M := M) hIM hS (x := 1 * e) (by positivity)
    have c2 := Hyp_card_bound (n := I.length) (M := M) hIM hS (x := e * 1) (by positivity)
    have c3 := Hyp_card_bound (n := I.length) (M := M) hIM hS (x := e * e) (by positivity)
    have he1 : e ≤ 1 := by rw [hedef]; linarith [hsmall]
    have hee : e * e ≤ e := by nlinarith
    have c3' : (M : ℝ) ^ 3 * S * (e * e) ≤ (M : ℝ) ^ 3 * S * e :=
      mul_le_mul_of_nonneg_left hee (by positivity)
    have hfin : (M : ℝ) ^ 3 * S * (1 * e) + (M : ℝ) ^ 3 * S * (e * 1) + (M : ℝ) ^ 3 * S * e
        = 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) := by rw [hedef]; ring
    calc ‖primBilGUE d L W (Kt u) (Kt r - Kt u) I +
            primBilGUE d L W (Kt r - Kt u) (Kt u) I +
            primBilGUE d L W (Kt r - Kt u) (Kt r - Kt u) I‖
        ≤ ‖primBilGUE d L W (Kt u) (Kt r - Kt u) I‖ +
            ‖primBilGUE d L W (Kt r - Kt u) (Kt u) I‖ +
            ‖primBilGUE d L W (Kt r - Kt u) (Kt r - Kt u) I‖ := norm_add₃_le
      _ ≤ (M : ℝ) ^ 3 * S * (1 * e) + (M : ℝ) ^ 3 * S * (e * 1) + (M : ℝ) ^ 3 * S * e := by
          gcongr
          · exact b1.trans c1
          · exact b2.trans c2
          · exact (b3.trans c3).trans c3'
      _ = 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) := hfin
  have hderiv : ∀ r ∈ Set.Icc u v, HasDerivWithinAt
      (fun s => Kt s I - ((s - u : ℝ) : ℂ) * primRhsGUE d L W (Kt u) I)
      (primRhsGUE d L W (Kt r) I - primRhsGUE d L W (Kt u) I) (Set.Icc u v) r := by
    intro r hr
    have h1 := hK r hr I hI hI1 hIM
    have h2 : HasDerivAt (fun s : ℝ => ((s - u : ℝ) : ℂ)) ((1 : ℝ) : ℂ) r :=
      ((hasDerivAt_id r).sub_const u).ofReal_comp
    have h3 := (h2.mul_const (primRhsGUE d L W (Kt u) I)).hasDerivWithinAt
      (s := Set.Icc u v)
    simp only [Complex.ofReal_one, one_mul] at h3
    exact h1.sub h3
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbil v ⟨huv, le_rfl⟩
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmvt
  calc ‖Kt v I - Kt u I - ((v - u : ℝ) : ℂ) * primRhsGUE d L W (Kt u) I‖
      = ‖Kt v I - ((v - u : ℝ) : ℂ) * primRhsGUE d L W (Kt u) I - Kt u I‖ := by
        congr 1; ring
    _ ≤ 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) * (v - u) := hmvt
    _ = 3 * (M : ℝ) ^ 6 * S ^ 2 * (v - u) ^ 2 := by ring

end HypKt
/-! ### The discretization error on the grid and the discrete Duhamel formula -/

section HypDuhamel

/-- **The discretization error** of `K̃` along the grid,
`‖K̃_{u_k} − K̃_{u_0} − Δ ∑_{j<k} F(K̃_{u_j})‖ ≤ 3 M⁶ N² Δ (t₀ − t₁)`, `N = (W L)^d`. -/
theorem Hyp_Kt_disc {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n M : ℕ}
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (ht10 : t1 n ≤ t0 n) (hK0 : K n ≠ 0)
    (hK : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ M →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hbd : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ M → ‖Kt n t J‖ ≤ 1)
    (hsmall : (M : ℝ) ^ 3 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1)
    {k : ℕ} (hk : k ≤ K n) (I : RBM.Loop.LoopIdx (Zd d (sz.L n))) (hI : I.WF) (hI1 : 1 ≤ I.length)
    (hIM : I.length ≤ M) :
    ‖Kt n (gridTime t1 t0 K n k) I - Kt n (gridTime t1 t0 K n 0) I -
        (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) I‖ ≤
      3 * (M : ℝ) ^ 6 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 2 * gridStep t1 t0 K n *
        (t0 n - t1 n) := by
  set Δ := gridStep t1 t0 K n with hΔdef
  have hΔ0 : 0 ≤ Δ := Hyp_step_nonneg ht10
  set a : ℕ → ℂ := fun j => Kt n (gridTime t1 t0 K n j) I with hadef
  set F : ℕ → ℂ := fun j =>
    primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) I with hFdef
  have hsucc : ∀ j : ℕ, gridTime t1 t0 K n (j + 1) - gridTime t1 t0 K n j = Δ := by
    intro j; unfold gridTime; rw [← hΔdef]; push_cast; ring
  have hstep : ∀ j, j < K n → ‖a (j + 1) - a j - (Δ : ℂ) * F j‖ ≤
      3 * (M : ℝ) ^ 6 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2 := by
    intro j hj
    have hsub : Set.Icc (gridTime t1 t0 K n j) (gridTime t1 t0 K n (j + 1)) ⊆
        Set.Icc (t1 n) (t0 n) :=
      Set.Icc_subset_Icc (Hyp_time_ge ht10 j) (Hyp_time_le ht10 hK0 (by omega))
    have huv : gridTime t1 t0 K n j ≤ gridTime t1 t0 K n (j + 1) :=
      Hyp_time_mono ht10 (Nat.le_succ j)
    have h := Hyp_Kt_step (d := d) (L := sz.L n) (W := sz.W n) (Kt n) (M := M) huv
      (fun t ht I' hI' h1 hM => (hK t (hsub ht) I' hI' h1 hM).mono hsub)
      (fun t ht J hJ h2 hJM => hbd t (hsub ht) J hJ h2 hJM)
      (by rw [hsucc j]; exact hsmall) I hI hI1 hIM
    rw [hsucc j] at h
    exact h
  have hid : a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, F j =
      ∑ j ∈ Finset.range k, (a (j + 1) - a j - (Δ : ℂ) * F j) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub, Finset.mul_sum]
  change ‖a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, F j‖ ≤ _
  rw [hid]
  have hKΔ : (K n : ℝ) * Δ = t0 n - t1 n := by
    rw [hΔdef]; unfold gridStep
    have : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK0
    field_simp
  calc ‖∑ j ∈ Finset.range k, (a (j + 1) - a j - (Δ : ℂ) * F j)‖
      ≤ ∑ j ∈ Finset.range k, ‖a (j + 1) - a j - (Δ : ℂ) * F j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, 3 * (M : ℝ) ^ 6 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2 :=
        Finset.sum_le_sum fun j hj => hstep j (by rw [Finset.mem_range] at hj; omega)
    _ = (k : ℝ) * (3 * (M : ℝ) ^ 6 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (K n : ℝ) * (3 * (M : ℝ) ^ 6 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
    _ = 3 * (M : ℝ) ^ 6 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 2 * Δ * (t0 n - t1 n) := by
        rw [← hKΔ]; ring

/-- The discrete Duhamel formula, in norm:
`a_k − b_k = (a_0 − b_0) + (a_k − a_0 − Δ∑(e+f)) + Δ∑(e + (f − g)) − (b_k − b_0 − Δ∑g)`. -/
private theorem Hyp_duhamel_norm (a b e f g : ℕ → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ) (k : ℕ) :
    ‖a k - b k‖ ≤ ‖a 0 - b 0‖ + ‖a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j)‖ +
      Δ * ∑ j ∈ Finset.range k, (‖e j‖ + ‖f j - g j‖) +
      ‖b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j‖ := by
  have hid : a k - b k = (a 0 - b 0) + (a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j))
      + (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))
      - (b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hid]
  have h3 : ‖(Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))‖ ≤
      Δ * ∑ j ∈ Finset.range k, (‖e j‖ + ‖f j - g j‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hΔ
    exact Finset.sum_le_sum fun j _ => norm_add_le _ _
  calc _ ≤ ‖(a 0 - b 0) + (a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j))
          + (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))‖
        + ‖b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j‖ := norm_sub_le _ _
    _ ≤ ‖a 0 - b 0‖ + ‖a k - a 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + f j)‖
          + ‖(Δ : ℂ) * ∑ j ∈ Finset.range k, (e j + (f j - g j))‖
        + ‖b k - b 0 - (Δ : ℂ) * ∑ j ∈ Finset.range k, g j‖ := by
        gcongr
        exact norm_add₃_le
    _ ≤ _ := by linarith [h3]

/-- `g(u) ≤ sup_{[t₁,t]} g` for a function continuous on `[t₁,t₀]` and `u ∈ [t₁,t] ⊆ [t₁,t₀]`. -/
private theorem Hyp_le_supOn {g : ℝ → ℝ} {a b c u : ℝ} (hg : ContinuousOn g (Set.Icc a c))
    (hbc : b ≤ c) (hu : u ∈ Set.Icc a b) : g u ≤ supOn g a b := by
  have hsub : Set.Icc a b ⊆ Set.Icc a c := Set.Icc_subset_Icc le_rfl hbc
  have hbdd : BddAbove (g '' Set.Icc a b) :=
    IsCompact.bddAbove_image isCompact_Icc (hg.mono hsub)
  have hbdd' : BddAbove (Set.range fun v : Set.Icc a b => g v) := by
    rw [← Set.image_eq_range] at *
    simpa [Set.image] using hbdd
  exact le_ciSup hbdd' ⟨u, hu⟩

/-- The generator of one GUE-phase increment splits at every loop of length `m ≥ 1`:
`genMatGUE(𝓛) = 𝓔^{(G̃)} + F(𝓛)` (`loopGenGUE` for `m ≥ 2`, `loopGenGUE_one` for `m = 1`, where
`F = primRhsGUE` of a `1`-loop is `0`). -/
private theorem Hyp_genMat_split {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) {m : ℕ} (hm : 1 ≤ m) (σ : Fin m → Bool) (a : Fin m → Zd d L) :
    genMatGUE d L W E u M (loopOf σ a) =
      egtNGUE d L W E u M (loopOf σ a) +
        primRhsGUE d L W (loopL d L W (blockMat d L W M) (zt E u)) (loopOf σ a) := by
  rcases Nat.lt_or_ge 1 m with hm2 | hm1
  · rw [loopGenGUE d L W E hL hE u hu0 hu1 M hM m hm2 σ a, add_comm]
  · obtain rfl : m = 1 := by omega
    rw [loopGenGUE_one d L W E hL hE u hu0 hu1 M hM σ a]
    have h0 : primRhsGUE d L W (loopL d L W (blockMat d L W M) (zt E u)) (loopOf σ a) = 0 :=
      Hyp_primRhs_one _ _ (by simp [loopOf, RBM.Loop.LoopIdx.length])
    rw [h0, add_zero]

/-- **The grid bound at `k ≤ σ`** (pathwise): the discrete Duhamel formula
with the initial term, the martingale remainder (`hM`, `hq`), the drift (`hF`, `heG`) and the
`K̃` discretization (`hdisc`), for every `t` that dominates all earlier grid times.  The drift of
`hM` is `genMatGUE`, split at each grid time by `loopGenGUE`/`loopGenGUE_one` into
`primRhsGUE (𝓛) + egtNGUE` (the hypotheses `hE`, `ht1`, `ht0`, `hm` are those of the split). -/
theorem Hyp_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (ω : PathΩ sz)
    (g1 g3 g4 : ℝ → ℝ) {c Cf Ce err Λ0 : ℝ}
    (ht10 : t1 n ≤ t0 n) (hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht0 : t0 n < 1) (hm : 1 ≤ m)
    (hc : 0 ≤ c) (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce)
    (hg1 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g1 u) (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u)
    (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg1c : ContinuousOn g1 (Set.Icc (t1 n) (t0 n)))
    (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
          (zt (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖ ≤ c * Λ0)
    (hM : ∀ k ≤ K n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
          (zt (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω))
            (zt (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
              genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j)
                (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤
        c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) *
          (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
              (zt (E n) (gridTime t1 t0 K n j)) (2 * m)))
          + (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m))
    (hq : ∀ j < gueStop sz E t1 t0 K δ n ω,
      Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
          (zt (E n) (gridTime t1 t0 K n j)) (2 * m)) ≤ g4 (gridTime t1 t0 K n j))
    (hF : ∀ j < gueStop sz E t1 t0 K δ n ω, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2) -
        primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤
        Cf * g1 (gridTime t1 t0 K n j))
    (heG : ∀ j < gueStop sz E t1 t0 K δ n ω, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω)
          (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 K n j))
    (hdisc : ∀ k ≤ K n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2) -
        (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ err)
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) {k : ℕ} (hkσ : k ≤ gueStop sz E t1 t0 K δ n ω)
    (hkt : ∀ j < k, gridTime t1 t0 K n j ≤ t) :
    gueDmax sz E t1 t0 K Kt n m k ω ≤ (c * Λ0 + err) +
      c * (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m +
      (Cf * supOn g1 (t1 n) t + Ce * supOn g3 (t1 n) t) *
        (gridTime t1 t0 K n k - t1 n) +
      (c * supOn g4 (t1 n) t) * Real.sqrt (gridTime t1 t0 K n k - t1 n) := by
  set σ := gueStop sz E t1 t0 K δ n ω with hσdef
  have hσK : σ ≤ K n := firstHit_le _ _ _ ω
  have hkK : k ≤ K n := hkσ.trans hσK
  set Δ := gridStep t1 t0 K n with hΔdef
  have hΔ0 : 0 ≤ Δ := Hyp_step_nonneg ht10
  have hkΔ : (k : ℝ) * Δ = gridTime t1 t0 K n k - t1 n := (Hyp_time_sub k).symm
  have hjmem : ∀ j < k, gridTime t1 t0 K n j ∈ Set.Icc (t1 n) t :=
    fun j hj => ⟨Hyp_time_ge ht10 j, hkt j hj⟩
  set S1 := supOn g1 (t1 n) t
  set S3 := supOn g3 (t1 n) t
  set S4 := supOn g4 (t1 n) t
  have hS1 : ∀ j < k, g1 (gridTime t1 t0 K n j) ≤ S1 := fun j hj =>
    Hyp_le_supOn hg1c ht.2 (hjmem j hj)
  have hS3 : ∀ j < k, g3 (gridTime t1 t0 K n j) ≤ S3 := fun j hj =>
    Hyp_le_supOn hg3c ht.2 (hjmem j hj)
  have hS4 : ∀ j < k, g4 (gridTime t1 t0 K n j) ≤ S4 := fun j hj =>
    Hyp_le_supOn hg4c ht.2 (hjmem j hj)
  have hS4n : 0 ≤ S4 := supOn_nonneg fun u hu => hg4 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS1n : 0 ≤ S1 := supOn_nonneg fun u hu => hg1 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS3n : 0 ≤ S3 := supOn_nonneg fun u hu => hg3 u ⟨hu.1, hu.2.trans ht.2⟩
  unfold gueDmax
  refine ciSup_le fun x => ?_
  have hD := Hyp_duhamel_norm
    (a := fun j => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
      (zt (E n) (gridTime t1 t0 K n j)) (loopOf x.1 x.2))
    (b := fun j => Kt n (gridTime t1 t0 K n j) (loopOf x.1 x.2))
    (e := fun j => egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j)
      (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2))
    (f := fun j => primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j)))
      (loopOf x.1 x.2))
    (g := fun j => primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2))
    hΔ0 k
  have hM' := hM k hkK x
  have hsplit : ∑ j ∈ Finset.range k, genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j)
        (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2) =
      ∑ j ∈ Finset.range k, (egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j)
        (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2) +
        primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact Hyp_genMat_split (sz.three_le_L n) hE (ht1.trans (Hyp_time_ge ht10 j))
      (lt_of_le_of_lt (hkt j hj) (lt_of_le_of_lt ht.2 ht0))
      (gueH_isHermitian sz t1 t0 K n j ω) hm x.1 x.2
  rw [hsplit] at hM'
  have hsup : (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
      (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
      RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
        (zt (E n) (gridTime t1 t0 K n j)) (2 * m))) ≤ S4 :=
    Real.iSup_le (fun j => (hq j (lt_of_lt_of_le j.2 hkσ)).trans (hS4 j j.2)) hS4n
  have hsum : ∑ j ∈ Finset.range k,
      (‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω)
          (loopOf x.1 x.2)‖ +
        ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2) -
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖) ≤
      (k : ℝ) * (Cf * S1 + Ce * S3) := by
    calc _ ≤ ∑ _j ∈ Finset.range k, (Cf * S1 + Ce * S3) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          have hjσ : j < σ := lt_of_lt_of_le hj hkσ
          have e1 := (heG j hjσ x).trans (mul_le_mul_of_nonneg_left (hS3 j hj) hCe)
          have e2 := (hF j hjσ x).trans (mul_le_mul_of_nonneg_left (hS1 j hj) hCf)
          linarith
      _ = (k : ℝ) * (Cf * S1 + Ce * S3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hΛ0 := h0 x
  have hdk := hdisc k hkK x
  have hsqrt0 : 0 ≤ Real.sqrt (gridTime t1 t0 K n k - t1 n) := Real.sqrt_nonneg _
  have hMb : c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) *
      (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
        (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω))
          (zt (E n) (gridTime t1 t0 K n j)) (2 * m)))
      + (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m) ≤
      c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) * S4
        + (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m) := by
    gcongr
  have hsumΔ := mul_le_mul_of_nonneg_left hsum hΔ0
  have hfin : Δ * ((k : ℝ) * (Cf * S1 + Ce * S3)) =
      (Cf * S1 + Ce * S3) * (gridTime t1 t0 K n k - t1 n) := by
    rw [← hkΔ]; ring
  have hM'' := hM'.trans hMb
  linarith

end HypDuhamel

end RBM.Univ.GUEPhase

/-! ## Compiled nonempty instances (CLAUDE.md §4 step 2)

`HypAInst`.  `d = 3`.  The grid-time facts and `Hyp_interp_bound` at the window `[1/4, 1/2]`, `K = 64`,
`n = 0`; the loop-level helpers at `d = 3`, `L = 3`, `W = 2`; the `K̃` targets at the merged
`Grid.lean` §`GridCheck` sizes `sz0` (`L = 4 (n+1)`, `W = (2 (n+1))^5`, `ilambda = (2 (n+1))^{-6}`,
`N = 2^21 (n+1)^18 → ∞`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `κ = 1/10`, `E = 0`
(`m = I`), `τ_U = 1/1000`, `n₀ = 2`, and the window `1 - t₁ = y_n = ilambda²/L^d` (the boundary of
`hell`), `t₀ - t₁ = y_n/(N+1)`, `K = 64`.  `Hyp_Kt_detDom`: `STKbound` by the merged
`Sizes.stKbound_holds`, the primitive family `Kt` from `gueK_exists`; `Hyp_Kt_disc` and `Hyp_grid`
use the stationary solution `K̃ = m_σ` on `1`-loops, `0` on longer loops; `Hyp_grid` at the concrete
path `ω₀ = 0`, with `δ` above the finite sum of `gueDev` (so `gueStop = 64`) and the constants
`c, C_f, C_e, g₄` finite sums of the left sides of `h0, hM, hF, heG, hq`. -/

/-! ### Grid times and the interpolation bound at the window `[1/4, 1/2]`, `K = 64` -/

/-! ### Loop-level helpers at `d = 3`, `L = 3`, `W = 2` -/

/-! ### The window at the `GridCheck` sizes `sz0`: `E = 0`, `1 - t₁ = y`, `t₀ - t₁ = y/(N+1)` -/

/-! ### The stationary solution and the primitive family at `sz0` -/

/-! ### `Hyp_Kt_disc` and `Hyp_grid` at `sz0`, `n = 0` (`N = 2097152`), `M = 4`, `K = 64` -/

end
