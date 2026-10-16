/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEProcBA
import RBM3D.BA.KBound
import RBM3D.Universality.GUEPhase.ProcK
import RBM3D.Universality.GUEPhase.HypA

/-!
# BA-C5 row a: the deterministic `K̃` and the grid bound on the GUE-phase grid at block Anderson

Ticket T2519 (row a, target 3; DECISIONS §344, §346, §348; Amends 1-3).  New BA leaf: no merged
file is edited.  Band twins: `Universality/GUEPhase/ProcK.lean` (`gueKproc_detDom:553`) and
`HypA.lean` (`Hyp_Kt_detDom:690`, `Hyp_Kt_one:712`, `Hyp_grid:981`).  Paper: the GUE phase of
Thm 2.4 (`paper/tex/1_2_Intro_model_result.tex:566-570`, "essentially identical to [YY_25,
Theorem 2.6]").

What changes from the band (UBA-C1: statements at the flow datum `(g, E, m)`, `g = λ₀`):

* the scale `gueScale sz E n t = N etaT (E n) t` becomes `N etaOf (m n) t`;
* the pin `hKb : sz.STKbound E` is not a premise at BA: the deterministic bound
  `baKBoundAt_holds` (`BA/KBound:85`, `|𝒦^{(k)}| ≤ C L^τ (W^{-d} B_{t,0}(g))^{k-1}` for `BAReal`
  data with `0 < g ≤ Λ`) gives `K̃` at `t₁` (`hKinit` is the start `BAKsol`), so the window
  `0 < g ≤ Λ` is only needed eventually;
* the zero-mode condition is `L^d (1 - t₁) ≤ 2 g²` (the RBG text has `L^d (1 - t₁) ≤ λ²` and
  `g² = t₀ λ²` with `t₀ ≥ t₁ ≥ 26/27` from `L^d (1 - t₁) ≤ 1`, `L ≥ 3`, `d ≥ 3`:
  `GUEHypABA_hell_of_hell`);
* `|E| ≤ 2 - κ` becomes `BAReal d L g κ E m` (`0 < Im m`, `‖m‖ ≤ 1`);
* the clauses `hKinit`, `hK` are those of `BAKFam` (guarded by `0 < g n`);
* `hscale` of `gueKproc_detDom` is unused there and dropped.

The band privates of `ProcK`, `HypA` that carry no band token are read by `open private`.

* §1 `Hyp_Kt_detDomBA` (the pointwise bound, conclusion `hKdet`), `gueKproc_detDomBA` (the
  interpolated grid maximum), `Hyp_Kt_oneBA` (`K̃ = m_σ` on 1-loops), `GUEHypABA_hell_of_hell`
  (the zero-mode premise from the RBG ones); private: `HypABA_Bparam_le`, `HypABA_initial`,
  `HypABA_hbase`.
* §2 `Hyp_gridBA` (the pathwise grid bound at `k ≤ σ`; the split of the drift is `loopGenGUEOf`).
* §3 compiled nonempty instances at `d = 3`, `sz0` and its BA flow datum.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private ProcK_size_pos ProcK_one_le_size ProcK_ofFn_getD ProcK_loopOf_eq ProcK_lam_near_le
  ProcK_gueTent_sum_le_two ProcK_inv_le_two_inv_of_le_two_mul ProcK_gueKbar_mono ProcK_gueTime_mem_Icc
  ProcK_gueTime_kstar_near ProcK_gueKbar_le_of_hbase ProcK_gueTent_nonneg from
  RBM3D.Universality.GUEPhase.ProcK
open private Hyp_primRhs_one Hyp_le_supOn Hyp_duhamel_norm Hyp_time_mono Hyp_time_sub Hyp_time_zero from
  RBM3D.Universality.GUEPhase.HypA

noncomputable section

namespace RBM.BA

open MeasureTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase

/-! ## 1. `K̃` at `t₁` from `baKBoundAt_holds` and the bootstrap (7.36) -/

section KBound

/-- **The conversion** `W^{-d} B_{t,0}(g) ≤ 3 (N η_t)⁻¹` under the zero-mode condition `L^d (1 - t) ≤ 2 g²`
(`(g² + x)⁻¹ ≤ 2 (L^d x)⁻¹`, so `W^{-d} B ≤ 3 W^{-d} (L^d x)⁻¹ = 3 (N x)⁻¹ ≤ 3 (N x Im m)⁻¹`, `Im m ≤ ‖m‖ ≤ 1`);
twin of `ProcK_Bctl_le`/`Hyp_Bctl_le` at the coupling `g` of the flow datum. -/
private theorem HypABA_Bparam_le (d L W : ℕ) [NeZero L] [NeZero W] {g t : ℝ} {m : ℂ} (hm : 0 < m.im)
    (hm1 : ‖m‖ ≤ 1) (ht : t < 1) (hell : (L : ℝ) ^ d * (1 - t) ≤ 2 * g ^ 2) :
    (((W : ℕ) : ℝ) ^ d)⁻¹ * Bparam d L g t 0 ≤ 3 * ((((W * L) ^ d : ℕ) : ℝ) * etaOf m t)⁻¹ := by
  have hx : 0 < 1 - t := by linarith
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := pow_pos hL d
  have hN : (((W * L) ^ d : ℕ) : ℝ) = (W : ℝ) ^ d * (L : ℝ) ^ d := by push_cast; ring
  have hηpos : 0 < etaOf m t := mul_pos hx hm
  have hηle : etaOf m t ≤ 1 - t := by
    unfold etaOf
    calc (1 - t) * m.im ≤ (1 - t) * 1 :=
          mul_le_mul_of_nonneg_left (le_trans (Complex.im_le_norm m) hm1) hx.le
      _ = 1 - t := mul_one _
  have h1 : (g ^ 2 + (1 - t))⁻¹ ≤ 2 * ((L : ℝ) ^ d * (1 - t))⁻¹ :=
    ProcK_inv_le_two_inv_of_le_two_mul (mul_pos hLd hx) (by positivity) (by nlinarith [sq_nonneg g])
  have hB : Bparam d L g t 0 ≤ 3 * ((L : ℝ) ^ d * (1 - t))⁻¹ := by
    unfold Bparam
    rw [abs_of_pos hx]
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    linarith
  have hNx : ((W : ℝ) ^ d * (L : ℝ) ^ d * (1 - t))⁻¹ ≤ ((W : ℝ) ^ d * (L : ℝ) ^ d * etaOf m t)⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hηle (by positivity))
  have hid : ((W : ℝ) ^ d)⁻¹ * (3 * ((L : ℝ) ^ d * (1 - t))⁻¹) = 3 * ((W : ℝ) ^ d * (L : ℝ) ^ d * (1 - t))⁻¹ := by
    field_simp
  rw [hN]
  calc ((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0 ≤ ((W : ℝ) ^ d)⁻¹ * (3 * ((L : ℝ) ^ d * (1 - t))⁻¹) :=
        mul_le_mul_of_nonneg_left hB (inv_nonneg.2 hWd.le)
    _ = 3 * ((W : ℝ) ^ d * (L : ℝ) ^ d * (1 - t))⁻¹ := hid
    _ ≤ 3 * ((W : ℝ) ^ d * (L : ℝ) ^ d * etaOf m t)⁻¹ := by linarith

/-- The initial data of `K̃` at `t₁`: `‖K̃_{t₁, I}‖ ≤ N^{τ'} (N η_{t₁})^{-|I|+1}` for loops of length in `[2, 2 n₀]`, from
`baKBoundAt_holds` at `τ = τ'/4` (the constants `C_ℓ`, `ℓ ∈ [2, 2 n₀]`, are summed), the start `hKinit` (the clause of `BAKFam`),
the conversion `HypABA_Bparam_le` (`hell`), `L^{τ'/4} ≤ N^{τ'/4}`, and `N → ∞` (`hsz`) for the thresholds; the window `0 < g ≤ Λ` is
used only eventually (twin of `ProcK_initial`/`Hyp_initial`, from the pin `STKbound` at the band). -/
private theorem HypABA_initial {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ Λ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (n0 : ℕ)
    {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ Λ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop)
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I =
      BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ n : ℕ in atTop, ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length → I.length ≤ 2 * n0 →
      ‖Kt n (t1 n) I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n))⁻¹ ^ (I.length - 1) := by
  classical
  have hall : ∀ ℓ : ℕ, ∃ C : ℝ, 0 < C ∧ (2 ≤ ℓ → ℓ ≤ 2 * n0 → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W →
      ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d L),
          ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)‖
            ≤ C * (L : ℝ) ^ (τ' / 4) * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (ℓ - 1)) := by
    intro ℓ
    by_cases hℓ : 2 ≤ ℓ ∧ ℓ ≤ 2 * n0
    · obtain ⟨C, hC, H⟩ := baKBoundAt_holds d hd hΛ hκ ℓ (by omega) (τ' / 4) (by positivity)
      exact ⟨C, hC, fun _ _ => H⟩
    · exact ⟨1, one_pos, fun h2 h3 => absurd ⟨h2, h3⟩ hℓ⟩
  choose C hCpos hCbd using hall
  set Cm : ℝ := ∑ ℓ ∈ Finset.range (2 * n0 + 1), C ℓ with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun ℓ _ => (hCpos ℓ).le
  have hCle : ∀ ℓ, ℓ ≤ 2 * n0 → C ℓ ≤ Cm := fun ℓ hℓ =>
    Finset.single_le_sum (f := C) (fun i _ => (hCpos i).le) (Finset.mem_range.2 (by omega))
  have hpow : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ^ (2 * n0) * Cm ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) :=
    hsz.eventually (eventually_le_rpow ((3 : ℝ) ^ (2 * n0) * Cm) (half_pos hτ'))
  filter_upwards [hlam, hell, hpow] with n hlamn hellN hpowN
  intro I hWF h2 h2n
  have ht1lt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hrn := hr n
  have hm0 : 0 < (m n).im := hrn.1.1
  have hm1 : ‖m n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) hrn.1
  have hb := hCbd I.length h2 h2n (sz.L n) (sz.three_le_L n) (sz.W n) (sz.W_pos n) (g n) hlamn.1 hlamn.2 (E n)
    (m n) hrn (t1 n) (ht1 n) ht1lt (fun i : Fin I.length => I.σ.getD i false)
    (fun i : Fin I.length => I.a.getD i (0 : Zd d (sz.L n)))
  have hloop : KLloopOf d (sz.L n) (fun i : Fin I.length => I.σ.getD i false)
      (fun i : Fin I.length => I.a.getD i (0 : Zd d (sz.L n))) = I := ProcK_loopOf_eq I hWF
  rw [hloop] at hb
  rw [hKinit n hlamn.1 I]
  refine hb.trans ?_
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := ProcK_one_le_size sz n
  have hN0 : 0 < N := by linarith
  set Λ1 : ℝ := (N * etaOf (m n) (t1 n))⁻¹ with hΛ1
  have hη : 0 < etaOf (m n) (t1 n) := mul_pos (by linarith) hm0
  have hΛ10 : 0 ≤ Λ1 := by positivity
  have hBle : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (g n) (t1 n) 0 ≤ 3 * Λ1 :=
    HypABA_Bparam_le d (sz.L n) (sz.W n) hm0 hm1 ht1lt hellN
  have hB0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (g n) (t1 n) 0 := by
    have hx : 0 < 1 - t1 n := by linarith
    unfold Bparam
    rw [abs_of_pos hx]
    positivity
  have hpowle : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (g n) (t1 n) 0) ^ (I.length - 1)
      ≤ 3 ^ (2 * n0) * Λ1 ^ (I.length - 1) :=
    calc _ ≤ (3 * Λ1) ^ (I.length - 1) := pow_le_pow_left₀ hB0 hBle _
      _ = 3 ^ (I.length - 1) * Λ1 ^ (I.length - 1) := mul_pow _ _ _
      _ ≤ 3 ^ (2 * n0) * Λ1 ^ (I.length - 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  have hLN : ((sz.L n : ℕ) : ℝ) ^ (τ' / 4) ≤ N ^ (τ' / 4) := by
    have h := sz.L_rpow_le (by omega : 0 < d) n (by positivity : 0 ≤ τ' / 4)
    refine h.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hτ']
  have hCl := hCle I.length h2n
  have hCp := (hCpos I.length).le
  calc C I.length * ((sz.L n : ℕ) : ℝ) ^ (τ' / 4) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (g n) (t1 n) 0) ^ (I.length - 1)
      ≤ Cm * N ^ (τ' / 4) * (3 ^ (2 * n0) * Λ1 ^ (I.length - 1)) := by
        refine mul_le_mul (mul_le_mul hCl hLN (by positivity) hCm0) hpowle (by positivity) (by positivity)
    _ = ((3 : ℝ) ^ (2 * n0) * Cm) * N ^ (τ' / 4) * Λ1 ^ (I.length - 1) := by ring
    _ ≤ N ^ (τ' / 2) * N ^ (τ' / 4) * Λ1 ^ (I.length - 1) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpowN (by positivity)) (by positivity)
    _ ≤ N ^ τ' * Λ1 ^ (I.length - 1) := by
        have h1 : N ^ (τ' / 2) * N ^ (τ' / 4) = N ^ (τ' / 2 + τ' / 4) := (Real.rpow_add hN0 _ _).symm
        rw [h1]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity)

/-- (7.36) on the size scale at BA: for every `τ > 0`, eventually in `n`, `‖K̃_{t,I}‖ ≤ N^τ (N η_t)^{-|I|+1}` on `[t₁, t₀]` for loops of
length in `[2, 2 n₀]`, `η_t = etaOf (m n) t`.  The scale-free `eq736` is applied at each `n` with `A = N^{τ'}`, `ε = N^{-τ_U}`;
the index-scale thresholds and `HypABA_initial` are transferred along `sz.size` (twin of `ProcK_hbase`/`Hyp_hbase`). -/
private theorem HypABA_hbase {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ Λ τU : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hτU : 0 < τU)
    (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ Λ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n))
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I =
      BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length →
      I.length ≤ 2 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length →
      I.length ≤ 2 * n0 →
      ‖Kt n t I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (I.length - 1) := by
  set τ' := min τ τU / 2 with hτ'
  have hτ'0 : 0 < τ' := by have := lt_min hτ hτU; positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : τ' < τU := by have := min_le_right τ τU; linarith
  filter_upwards [HypABA_initial hd sz hκ hΛ n0 hr hlam ht1 ht10 ht0 hsz hell Kt hKinit hτ'0, h730,
    hsz.eventually (eventually_small (n := 2 * n0) hτ'U),
    hsz.eventually (eventually_le_rpow 2 (sub_pos.2 hτ'τ)), hlam] with n hinit h730n hε h2 hlamn
  intro t ht I hWF h2I hIn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := ProcK_size_pos sz n
  have hm0 : 0 < (m n).im := (hr n).1.1
  have ht1lt : ∀ u ∈ Set.Icc (t1 n) (t0 n), u < 1 := fun u hu => lt_of_le_of_lt hu.2 (ht0 n)
  have hlam' : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < ((sz.size n : ℕ) : ℝ) * etaOf (m n) u := fun u hu =>
    mul_pos hN0 (mul_pos (by linarith [ht1lt u hu]) hm0)
  have hanti' : ∀ u v : ℝ, u ≤ v → etaOf (m n) v ≤ etaOf (m n) u := fun u v huv => by
    unfold etaOf; nlinarith [hm0]
  have hanti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ v ∈ Set.Icc (t1 n) (t0 n), u ≤ v →
      ((sz.size n : ℕ) : ℝ) * etaOf (m n) v ≤ ((sz.size n : ℕ) : ℝ) * etaOf (m n) u := fun u _ v _ huv =>
    mul_le_mul_of_nonneg_left (hanti' u v huv) hN0.le
  have hlamc : ContinuousOn (fun u => ((sz.size n : ℕ) : ℝ) * etaOf (m n) u) (Set.Icc (t1 n) (t0 n)) := by
    have heq : (fun u => ((sz.size n : ℕ) : ℝ) * etaOf (m n) u) =
        fun u => ((sz.size n : ℕ) : ℝ) * ((1 - u) * (m n).im) := rfl
    rw [heq]
    fun_prop
  have hA : 0 < ((sz.size n : ℕ) : ℝ) ^ τ' := Real.rpow_pos_of_pos hN0 _
  have hsmall : ∀ u ∈ Set.Icc (t1 n) (t0 n),
      (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) * (u - t1 n) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-τU) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) u) := by
    intro u hu
    have h1 : u - t1 n ≤ t0 n - t1 n := by linarith [hu.2]
    have h2' : etaOf (m n) (t0 n) ≤ etaOf (m n) u := hanti' u (t0 n) hu.2
    have hNpow : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := Real.rpow_nonneg hN0.le _
    have h3 : u - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) u :=
      le_trans h1 (le_trans h730n (mul_le_mul_of_nonneg_left h2' hNpow))
    have e : (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) := rfl
    rw [e]
    calc ((sz.size n : ℕ) : ℝ) * (u - t1 n)
        ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) u) :=
          mul_le_mul_of_nonneg_left h3 hN0.le
      _ = ((sz.size n : ℕ) : ℝ) ^ (-τU) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) u) := by ring
  have key := eq736 d (sz.L n) (sz.W n) (Kt n) (n := 2 * n0) (ht10 n)
    (fun u => ((sz.size n : ℕ) : ℝ) * etaOf (m n) u) hlam' hanti hlamc (hK n hlamn.1) hA
    (fun J hJ h2J hJn => hinit J hJ h2J hJn) hsmall hε t ht I hWF h2I hIn
  have hx : 0 ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (I.length - 1) :=
    pow_nonneg (inv_pos.2 (hlam' t ht)).le _
  have hsplit : ((sz.size n : ℕ) : ℝ) ^ τ
      = ((sz.size n : ℕ) : ℝ) ^ (τ - τ') * ((sz.size n : ℕ) : ℝ) ^ τ' := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [hsplit]
  have : 2 * ((sz.size n : ℕ) : ℝ) ^ τ' * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (I.length - 1)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - τ') * ((sz.size n : ℕ) : ℝ) ^ τ' *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (I.length - 1) := by
    gcongr
  linarith

/-- **The bound (7.36) at every `t ∈ [t₁, t₀]`, deterministic, at BA** (twin of `Hyp_Kt_detDom`, `HypA:690`): `‖K̃_t(J)‖ ≺ (N η_t)^{-|J|+1}`,
uniformly in `t ∈ [t₁, t₀]` and the well-formed loops `2 ≤ |J| ≤ 2 n₀`, in the explicit size-scale form (`N = sz.size n`,
`η_t = etaOf (m n) t`; at `n₀ = 4` the conclusion is `hKdet` of the signed chain, probe `t/T2519` b992c2e7, `RBM3D/Probe/T2519Pins.lean:238-240`,
Amend 3 item 5, with `2 * n₀ = 2 * 4`).  The pin
`hKb` of the band is replaced by `baKBoundAt_holds` (`BAReal` data, window `0 < g ≤ Λ` eventually); `hK` is the clause of `BAKFam` for
`1 ≤ |I| ≤ 4 n₀`, guarded by `0 < g n`. -/
theorem Hyp_Kt_detDomBA {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ Λ τU : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hτU : 0 < τU)
    (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ Λ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n))
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I =
      BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)),
      I.WF → 2 ≤ I.length → I.length ≤ 2 * n0 →
      ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1) :=
  fun _ hτ => HypABA_hbase hd sz hκ hΛ hτU n0 hr hlam ht1 ht10 ht0 hsz h730 hell Kt hKinit
    (fun n hg t ht I hI h2 hlen => hK n hg t ht I hI (by omega) (by omega)) hτ

/-- **`hK` for `gueKproc` at BA** (twin of `gueKproc_detDom`, `ProcK:553`): `K̃ ≺ Λ^{l-1}` on the grid, interpolated, in the explicit
size-scale form `∀ ε > 0, ∀ᶠ n, … ≤ (sz.size n)^ε · (N η_t)^{-(l-1)}`, `η_t = etaOf (m n) t`.  The initial data at `t₁` come from
`baKBoundAt_holds` (not the band pin), the bootstrap `eq736` is applied at each `n`, and `Tendsto sz.size atTop atTop` turns `∀ᶠ N`
into `∀ᶠ n`.  The band hypothesis `hscale` is unused there and is not carried. -/
theorem gueKproc_detDomBA {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ Λ τU : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hτU : 0 < τU)
    (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ Λ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto sz.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n))
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I =
      BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (l : Set.Icc 2 (2 * n0)),
      gueKproc sz t1 t0 (gueGridK sz n0) Kt n (l : ℕ) (t : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t : ℝ))⁻¹ ^ ((l : ℕ) - 1) := by
  intro τ hτ
  have hτ'0 : 0 < τ / 2 := by positivity
  filter_upwards [HypABA_hbase hd sz hκ hΛ hτU n0 hr hlam ht1 ht10 ht0 hsz h730 hell Kt hKinit
      (fun n hg t ht I hWF h2 hlen => hK n hg t ht I hWF (by omega) (by omega)) hτ'0, h730,
    hsz.eventually (eventually_le_rpow ((2 : ℝ) ^ (2 * n0 + 1)) hτ'0)] with n hbaseN h730n h2pow
  rintro ⟨t, ht⟩ ⟨l, hl⟩
  simp only [Set.mem_Icc] at hl ht
  change gueKproc sz t1 t0 (gueGridK sz n0) Kt n l t ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (l - 1)
  set Nn : ℝ := ((sz.size n : ℕ) : ℝ) with hNn
  have hN0 : 0 < Nn := ProcK_size_pos sz n
  have hN1 : 1 ≤ Nn := ProcK_one_le_size sz n
  have hm0 : 0 < (m n).im := (hr n).1.1
  have hm1 : ‖m n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) (hr n).1
  have hmim1 : (m n).im ≤ 1 := (Complex.im_le_norm _).trans hm1
  have ht1lt : ∀ u ∈ Set.Icc (t1 n) (t0 n), u < 1 := fun u hu => lt_of_le_of_lt hu.2 (ht0 n)
  have hlam_pos : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < Nn * etaOf (m n) u := fun u hu =>
    mul_pos hN0 (mul_pos (by linarith [ht1lt u hu]) hm0)
  have hanti' : ∀ u v : ℝ, u ≤ v → etaOf (m n) v ≤ etaOf (m n) u := fun u v huv => by
    unfold etaOf; nlinarith [hm0]
  have hlam_anti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ v ∈ Set.Icc (t1 n) (t0 n), u ≤ v →
      Nn * etaOf (m n) v ≤ Nn * etaOf (m n) u := fun u _ v _ huv =>
    mul_le_mul_of_nonneg_left (hanti' u v huv) hN0.le
  have hKne : gueGridK sz n0 n ≠ 0 := gueGridK_ne_zero sz n0 n
  have hstepN : gridStep t1 t0 (gueGridK sz n0) n ≤ etaOf (m n) (t0 n) := by
    have hetat0nonneg : 0 ≤ etaOf (m n) (t0 n) := mul_nonneg (by linarith [ht0 n]) hm0.le
    have hK1 : (1 : ℝ) ≤ (gueGridK sz n0 n : ℝ) := by
      have hge1 : 1 ≤ gueGridK sz n0 n := Nat.one_le_iff_ne_zero.2 hKne
      exact_mod_cast hge1
    have hNpow_le1 : Nn ^ (-τU) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    unfold gridStep
    have hK0 : (0 : ℝ) < (gueGridK sz n0 n : ℝ) := by linarith
    rw [div_le_iff₀ hK0]
    calc t0 n - t1 n ≤ Nn ^ (-τU) * etaOf (m n) (t0 n) := h730n
      _ ≤ 1 * etaOf (m n) (t0 n) := mul_le_mul_of_nonneg_right hNpow_le1 hetat0nonneg
      _ = etaOf (m n) (t0 n) := one_mul _
      _ ≤ etaOf (m n) (t0 n) * (gueGridK sz n0 n : ℝ) := by nlinarith [hK1, hetat0nonneg]
  have hperk : ∀ k : ℕ, k ≤ gueGridK sz n0 n →
      gueKbar sz t1 t0 (gueGridK sz n0) Kt n l k ≤
        Nn ^ (τ / 2) * (Nn * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ (l - 1) :=
    fun k hk => ProcK_gueKbar_le_of_hbase sz t1 t0 (gueGridK sz n0) n n0 l Kt (fun u => Nn * etaOf (m n) u)
      (Nn ^ (τ / 2)) (Real.rpow_nonneg hN0.le _) (ht10 n) hKne hlam_pos hlam_anti
      (fun u hu I hWF h2 hlen => hbaseN u hu I hWF h2 hlen) hl.1 hl.2 k hk
  by_cases hstep0 : gridStep t1 t0 (gueGridK sz n0) n = 0
  · have ht1t0eq : t1 n = t0 n := by
      by_contra hne
      apply hne
      have hKR : (gueGridK sz n0 n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hKne
      have := hstep0
      unfold gridStep at this
      field_simp at this
      linarith [this]
    have hteq : t = t1 n := le_antisymm (by rw [ht1t0eq]; exact ht.2) ht.1
    have hgoal_eq : gueKproc sz t1 t0 (gueGridK sz n0) Kt n l t
        = gueKbar sz t1 t0 (gueGridK sz n0) Kt n l 0 := by
      unfold gueKproc gueInterp
      rw [ite_eq_left hstep0]
    rw [hgoal_eq, hteq]
    have h0 := hperk 0 (Nat.zero_le _)
    have e0 : gridTime t1 t0 (gueGridK sz n0) n 0 = t1 n := by simp [gridTime]
    rw [e0] at h0
    refine h0.trans ?_
    have hnn : (0 : ℝ) ≤ (Nn * etaOf (m n) (t1 n))⁻¹ ^ (l - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos (t1 n) ⟨le_refl _, ht10 n⟩).le) _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hnn
  · have hstepPos : 0 < gridStep t1 t0 (gueGridK sz n0) n :=
      lt_of_le_of_ne (div_nonneg (by linarith [ht10 n]) (Nat.cast_nonneg _)) (Ne.symm hstep0)
    obtain ⟨kstar, hkstarKN, hknear, hkdom⟩ :=
      ProcK_gueTime_kstar_near hstepPos (ht10 n) t ht.1 ht.2 hKne
    have htimekstar_mem : gridTime t1 t0 (gueGridK sz n0) n kstar ∈ Set.Icc (t1 n) (t0 n) :=
      ProcK_gueTime_mem_Icc (ht10 n) hKne hkstarKN
    have hlamnear : Nn * etaOf (m n) t ≤ 2 * (Nn * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n kstar)) := by
      have hsmall : Nn * gridStep t1 t0 (gueGridK sz n0) n ≤ Nn * (1 - t0 n) * (m n).im := by
        have hstepmul := mul_le_mul_of_nonneg_left hstepN hN0.le
        rw [show Nn * etaOf (m n) (t0 n) = Nn * (1 - t0 n) * (m n).im by unfold etaOf; ring] at hstepmul
        exact hstepmul
      have hkey := ProcK_lam_near_le hN0.le hm0.le hmim1 htimekstar_mem.2 hknear hsmall
      unfold etaOf
      linarith [hkey, mul_assoc Nn (1 - t) (m n).im,
        mul_assoc Nn (1 - gridTime t1 t0 (gueGridK sz n0) n kstar) (m n).im]
    have hinvnear : (Nn * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n kstar))⁻¹
        ≤ 2 * (Nn * etaOf (m n) t)⁻¹ :=
      ProcK_inv_le_two_inv_of_le_two_mul (hlam_pos t ht) (hlam_pos _ htimekstar_mem) hlamnear
    have hkstarbound : gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar ≤
        Nn ^ (τ / 2) * (2 ^ (2 * n0) * (Nn * etaOf (m n) t)⁻¹ ^ (l - 1)) := by
      refine (hperk kstar hkstarKN).trans ?_
      have hNnn2 : (0 : ℝ) ≤ Nn ^ (τ / 2) := Real.rpow_nonneg hN0.le _
      apply mul_le_mul_of_nonneg_left _ hNnn2
      have hkstarinv_nn : (0 : ℝ) ≤ (Nn * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n kstar))⁻¹ :=
        inv_nonneg.2 (hlam_pos _ htimekstar_mem).le
      have htinv_nn : (0 : ℝ) ≤ (Nn * etaOf (m n) t)⁻¹ ^ (l - 1) :=
        pow_nonneg (inv_nonneg.2 (hlam_pos t ht).le) _
      calc (Nn * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n kstar))⁻¹ ^ (l - 1)
          ≤ (2 * (Nn * etaOf (m n) t)⁻¹) ^ (l - 1) := pow_le_pow_left₀ hkstarinv_nn hinvnear (l - 1)
        _ = 2 ^ (l - 1) * (Nn * etaOf (m n) t)⁻¹ ^ (l - 1) := by rw [mul_pow]
        _ ≤ 2 ^ (2 * n0) * (Nn * etaOf (m n) t)⁻¹ ^ (l - 1) := by
            apply mul_le_mul_of_nonneg_right _ htinv_nn
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hgueKproc_le : gueKproc sz t1 t0 (gueGridK sz n0) Kt n l t
        ≤ 2 * gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar := by
      unfold gueKproc gueInterp
      rw [ite_eq_right hstep0]
      have hdomle : ∀ k, k ∈ Finset.range (gueGridK sz n0 n + 1) →
          gueKbar sz t1 t0 (gueGridK sz n0) Kt n l k * gueTent t1 t0 (gueGridK sz n0) n k t
            ≤ gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar * gueTent t1 t0 (gueGridK sz n0) n k t := by
        intro k hk
        by_cases hpos : 0 < gueTent t1 t0 (gueGridK sz n0) n k t
        swap
        · have htent0 : gueTent t1 t0 (gueGridK sz n0) n k t = 0 :=
            le_antisymm (not_lt.1 hpos) (ProcK_gueTent_nonneg k t)
          rw [htent0, mul_zero, mul_zero]
        · have hkkstar : k ≤ kstar :=
            hkdom k (by simpa using (Finset.mem_range.mp hk : k < gueGridK sz n0 n + 1)) hpos
          exact mul_le_mul_of_nonneg_right (ProcK_gueKbar_mono sz Kt l hkkstar) (ProcK_gueTent_nonneg k t)
      calc ∑ k ∈ Finset.range (gueGridK sz n0 n + 1),
            gueKbar sz t1 t0 (gueGridK sz n0) Kt n l k * gueTent t1 t0 (gueGridK sz n0) n k t
          ≤ ∑ k ∈ Finset.range (gueGridK sz n0 n + 1),
              gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar * gueTent t1 t0 (gueGridK sz n0) n k t :=
            Finset.sum_le_sum hdomle
        _ = gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar *
              ∑ k ∈ Finset.range (gueGridK sz n0 n + 1), gueTent t1 t0 (gueGridK sz n0) n k t := by
            rw [Finset.mul_sum]
        _ ≤ gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar * 2 := by
            have hkbar_nonneg : (0 : ℝ) ≤ gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar := by
              unfold gueKbar
              exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
            apply mul_le_mul_of_nonneg_left (ProcK_gueTent_sum_le_two t hstepPos ht.1) hkbar_nonneg
        _ = 2 * gueKbar sz t1 t0 (gueGridK sz n0) Kt n l kstar := by ring
    have hcomb : gueKproc sz t1 t0 (gueGridK sz n0) Kt n l t
        ≤ 2 * (Nn ^ (τ / 2) * (2 ^ (2 * n0) * (Nn * etaOf (m n) t)⁻¹ ^ (l - 1))) :=
      hgueKproc_le.trans (mul_le_mul_of_nonneg_left hkstarbound (by norm_num))
    refine hcomb.trans ?_
    have hfin : 2 * (Nn ^ (τ / 2) * (2 ^ (2 * n0) * (Nn * etaOf (m n) t)⁻¹ ^ (l - 1)))
        = (2 ^ (2 * n0 + 1)) * Nn ^ (τ / 2) * (Nn * etaOf (m n) t)⁻¹ ^ (l - 1) := by ring
    rw [hfin]
    have hpow2N : (2 : ℝ) ^ (2 * n0 + 1) ≤ Nn ^ (τ / 2) := h2pow
    have hNpow_split : Nn ^ τ = Nn ^ (τ / 2) * Nn ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [hNpow_split]
    have htinv_nn' : (0 : ℝ) ≤ (Nn * etaOf (m n) t)⁻¹ ^ (l - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos t ht).le) _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow2N (Real.rpow_nonneg hN0.le _)) htinv_nn'

/-- At length `1`, `K̃_t = m_σ` on `[t₁, t₀]` (twin of `Hyp_Kt_one`, `HypA:712`; the primitive equation has zero right side): from
`hKinit` (the start `BAKsol`, whose 1-loops are `PropSpin m`, `baKsol_one`) and `hK` at length `1`.  Both clauses are guarded by
`0 < g n`; this is the `Kt = m` premise of `T2519_HoffBA` (the guard `0 < g n →` is the signed one). -/
theorem Hyp_Kt_oneBA {d : ℕ} (sz : Sizes d) {κ : ℝ} (hκ : 0 < κ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (n0 : ℕ)
    (hn0 : 1 ≤ n0) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)), Kt n (t1 n) I =
      BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t)
    (n : ℕ) (hg : 0 < g n) {u : ℝ} (hu : u ∈ Set.Icc (t1 n) (t0 n)) (σ : Bool) (a : Zd d (sz.L n)) :
    Kt n u ⟨[σ], [a]⟩ = mSigOf (m n) σ := by
  have hI : (⟨[σ], [a]⟩ : LoopIdx (Zd d (sz.L n))).length = 1 := rfl
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r => Kt n r ⟨[σ], [a]⟩)
    (f' := fun r => primRhsGUE d (sz.L n) (sz.W n) (Kt n r) ⟨[σ], [a]⟩) (C := 0)
    (fun r hr' => hK n hg r hr' _ rfl (by rw [hI]) (by rw [hI]; omega))
    (fun r _ => by rw [Hyp_primRhs_one _ _ hI, norm_zero]) u hu
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hmvt
  have h1 := baKsol_one d hκ hg (sz.three_le_L n) (sz.W n) (hr n) (t := t1 n)
    ⟨ht1 n, lt_of_le_of_lt (ht10 n) (ht0 n)⟩ (fun _ : Fin 1 => σ) (fun _ => a)
  have hloop : KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => a) = ⟨[σ], [a]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [hloop] at h1
  rw [hmvt, hKinit n hg, h1]
  rfl

/-- **From the RBG zero-mode premises to the one of the K lemmas** (`g = √t₀ λ`; `d ≥ 3`, `L ≥ 3`): `L^d (1 - t₁) ≤ λ²`,
`L^d (1 - t₁) ≤ 1` (`hell`, `hell1` of `RBG_Prod`) and `t₁ ≤ t₀` give `L^d (1 - t₁) ≤ 2 g²`, since `L^d ≥ 27` forces
`t₀ ≥ t₁ ≥ 26/27`, so `λ² ≤ (27/26) g²`.  A helper for the producers of rows c, d (the premise `hell` of `Hyp_Kt_detDomBA`). -/
theorem GUEHypABA_hell_of_hell {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) {t1 t0 lam : ℝ} (ht10 : t1 ≤ t0)
    (hell : (L : ℝ) ^ d * (1 - t1) ≤ lam ^ 2) (hell1 : (L : ℝ) ^ d * (1 - t1) ≤ 1) :
    (L : ℝ) ^ d * (1 - t1) ≤ 2 * (Real.sqrt t0 * lam) ^ 2 := by
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h27 : (27 : ℝ) ≤ (L : ℝ) ^ d :=
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ (L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hL3 3
      _ ≤ (L : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
  have ht1 : 26 / 27 ≤ t1 := by
    by_contra hc
    have h1 : 1 / 27 < 1 - t1 := by linarith [not_le.1 hc]
    nlinarith
  have ht0 : 0 ≤ t0 := by linarith
  rw [mul_pow, Real.sq_sqrt ht0]
  nlinarith [sq_nonneg lam]

end KBound

/-! ## 2. The grid bound at `k ≤ σ` (pathwise) -/

section HypGrid

/-- **The grid bound at `k ≤ σ`** (pathwise; twin of `Hyp_grid`, `HypA:981`): the discrete Duhamel formula with the initial term, the
martingale remainder (`hM`, `hq`), the drift (`hF`, `heG`) and the `K̃` discretization (`hdisc`), for every `t` that dominates all earlier
grid times.  The drift of `hM` is `genMatGUEOf` (the generic generator at the flow datum), split at each grid time by `loopGenGUEOf`
(`Generator:1168`, every loop length, no `3 ≤ L`, no `|E| < 2`) into `primRhsGUE (𝓛) + egtNGUEOf`; `0 < Im m` replaces `|E| < 2`. -/
theorem Hyp_gridBA {d : ℕ} (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ) (ω : PathΩ (sz.withLam 0))
    (g1 g3 g4 : ℝ → ℝ) {c Cf Ce err Λ0 : ℝ}
    (ht10 : t1 n ≤ t0 n) (hm : 0 < (m n).im) (ht0 : t0 n < 1)
    (hc : 0 ≤ c) (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce)
    (hg1 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g1 u) (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u)
    (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg1c : ContinuousOn g1 (Set.Icc (t1 n) (t0 n))) (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n 0 ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖ ≤ c * Λ0)
    (hM : ∀ k ≤ K n, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n 0 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2)
          - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
              genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j)
                (gueHBA sz g t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤
        c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) *
          (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
              (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (2 * l)))
          + (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ l))
    (hq : ∀ j < gueStopBA sz g E t1 t0 m K δ n ω,
      Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (2 * l)) ≤ g4 (gridTime t1 t0 K n j))
    (hF : ∀ j < gueStopBA sz g E t1 t0 m K δ n ω, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)))
          (loopOf x.1 x.2) -
        primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤
        Cf * g1 (gridTime t1 t0 K n j))
    (heG : ∀ j < gueStopBA sz g E t1 t0 m K δ n ω, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω)
          (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 K n j))
    (hdisc : ∀ k ≤ K n, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2) -
        (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ err)
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) {k : ℕ} (hkσ : k ≤ gueStopBA sz g E t1 t0 m K δ n ω)
    (hkt : ∀ j < k, gridTime t1 t0 K n j ≤ t) :
    gueDmaxBA sz g E t1 t0 m K Kt n l k ω ≤ (c * Λ0 + err) +
      c * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ l +
      (Cf * supOn g1 (t1 n) t + Ce * supOn g3 (t1 n) t) * (gridTime t1 t0 K n k - t1 n) +
      (c * supOn g4 (t1 n) t) * Real.sqrt (gridTime t1 t0 K n k - t1 n) := by
  set σ := gueStopBA sz g E t1 t0 m K δ n ω with hσdef
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
  have hS1 : ∀ j < k, g1 (gridTime t1 t0 K n j) ≤ S1 := fun j hj => Hyp_le_supOn hg1c ht.2 (hjmem j hj)
  have hS3 : ∀ j < k, g3 (gridTime t1 t0 K n j) ≤ S3 := fun j hj => Hyp_le_supOn hg3c ht.2 (hjmem j hj)
  have hS4 : ∀ j < k, g4 (gridTime t1 t0 K n j) ≤ S4 := fun j hj => Hyp_le_supOn hg4c ht.2 (hjmem j hj)
  have hS4n : 0 ≤ S4 := supOn_nonneg fun u hu => hg4 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS1n : 0 ≤ S1 := supOn_nonneg fun u hu => hg1 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS3n : 0 ≤ S3 := supOn_nonneg fun u hu => hg3 u ⟨hu.1, hu.2.trans ht.2⟩
  unfold gueDmaxBA
  refine ciSup_le fun x => ?_
  have hD := Hyp_duhamel_norm
    (a := fun j => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
      (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (loopOf x.1 x.2))
    (b := fun j => Kt n (gridTime t1 t0 K n j) (loopOf x.1 x.2))
    (e := fun j => egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j)
      (gueHBA sz g t1 t0 K n j ω) (loopOf x.1 x.2))
    (f := fun j => primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j)))
      (loopOf x.1 x.2))
    (g := fun j => primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2))
    hΔ0 k
  have hM' := hM k hkK x
  have hsplit : ∑ j ∈ Finset.range k, genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j)
        (gueHBA sz g t1 t0 K n j ω) (loopOf x.1 x.2) =
      ∑ j ∈ Finset.range k, (egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j)
        (gueHBA sz g t1 t0 K n j ω) (loopOf x.1 x.2) +
        primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
          (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [loopGenGUEOf d (sz.L n) (sz.W n) (m n) hm (E n) (gridTime t1 t0 K n j)
      (lt_of_le_of_lt (hkt j hj) (lt_of_le_of_lt ht.2 ht0)) (gueHBA sz g t1 t0 K n j ω)
      (gueHBA_isHermitian sz g t1 t0 K n j ω) l x.1 x.2, add_comm]
  rw [hsplit] at hM'
  have hsup : (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
      (etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
      RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (2 * l))) ≤ S4 :=
    Real.iSup_le (fun j => (hq j (lt_of_lt_of_le j.2 hkσ)).trans (hS4 j j.2)) hS4n
  have hsum : ∑ j ∈ Finset.range k,
      (‖egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω)
          (loopOf x.1 x.2)‖ +
        ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
            (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2) -
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
        (etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n j)) (2 * l)))
      + (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ l) ≤
      c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) * S4
        + (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ l) := by
    gcongr
  have hsumΔ := mul_le_mul_of_nonneg_left hsum hΔ0
  have hfin : Δ * ((k : ℝ) * (Cf * S1 + Ce * S3)) =
      (Cf * S1 + Ce * S3) * (gridTime t1 t0 K n k - t1 n) := by
    rw [← hkΔ]; ring
  have hM'' := hM'.trans hMb
  linarith

end HypGrid

/-! ## 3. Compiled nonempty instances

`d = 3`, `sz0` (`L_n = 4 (n + 1)`, `W_n = (2 (n + 1))^5`, `N_0 = 2^21`) and its BA flow datum `(g, E, m) = (BAflowLam0, BAflowEs,
BAmF)` (`BAReal` at `κ = 1/2` for every `n`, `0 < g ≤ 10` eventually).  The window: `1 - t₀ = x_n = λ_n² / (4 L_n³)`,
`t₀ - t₁ = x_n / (2 N_n)` (so `L³ (1 - t₁) ≤ λ²/2 ≤ 2 g²` since `t₀ ≥ 1/4` along the flow, and `t₀ - t₁ ≤ N^{-1/20} η_{t₀}` since
`Im m ≥ 1/2`); `τ_U = 1/20`, `n₀ = 4` (the `n₀` of the amended texts).  The primitive family is that of `gueK_existsBA` (chosen per `n`, guarded by `0 < g n`).  Every
hypothesis is discharged; for `Hyp_gridBA` the constants `c`, `C_f`, `C_e`, `err`, `g₄` are finite sums of the left sides (as in the band
instance `HypAInst`), for every path `ω`, threshold `δ` and primitive family `Kt`. -/

namespace GUEHypABAInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

private abbrev ig : ℕ → ℝ := BAflowLam0 sz0 zSeq
private abbrev iE : ℕ → ℝ := BAflowEs sz0 zSeq
private abbrev im : ℕ → ℂ := BAmF sz0 ig iE
private abbrev iN (n : ℕ) : ℝ := ((sz0.size n : ℕ) : ℝ)
private abbrev ix (n : ℕ) : ℝ := sz0.lam n ^ 2 / (4 * ((sz0.L n : ℕ) : ℝ) ^ 3)
private abbrev it0 (n : ℕ) : ℝ := 1 - ix n
private abbrev it1 (n : ℕ) : ℝ := it0 n - ix n / (2 * iN n)

private theorem GUEHypABAInst_real (n : ℕ) : BAReal 3 (sz0.L n) (ig n) (1 / 2) (iE n) (im n) :=
  BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n

private theorem GUEHypABAInst_L (n : ℕ) : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
  change (4 : ℝ) ≤ ((4 * (n + 1) : ℕ) : ℝ)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem GUEHypABAInst_N (n : ℕ) : (1 : ℝ) ≤ iN n :=
  le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (size_ge n)

private theorem GUEHypABAInst_x_pos (n : ℕ) : 0 < ix n := by
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) := by linarith [GUEHypABAInst_L n]
  have := sz0_lam_pos n
  unfold ix; positivity

private theorem GUEHypABAInst_x_le (n : ℕ) : ix n ≤ 1 / 4 := by
  have hL : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := GUEHypABAInst_L n
  have h1 := sz0_lam_L n
  have h3 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hcast : ((((sz0.L n) ^ 3 : ℕ) : ℝ)) = ((sz0.L n : ℕ) : ℝ) ^ 3 := by push_cast; ring
  rw [hcast] at h1
  have h2 : sz0.lam n ^ 2 ≤ 1 / 64 := by nlinarith [sq_nonneg (sz0.lam n)]
  unfold ix
  rw [div_le_iff₀ (by positivity)]
  nlinarith

private theorem GUEHypABAInst_t0 (n : ℕ) : 1 / 4 ≤ BAflowT0 sz0 zSeq n := by
  have h1 := mS_im_half (sz0.L n) (sz0.lam n) (sz0_lam_L n)
  have h2 := zSeq_im_le n
  have h3 := zSeq_im_pos n
  unfold BAflowT0 BAt0
  rw [BAm_zSeq n, le_div_iff₀ (by linarith)]
  linarith

private theorem GUEHypABAInst_t1_nonneg (n : ℕ) : 0 ≤ it1 n := by
  have h1 := GUEHypABAInst_x_le n
  have h2 := GUEHypABAInst_x_pos n
  have hN := GUEHypABAInst_N n
  have : ix n / (2 * iN n) ≤ ix n := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  unfold it1 it0; linarith

private theorem GUEHypABAInst_t10 (n : ℕ) : it1 n ≤ it0 n := by
  have h2 := GUEHypABAInst_x_pos n
  have hN := GUEHypABAInst_N n
  have : 0 ≤ ix n / (2 * iN n) := by positivity
  unfold it1; linarith

private theorem GUEHypABAInst_t0_lt (n : ℕ) : it0 n < 1 := by
  have := GUEHypABAInst_x_pos n; unfold it0; linarith

private theorem GUEHypABAInst_g_pos (n : ℕ) : 0 < ig n := by
  have hm : 0 < (BAm 3 (sz0.L n) (sz0.lam n) (zSeq n)).im := by
    rw [BAm_zSeq n]; linarith [mS_im_half (sz0.L n) (sz0.lam n) (sz0_lam_L n)]
  exact mul_pos (Real.sqrt_pos.mpr (BAt0_pos (zSeq_im_pos n) hm)) (sz0_lam_pos n)

private theorem GUEHypABAInst_hell (n : ℕ) : ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - it1 n) ≤ 2 * ig n ^ 2 := by
  have hx := GUEHypABAInst_x_pos n
  have hN := GUEHypABAInst_N n
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) ^ 3 := by have := GUEHypABAInst_L n; positivity
  have hg2 : ig n ^ 2 = BAflowT0 sz0 zSeq n * sz0.lam n ^ 2 := by
    unfold ig BAflowLam0
    rw [mul_pow, Real.sq_sqrt]
    have := GUEHypABAInst_t0 n
    linarith
  have hxN : ix n / (2 * iN n) ≤ ix n := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h1 : 1 - it1 n ≤ 2 * ix n := by unfold it1 it0; linarith
  have hL0 : ((sz0.L n : ℕ) : ℝ) ≠ 0 := by have := GUEHypABAInst_L n; intro h; linarith
  have h2 : ((sz0.L n : ℕ) : ℝ) ^ 3 * ix n = sz0.lam n ^ 2 / 4 := by
    unfold ix; field_simp
  have h3 := GUEHypABAInst_t0 n
  calc ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - it1 n) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 * (2 * ix n) :=
        mul_le_mul_of_nonneg_left h1 hL.le
    _ = sz0.lam n ^ 2 / 2 := by rw [← mul_assoc, mul_comm _ 2, mul_assoc, h2]; ring
    _ ≤ 2 * ig n ^ 2 := by rw [hg2]; nlinarith [sq_nonneg (sz0.lam n)]

private theorem GUEHypABAInst_h730 (n : ℕ) :
    it0 n - it1 n ≤ iN n ^ (-(1 / 20 : ℝ)) * etaOf (im n) (it0 n) := by
  have hx := GUEHypABAInst_x_pos n
  have hN := GUEHypABAInst_N n
  have hm := (GUEHypABAInst_real n).2
  have hpow : iN n ^ (-1 : ℝ) ≤ iN n ^ (-(1 / 20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  rw [Real.rpow_neg_one] at hpow
  have heta : etaOf (im n) (it0 n) = ix n * (im n).im := by unfold etaOf it0; ring
  have h1 : it0 n - it1 n = ix n / (2 * iN n) := by unfold it1; ring
  rw [h1, heta]
  have hN0 : 0 < iN n := by linarith
  calc ix n / (2 * iN n) = (iN n)⁻¹ * (ix n * (1 / 2)) := by field_simp
    _ ≤ iN n ^ (-(1 / 20 : ℝ)) * (ix n * (im n).im) := by
        apply mul_le_mul hpow (mul_le_mul_of_nonneg_left hm hx.le) (by positivity) (by positivity)

/-- The primitive family of `gueK_existsBA` at the window `[t₁_n, t₀_n]` (chosen per `n`; the clauses are guarded by `0 < g n`). -/
private theorem GUEHypABAInst_K : ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ,
    (∀ n, 0 < ig n → ∀ I : LoopIdx (Zd 3 (sz0.L n)), Kt n (it1 n) I = BAKsol 3 (sz0.L n) (sz0.W n)
      (BAMsigma 3 (sz0.L n) (BAMB 3 (sz0.L n) (ig n) (iE n : ℂ) (im n))) (PropSpin (im n)) (it1 n) I) ∧
    (∀ n, 0 < ig n → ∀ t ∈ Set.Icc (it1 n) (it0 n), ∀ I : LoopIdx (Zd 3 (sz0.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * 4 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE 3 (sz0.L n) (sz0.W n) (Kt n t) I) (Set.Icc (it1 n) (it0 n)) t) := by
  classical
  have hex := fun n (hg : 0 < ig n) => gueK_existsBA 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) hg
    (show (0 : ℝ) < 1 / 2 by norm_num) (GUEHypABAInst_real n) (GUEHypABAInst_t1_nonneg n) (GUEHypABAInst_t10 n)
    (GUEHypABAInst_t0_lt n) (4 * 4)
  refine ⟨fun n => if h : 0 < ig n then (hex n h).choose else fun _ _ => 0, fun n h I => ?_, fun n h t ht I hI h1 h2 => ?_⟩
  · simp only [h, ↓reduceDIte]; exact (hex n h).choose_spec.1 I
  · simp only [h, ↓reduceDIte]; exact (hex n h).choose_spec.2.1 t ht I hI h1 h2

/-- `Hyp_Kt_detDomBA` at the instance: `‖K̃_{t,I}‖ ≤ N^ε (N η_t)^{-|I|+1}` on `[t₁, t₀]`, `2 ≤ |I| ≤ 4`, for every `ε > 0`, eventually. -/
example : ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ,
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (it1 n) (it0 n), ∀ I : LoopIdx (Zd 3 (sz0.L n)),
      I.WF → 2 ≤ I.length → I.length ≤ 2 * 4 →
      ‖Kt n s I‖ ≤ iN n ^ ε * (iN n * etaOf (im n) s)⁻¹ ^ (I.length - 1) := by
  obtain ⟨Kt, hKinit, hK⟩ := GUEHypABAInst_K
  exact ⟨Kt, Hyp_Kt_detDomBA le_rfl sz0 (κ := 1 / 2) (Λ := (1 / 10 : ℝ)⁻¹) (τU := 1 / 20) (by norm_num) (by norm_num)
    (by norm_num) 4 GUEHypABAInst_real (BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0)
    GUEHypABAInst_t1_nonneg GUEHypABAInst_t10 GUEHypABAInst_t0_lt (tendsto_natCast_atTop_iff.mp sz0_tendsto)
    (Eventually.of_forall GUEHypABAInst_h730) (Eventually.of_forall GUEHypABAInst_hell) Kt hKinit hK⟩

/-- `gueKproc_detDomBA` at the instance. -/
example : ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ,
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc it1 it0 n) (l : Set.Icc 2 (2 * 4)),
      gueKproc sz0 it1 it0 (gueGridK sz0 4) Kt n (l : ℕ) (t : ℝ) ≤
        iN n ^ ε * (iN n * etaOf (im n) (t : ℝ))⁻¹ ^ ((l : ℕ) - 1) := by
  obtain ⟨Kt, hKinit, hK⟩ := GUEHypABAInst_K
  exact ⟨Kt, gueKproc_detDomBA le_rfl sz0 (κ := 1 / 2) (Λ := (1 / 10 : ℝ)⁻¹) (τU := 1 / 20) (by norm_num) (by norm_num)
    (by norm_num) 4 GUEHypABAInst_real (BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0)
    GUEHypABAInst_t1_nonneg GUEHypABAInst_t10 GUEHypABAInst_t0_lt (tendsto_natCast_atTop_iff.mp sz0_tendsto)
    (Eventually.of_forall GUEHypABAInst_h730) (Eventually.of_forall GUEHypABAInst_hell) Kt hKinit hK⟩

/-- `Hyp_Kt_oneBA` at the instance, `n = 0`, `u = t₁_0`: the 1-loops of the primitive family are `m_σ`. -/
example : ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ, ∀ (σ : Bool) (a : Zd 3 (sz0.L 0)),
    Kt 0 (it1 0) ⟨[σ], [a]⟩ = mSigOf (im 0) σ := by
  obtain ⟨Kt, hKinit, hK⟩ := GUEHypABAInst_K
  exact ⟨Kt, fun σ a => Hyp_Kt_oneBA sz0 (κ := 1 / 2) (by norm_num) 4 (by norm_num) Kt GUEHypABAInst_real
    GUEHypABAInst_t1_nonneg GUEHypABAInst_t10 GUEHypABAInst_t0_lt hKinit hK 0 (GUEHypABAInst_g_pos 0)
    ⟨le_rfl, GUEHypABAInst_t10 0⟩ σ a⟩

/-! ### `Hyp_gridBA` at the instance, every hypothesis discharged

`n = 0`, `l = 2`, the grid `K = 4`, `t = t₀`, every path `ω`, every threshold `δ`, every primitive family `Kt` (the theorem holds for any).
The constants of the theorem are chosen as finite sums of the left sides (`k, j ≤ 4`, the labels `x ∈ (Fin 2 → Bool) × (Fin 2 → Zd 3 4)`):
`c = S₀ + Σ_k Σ_x AM_k(x)/sc_k`, `Λ₀ = 1`, `C_f`, `C_e`, `g₄ ≡ Σ_j Q_j`, `err` the maximal discretization error, `g₁ = g₃ ≡ 1`
(the band instance `HypAInst` does the same). -/

private abbrev X2 : Type := (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L 0))
private abbrev uj (j : ℕ) : ℝ := gridTime it1 it0 (fun _ => 4) 0 j
private abbrev Hj (ω : PathΩ (sz0.withLam 0)) (j : ℕ) := gueHBA sz0 ig it1 it0 (fun _ => 4) 0 j ω
private abbrev Lj (ω : PathΩ (sz0.withLam 0)) (j : ℕ) (x : X2) : ℂ := loopL 3 (sz0.L 0) (sz0.W 0)
  (blockMat 3 (sz0.L 0) (sz0.W 0) (Hj ω j)) (ztOf (im 0) (iE 0) (uj j)) (loopOf x.1 x.2)
private abbrev scj (j : ℕ) : ℝ := (iN 0 * etaOf (im 0) (uj j))⁻¹ ^ 2
private abbrev AMj (ω : PathΩ (sz0.withLam 0)) (j : ℕ) (x : X2) : ℝ :=
  ‖Lj ω j x - Lj ω 0 x - (gridStep it1 it0 (fun _ => 4) 0 : ℂ) * ∑ i ∈ Finset.range j,
    genMatGUEOf 3 (sz0.L 0) (sz0.W 0) (im 0) (iE 0) (uj i) (Hj ω i) (loopOf x.1 x.2)‖
private abbrev AFj (ω : PathΩ (sz0.withLam 0)) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ) (j : ℕ) (x : X2) : ℝ :=
  ‖primRhsGUE 3 (sz0.L 0) (sz0.W 0) (loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (Hj ω j))
    (ztOf (im 0) (iE 0) (uj j))) (loopOf x.1 x.2) - primRhsGUE 3 (sz0.L 0) (sz0.W 0) (Kt 0 (uj j)) (loopOf x.1 x.2)‖
private abbrev AEj (ω : PathΩ (sz0.withLam 0)) (j : ℕ) (x : X2) : ℝ :=
  ‖egtNGUEOf 3 (sz0.L 0) (sz0.W 0) (im 0) (iE 0) (uj j) (Hj ω j) (loopOf x.1 x.2)‖
private abbrev ADj (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ) (k : ℕ) (x : X2) : ℝ :=
  ‖Kt 0 (uj k) (loopOf x.1 x.2) - Kt 0 (uj 0) (loopOf x.1 x.2) - (gridStep it1 it0 (fun _ => 4) 0 : ℂ) *
    ∑ j ∈ Finset.range k, primRhsGUE 3 (sz0.L 0) (sz0.W 0) (Kt 0 (uj j)) (loopOf x.1 x.2)‖
private abbrev Qj (ω : PathΩ (sz0.withLam 0)) (j : ℕ) : ℝ :=
  Real.sqrt ((iN 0)⁻¹ * (etaOf (im 0) (uj j))⁻¹ ^ 2 * RBM.Ind.loopMax 3 (sz0.L 0) (sz0.W 0)
    (blockMat 3 (sz0.L 0) (sz0.W 0) (Hj ω j)) (ztOf (im 0) (iE 0) (uj j)) (2 * 2))

/-- A nonnegative term is at most the double sum over `j < 5` and `x`. -/
private theorem GUEHypABAInst_dsum (f : ℕ → X2 → ℝ) (hf : ∀ j x, 0 ≤ f j x) {j : ℕ} (hj : j < 5) (x : X2) :
    f j x ≤ ∑ j ∈ Finset.range 5, ∑ x, f j x :=
  (Finset.single_le_sum (f := f j) (fun _ _ => hf j _) (Finset.mem_univ x)).trans
    (Finset.single_le_sum (f := fun j => ∑ x, f j x)
      (fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _) (Finset.mem_range.2 hj))

private theorem GUEHypABAInst_scj_pos {k : ℕ} (hk : k ≤ 4) : 0 < scj k := by
  have hu := Hyp_time_le (K := fun _ => 4) (GUEHypABAInst_t10 0) (by norm_num) (k := k) hk
  have hη : 0 < etaOf (im 0) (uj k) := mul_pos (by linarith [GUEHypABAInst_t0_lt 0]) (GUEHypABAInst_real 0).1.1
  have hN : 0 < iN 0 := by linarith [GUEHypABAInst_N 0]
  positivity

private noncomputable def S0 (ω : PathΩ (sz0.withLam 0)) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ) : ℝ :=
  ∑ x : X2, ‖Lj ω 0 x - Kt 0 (uj 0) (loopOf x.1 x.2)‖
private noncomputable def c0 (ω : PathΩ (sz0.withLam 0)) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ) : ℝ :=
  S0 ω Kt + ∑ k ∈ Finset.range 5, ∑ x, AMj ω k x / scj k

private theorem GUEHypABAInst_AMsc_nonneg (ω : PathΩ (sz0.withLam 0)) : ∀ k x, 0 ≤ AMj ω k x / scj k :=
  fun _ _ => div_nonneg (norm_nonneg _) (by positivity)

private theorem GUEHypABAInst_S0_nonneg (ω : PathΩ (sz0.withLam 0)) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ) :
    0 ≤ S0 ω Kt := Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem GUEHypABAInst_c0_nonneg (ω : PathΩ (sz0.withLam 0)) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ) :
    0 ≤ c0 ω Kt :=
  add_nonneg (GUEHypABAInst_S0_nonneg ω Kt)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => GUEHypABAInst_AMsc_nonneg ω _ _)

/-- `Hyp_gridBA` at the instance for every `ω`, `δ`, `Kt`: constants (independent of `k`) exist such that the conclusion holds for every
`k ≤ gueStopBA`, with every hypothesis of the theorem discharged. -/
example (ω : PathΩ (sz0.withLam 0)) (δ : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ) :
    ∃ c Cf Ce err Λ0 G4 : ℝ, ∀ k ≤ gueStopBA sz0 ig iE it1 it0 im (fun _ => 4) δ 0 ω,
      gueDmaxBA sz0 ig iE it1 it0 im (fun _ => 4) Kt 0 2 k ω ≤ (c * Λ0 + err) +
        c * (iN 0 * etaOf (im 0) (gridTime it1 it0 (fun _ => 4) 0 k))⁻¹ ^ 2 +
        (Cf * supOn (fun _ => (1 : ℝ)) (it1 0) (it0 0) + Ce * supOn (fun _ => (1 : ℝ)) (it1 0) (it0 0)) *
          (gridTime it1 it0 (fun _ => 4) 0 k - it1 0) +
        (c * supOn (fun _ => G4) (it1 0) (it0 0)) * Real.sqrt (gridTime it1 it0 (fun _ => 4) 0 k - it1 0) := by
  have hstop : gueStopBA sz0 ig iE it1 it0 im (fun _ => 4) δ 0 ω ≤ 4 := firstHit_le _ _ _ ω
  refine ⟨c0 ω Kt, ∑ j ∈ Finset.range 5, ∑ x, AFj ω Kt j x, ∑ j ∈ Finset.range 5, ∑ x, AEj ω j x,
    ∑ k ∈ Finset.range 5, ∑ x, ADj Kt k x, 1, ∑ j ∈ Finset.range 5, Qj ω j, fun k hk => ?_⟩
  refine Hyp_gridBA sz0 ig iE it1 it0 im (fun _ => 4) δ Kt 0 2 ω (fun _ => 1) (fun _ => 1)
    (fun _ => ∑ j ∈ Finset.range 5, Qj ω j) (c := c0 ω Kt) (Λ0 := 1)
    (Cf := ∑ j ∈ Finset.range 5, ∑ x, AFj ω Kt j x) (Ce := ∑ j ∈ Finset.range 5, ∑ x, AEj ω j x)
    (err := ∑ k ∈ Finset.range 5, ∑ x, ADj Kt k x) (GUEHypABAInst_t10 0) (GUEHypABAInst_real 0).1.1
    (GUEHypABAInst_t0_lt 0) (GUEHypABAInst_c0_nonneg ω Kt)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) continuousOn_const continuousOn_const
    continuousOn_const ?_ ?_ ?_ ?_ ?_ ?_ (t := it0 0) ⟨GUEHypABAInst_t10 0, le_rfl⟩ (k := k) hk
    (fun j hj => Hyp_time_le (K := fun _ => 4) (GUEHypABAInst_t10 0) (by norm_num) (by omega))
  · intro x
    rw [mul_one, c0]
    exact (Finset.single_le_sum (f := fun x : X2 => ‖Lj ω 0 x - Kt 0 (uj 0) (loopOf x.1 x.2)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ x)).trans (le_add_of_nonneg_right
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => GUEHypABAInst_AMsc_nonneg ω _ _))
  · intro k hk x
    have hs := GUEHypABAInst_scj_pos (k := k) hk
    have h1 : AMj ω k x / scj k ≤ c0 ω Kt := (GUEHypABAInst_dsum (fun k x => AMj ω k x / scj k)
      (GUEHypABAInst_AMsc_nonneg ω) (Nat.lt_succ_of_le hk) x).trans
        (le_add_of_nonneg_left (GUEHypABAInst_S0_nonneg ω Kt))
    have hX : 0 ≤ Real.sqrt (uj k - it1 0) * ⨆ j : Fin k, Qj ω j :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.iSup_nonneg fun _ => Real.sqrt_nonneg _)
    calc AMj ω k x = AMj ω k x / scj k * scj k := (div_mul_cancel₀ _ hs.ne').symm
      _ ≤ c0 ω Kt * scj k := mul_le_mul_of_nonneg_right h1 hs.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (GUEHypABAInst_c0_nonneg ω Kt)
  · intro j hj
    exact Finset.single_le_sum (f := Qj ω) (fun _ _ => Real.sqrt_nonneg _)
      (Finset.mem_range.2 (by omega))
  · intro j hj x
    rw [mul_one]
    exact GUEHypABAInst_dsum (AFj ω Kt) (fun _ _ => norm_nonneg _) (by omega) x
  · intro j hj x
    rw [mul_one]
    exact GUEHypABAInst_dsum (AEj ω) (fun _ _ => norm_nonneg _) (by omega) x
  · intro k hk x
    exact GUEHypABAInst_dsum (ADj Kt) (fun _ _ => norm_nonneg _) (by omega) x

/-- `GUEHypABA_hell_of_hell` at numbers: `d = 3`, `L = 4`, `λ = 1/10`, `1 - t₁ = 10^{-4}` (`L³ (1 - t₁) = 0.0064 ≤ λ² = 0.01 ≤ 1`),
`t₀ = 0.99995`. -/
example : (((4 : ℕ) : ℝ)) ^ 3 * (1 - 9999 / 10000) ≤ 2 * (Real.sqrt (99995 / 100000) * (1 / 10)) ^ 2 :=
  GUEHypABA_hell_of_hell (d := 3) (L := 4) le_rfl (by norm_num) (t1 := 9999 / 10000) (t0 := 99995 / 100000)
    (lam := 1 / 10) (by norm_num) (by norm_num) (by norm_num)

end GUEHypABAInst

end RBM.BA

end
