/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Proc

/-!
# The deterministic bound on `K̃` on the GUE-phase grid, `d ≥ 3` (T2323, UN-31b)

Port of RBM2D `Universality/GUEPhase/Proc.lean:862-1424` at `81fca44` (sections `KprocDom`,
`KprocInput`: `gueKproc_detDom`); the first cut `:1-860` is the merged `GUEPhase/Proc.lean`
(T2322, UN-31a).  Paper: the GUE phase of Thm 2.4 (`paper/tex/1_2_Intro_model_result.tex:566-570`,
"essentially identical to [YY_25, Theorem 2.6]"); (7.30), (7.32), (7.36) are those of [YY_25] §7.2
(`GUEPhase/Grid.lean` header).

`gueKproc_detDom` is `K̃ ≺ (N η_t)^{-(m-1)}` for the interpolated grid running maximum `gueKproc`,
`N = sz.size n = (W L)^d`, in the explicit form `∀ ε > 0, ∀ᶠ n, … ≤ N^ε (N η_t)^{-(m-1)}`.
The bootstrap (7.36) (`eq736`) is applied at each `n` with `A = N^{τ'}`; the three index-scale
thresholds are transferred along `sz.size` (`Tendsto sz.size atTop atTop`).

The one adaptation (DECISIONS §141).  RBM2D's `Proc_initial` bounds `‖K̃_{t₁}‖` by
`KLoop.Kbound_prec_uncond` and converts `KLoop.Mt` into `gueScale` (`kloop_Mt_eq`, `scaleM`,
`ellT_eq_L`); none of these has an RBM3D twin.  At `d ≥ 3` the initial values are the band K-loops
`STKloop sz n (E n) (t₁ n)` (`hKinit`), their bound is the pin `sz.STKbound E` (new hypothesis
`hKb`, as T2153a `Induction/GridEnvelopeN.lean:36-41`; proved under the flow by `stKbound_of_flow`,
`Loop/KLFinal.lean:302`), and the conversion `Bctl n t₁ ≤ 2 (N η_{t₁})⁻¹` needs
`(ilambda² + x)⁻¹ ≤ (L^d x)⁻¹`, i.e. **`L^d (1 - t₁) ≤ ilambda²`** (`hell`, the zero-mode regime;
RBM2D's `L² (1 - t₁) ≤ 1` is the `d = 2`, `ilambda = 1` case; the literal `ℓ_{t₁} = L` condition
`L² (1 - t₁) ≤ ilambda²` would lose a factor `L^{d-2}` that `N^ε` does not absorb).  The `≺` of a
deterministic left side is unfolded to "for every `ε`, eventually `≤ N^ε × RHS`" (the bad event of
`StochDomAt` is empty once `N ≥ 2`).  Everything else is dimension-free; renaming as in T2322
(`Z2 L ↦ Zd d L`, `d.size ↦ sz.size`, `LoopIdx ↦ RBM.Loop.LoopIdx`, `spectralM ↦ mE`).
Helpers are `private` with the prefix `ProcK_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### `gueKproc_detDom`: the deterministic bound on `K̃`, interpolated, on the size scale -/

/-- A tent is nonnegative (private twin of the merged private `Proc_gueTent_nonneg`). -/
private theorem ProcK_gueTent_nonneg {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (k : ℕ) (t : ℝ) :
    0 ≤ gueTent t1 t0 K n k t :=
  le_max_left _ _

/-- A value of a function on a finite type is below its supremum. -/
private theorem ProcK_le_ciSup_finite_aux {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) i

/-- The grid times are nondecreasing in the index. -/
private theorem ProcK_gridTime_mono {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (ht10 : t1 n ≤ t0 n)
    {i j : ℕ} (hij : i ≤ j) : gridTime t1 t0 K n i ≤ gridTime t1 t0 K n j := by
  have hstep0 : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold gridTime
  nlinarith [hstep0]

section KprocDom

/-- Two nearby continuum points give comparable values of the (affine, decreasing) scale
`lam n t = M (1 - t) (Im m)`, provided the gap is dominated by the value at the right endpoint
`t0`. -/
private theorem ProcK_lam_near_le {M im0 t t' t0 Δ : ℝ} (hM : 0 ≤ M) (him0 : 0 ≤ im0)
    (him1 : im0 ≤ 1) (ht' : t' ≤ t0) (hclose : |t - t'| ≤ Δ)
    (hsmall : M * Δ ≤ M * (1 - t0) * im0) :
    M * (1 - t) * im0 ≤ 2 * (M * (1 - t') * im0) := by
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) hclose
  have hMim0 : 0 ≤ M * im0 := mul_nonneg hM him0
  have hLt0t' : M * (1 - t0) * im0 ≤ M * (1 - t') * im0 := by
    have h : M * im0 * (t0 - t') ≥ 0 := mul_nonneg hMim0 (by linarith)
    nlinarith [h]
  have habs1 := abs_le.mp hclose
  have hb0 : M * im0 * (t - t') ≤ M * im0 * Δ := mul_le_mul_of_nonneg_left habs1.2 hMim0
  have hb1 : M * im0 * (t - t') ≤ M * Δ := by
    have hstep : M * im0 * Δ ≤ M * Δ := by
      have hle : M * im0 ≤ M * 1 := mul_le_mul_of_nonneg_left him1 hM
      nlinarith [mul_le_mul_of_nonneg_right hle hΔ0]
    linarith [hb0, hstep]
  nlinarith [hb1, hsmall, hLt0t']

variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}

/-- At most two grid tents are nonzero at a continuum point, and each is `≤ 1`, so the whole
partition of unity is `≤ 2`. -/
private theorem ProcK_gueTent_sum_le_two (t : ℝ) (hstep : 0 < gridStep t1 t0 K n)
    (ht1 : t1 n ≤ t) :
    ∑ k ∈ Finset.range (K n + 1), gueTent t1 t0 K n k t ≤ 2 := by
  set Δ := gridStep t1 t0 K n with hΔdef
  set s := (t - t1 n) / Δ with hsdef
  set k0 : ℕ := ⌊s⌋₊ with hk0def
  have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (by linarith) hstep.le
  have hzero : ∀ k ∈ Finset.range (K n + 1), k ≠ k0 → k ≠ k0 + 1 →
      gueTent t1 t0 K n k t = 0 := by
    intro k _ hk1 hk2
    unfold gueTent gridTime
    rw [← hΔdef]
    have hval : t - (t1 n + (k : ℝ) * Δ) = Δ * (s - k) := by rw [hsdef]; field_simp; ring
    rw [hval, abs_mul, abs_of_pos hstep]
    have hkcase : k < k0 ∨ k0 + 1 < k := by omega
    rcases hkcase with hlt | hgt
    · have h1 : (k : ℝ) + 1 ≤ (k0 : ℝ) := by exact_mod_cast hlt
      have h2 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have habsk : |s - (k : ℝ)| = s - (k : ℝ) := abs_of_nonneg (by linarith)
      have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
      rw [mul_div_cancel_left₀ _ hstep.ne']
      exact max_eq_left hgoal
    · have h1 : (k0 : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgt
      have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
      have habsk : |s - (k : ℝ)| = (k : ℝ) - s := by
        rw [abs_of_neg (by linarith : s - (k : ℝ) < 0)]; ring
      have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
      rw [mul_div_cancel_left₀ _ hstep.ne']
      exact max_eq_left hgoal
  have hsub : ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1))
      ⊆ Finset.range (K n + 1) := Finset.filter_subset _ _
  have heq : ∑ k ∈ Finset.range (K n + 1), gueTent t1 t0 K n k t
      = ∑ k ∈ (Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1),
          gueTent t1 t0 K n k t := by
    refine (Finset.sum_subset hsub ?_).symm
    intro k hk hk'
    simp only [Finset.mem_filter, not_and, not_or] at hk'
    exact hzero k hk (hk' hk).1 (hk' hk).2
  rw [heq]
  have hcard : ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card ≤ 2 := by
    calc ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card
        ≤ ({k0, k0 + 1} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro k hk
          simp only [Finset.mem_filter] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hk.2
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  calc ∑ k ∈ (Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1), gueTent t1 t0 K n k t
      ≤ ∑ _k ∈ (Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        unfold gueTent
        exact max_le (by norm_num)
          (by linarith [div_nonneg (abs_nonneg (t - gridTime t1 t0 K n k)) hstep.le])
    _ = ((Finset.range (K n + 1)).filter (fun k => k = k0 ∨ k = k0 + 1)).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 2 := by exact_mod_cast hcard

/-- `b⁻¹ ≤ 2a⁻¹` from `a ≤ 2b` (elementary real-analysis helper). -/
private theorem ProcK_inv_le_two_inv_of_le_two_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ 2 * b) : b⁻¹ ≤ 2 * a⁻¹ := by
  rw [show (2 : ℝ) * a⁻¹ = 2 / a by ring, inv_eq_one_div, div_le_div_iff₀ hb ha]
  linarith

/-- `gueKbar` is nondecreasing in the grid index (a running maximum). -/
private theorem ProcK_gueKbar_mono (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (m : ℕ) {k k' : ℕ}
    (hkk' : k ≤ k') :
    gueKbar sz t1 t0 K Kt n m k ≤ gueKbar sz t1 t0 K Kt n m k' := by
  unfold gueKbar
  apply ciSup_le
  intro j
  exact ProcK_le_ciSup_finite_aux
    (fun j' : Fin (k' + 1) => ⨆ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
      ‖Kt n (gridTime t1 t0 K n j') (loopOf x.1 x.2)‖)
    ⟨j, by omega⟩

/-- Every grid time with index `≤ K n` lies in `[t1 n, t0 n]`. -/
private theorem ProcK_gueTime_mem_Icc (ht10' : t1 n ≤ t0 n) (hKne : K n ≠ 0) {k : ℕ}
    (hk : k ≤ K n) : gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n) := by
  refine ⟨?_, ?_⟩
  · have h0 := ProcK_gridTime_mono (K := K) ht10' (Nat.zero_le k)
    have e : gridTime t1 t0 K n 0 = t1 n := by simp [gridTime]
    rwa [e] at h0
  · have h1 := ProcK_gridTime_mono (K := K) ht10' hk
    rwa [gridTime_last t1 t0 K n hKne] at h1

/-- There is a grid index `kstar ≤ K n` within one step of any `t ∈ [t1 n, t0 n]`, which
dominates (in index) every grid index whose tent is nonzero at `t`. -/
private theorem ProcK_gueTime_kstar_near (hstep : 0 < gridStep t1 t0 K n) (_ht10' : t1 n ≤ t0 n)
    (t : ℝ) (htlo : t1 n ≤ t) (hthi : t ≤ t0 n) (hKne : K n ≠ 0) :
    ∃ kstar : ℕ, kstar ≤ K n ∧ |t - gridTime t1 t0 K n kstar| ≤ gridStep t1 t0 K n ∧
      ∀ k : ℕ, k ≤ K n → gueTent t1 t0 K n k t > 0 → k ≤ kstar := by
  set Δ := gridStep t1 t0 K n with hΔdef
  set s := (t - t1 n) / Δ with hsdef
  set k0 : ℕ := ⌊s⌋₊ with hk0def
  have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (by linarith) hstep.le
  have hKNne0 : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hKne
  have hΔKN : Δ * (K n : ℝ) = t0 n - t1 n := by
    rw [hΔdef]; unfold gridStep; field_simp
  have hsKN : s ≤ (K n : ℝ) := by
    rw [hsdef, div_le_iff₀ hstep]
    linarith [hΔKN, hthi]
  have hk0KN : k0 ≤ K n := by
    have := Nat.floor_le hs0
    have hle : (k0 : ℝ) ≤ (K n : ℝ) := le_trans this hsKN
    exact_mod_cast hle
  refine ⟨min (k0 + 1) (K n), min_le_right _ _, ?_, ?_⟩
  · by_cases hcase : k0 + 1 ≤ K n
    · rw [min_eq_left hcase]
      have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
      have h1 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have htimeeq : gridTime t1 t0 K n (k0 + 1) - t = Δ * ((k0 : ℝ) + 1 - s) := by
        unfold gridTime; rw [← hΔdef, hsdef]; push_cast; field_simp; ring
      have hnn : 0 ≤ (k0 : ℝ) + 1 - s := by linarith
      have hle1 : (k0 : ℝ) + 1 - s ≤ 1 := by linarith
      rw [abs_sub_comm, htimeeq, abs_of_nonneg (by positivity)]
      nlinarith [hstep.le]
    · have hk0eq : k0 = K n := by omega
      rw [min_eq_right (by omega : K n ≤ k0 + 1)]
      have h1 : (k0 : ℝ) ≤ s := Nat.floor_le hs0
      have h1' : (K n : ℝ) ≤ s := by rw [← hk0eq]; exact h1
      have hseq : s = (K n : ℝ) := le_antisymm hsKN h1'
      have hts : t - t1 n = Δ * (K n : ℝ) := by
        rw [hsdef] at hseq; field_simp at hseq; linarith
      have htimeeq : gridTime t1 t0 K n (K n) = t1 n + Δ * (K n : ℝ) := by
        unfold gridTime; rw [← hΔdef]; ring
      rw [htimeeq]
      have hteq : t = t1 n + Δ * (K n : ℝ) := by linarith
      rw [hteq]
      simp [hstep.le]
  · intro k hkKN hkpos
    by_contra hcon
    have hgt : k0 + 1 < k := by omega
    apply absurd hkpos (not_lt.2 (le_of_eq ?_))
    unfold gueTent gridTime
    rw [← hΔdef]
    have hval : t - (t1 n + (k : ℝ) * Δ) = Δ * (s - k) := by rw [hsdef]; field_simp; ring
    rw [hval, abs_mul, abs_of_pos hstep]
    have h1 : (k0 : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgt
    have h2 : s < (k0 : ℝ) + 1 := Nat.lt_floor_add_one s
    have habsk : |s - (k : ℝ)| = (k : ℝ) - s := by
      rw [abs_of_neg (by linarith : s - (k : ℝ) < 0)]; ring
    have hgoal : (1 : ℝ) - |s - (k : ℝ)| ≤ 0 := by rw [habsk]; linarith
    rw [mul_div_cancel_left₀ _ hstep.ne']
    exact max_eq_left hgoal

/-- The per-grid-index bound on `gueKbar` obtained from a pointwise bound `hbase` at fixed `n`,
using that the bound is monotone increasing in the grid index. -/
private theorem ProcK_gueKbar_le_of_hbase (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n n0 m : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (lam : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ht10n : t1 n ≤ t0 n) (hKne : K n ≠ 0)
    (hlam_pos : ∀ t ∈ Set.Icc (t1 n) (t0 n), 0 < lam t)
    (hlam_anti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ t ∈ Set.Icc (t1 n) (t0 n), u ≤ t →
      lam t ≤ lam u)
    (hbase : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length →
      I.length ≤ 2 * n0 → ‖Kt n t I‖ ≤ A * (lam t)⁻¹ ^ (I.length - 1))
    (hm2 : 2 ≤ m) (hm2n0 : m ≤ 2 * n0) (k : ℕ) (hk : k ≤ K n) :
    gueKbar sz t1 t0 K Kt n m k ≤ A * (lam (gridTime t1 t0 K n k))⁻¹ ^ (m - 1) := by
  unfold gueKbar
  apply ciSup_le
  intro j
  apply ciSup_le
  intro x
  have hjk : (j : ℕ) ≤ k := by omega
  have htimej_mem : gridTime t1 t0 K n j ∈ Set.Icc (t1 n) (t0 n) :=
    ProcK_gueTime_mem_Icc ht10n hKne (by omega)
  have htimek_mem : gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n) :=
    ProcK_gueTime_mem_Icc ht10n hKne hk
  have hIlen : (loopOf x.1 x.2 : RBM.Loop.LoopIdx (Zd d (sz.L n))).length = m := by
    simp [loopOf, RBM.Loop.LoopIdx.length]
  have hIWF : (loopOf x.1 x.2 : RBM.Loop.LoopIdx (Zd d (sz.L n))).WF := by
    simp [loopOf, RBM.Loop.LoopIdx.WF]
  have hbound := hbase _ htimej_mem (loopOf x.1 x.2) hIWF (by omega) (by omega)
  rw [hIlen] at hbound
  refine hbound.trans ?_
  have hle : lam (gridTime t1 t0 K n k) ≤ lam (gridTime t1 t0 K n j) :=
    hlam_anti _ htimej_mem _ htimek_mem (ProcK_gridTime_mono ht10n hjk)
  have hinvle : (lam (gridTime t1 t0 K n j))⁻¹ ^ (m - 1)
      ≤ (lam (gridTime t1 t0 K n k))⁻¹ ^ (m - 1) :=
    pow_le_pow_left₀ (inv_nonneg.2 (hlam_pos _ htimej_mem).le)
      (inv_anti₀ (hlam_pos _ htimek_mem) hle) (m - 1)
  exact mul_le_mul_of_nonneg_left hinvle hA

end KprocDom

/-! #### The size-scale input: `K̃` at `t₁` and the bootstrap (7.36) -/

section KprocInput

private theorem ProcK_size_pos (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.size n := by
    unfold Sizes.size
    have hW := sz.W_pos n
    have hL := sz.three_le_L n
    positivity
  exact_mod_cast h1

private theorem ProcK_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : 0 < sz.size n := by
    unfold Sizes.size
    have hW := sz.W_pos n
    have hL := sz.three_le_L n
    positivity
  exact_mod_cast h1

private theorem ProcK_etaT_nonneg {e t : ℝ} (ht : t ≤ 1) : 0 ≤ etaT e t := by
  unfold etaT
  have h2 : 0 ≤ (mE e).im := by rw [mE_im]; positivity
  nlinarith

private theorem ProcK_etaT_anti (e : ℝ) {u t : ℝ} (hut : u ≤ t) : etaT e t ≤ etaT e u := by
  unfold etaT
  have h2 : 0 ≤ (mE e).im := by rw [mE_im]; positivity
  nlinarith

private theorem ProcK_im_le_one (e : ℝ) : (mE e).im ≤ 1 := by
  rw [mE_im]
  have : Real.sqrt (4 - e ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg e]⟩
  linarith

private theorem ProcK_gueScale_pos {κ : ℝ} {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ)
    (n : ℕ) {t : ℝ} (ht : t < 1) : 0 < gueScale sz E n t := by
  have h2 : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  unfold gueScale
  exact mul_pos (ProcK_size_pos sz n) (etaT_pos h2 ht)

private theorem ProcK_ofFn_getD {α : Type*} (l : List α) (dflt : α) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i dflt) = l := by
  subst h
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp

/-- A well-formed loop is `loopOf` of its own signs and labels (RBM2D `Proc_loopOf_eq` `:1120`). -/
private theorem ProcK_loopOf_eq {d L : ℕ} [NeZero L] (J : RBM.Loop.LoopIdx (Zd d L)) (hJ : J.WF) :
    loopOf (fun i : Fin J.length => J.σ.getD i false)
      (fun i : Fin J.length => J.a.getD i (0 : Zd d L)) = J := by
  obtain ⟨σ', a'⟩ := J
  simp only [RBM.Loop.LoopIdx.WF] at hJ
  simp only [loopOf, RBM.Loop.LoopIdx.length]
  rw [ProcK_ofFn_getD σ' false a'.length hJ, ProcK_ofFn_getD a' 0 a'.length rfl]

/-- The deterministic content of `STKbound` at one time sequence `τ`: `≺` of a deterministic
quantity is a deterministic inequality (the bad event is `∅` or the whole space, and
`P(bad) ≤ N^{-1} < 1` once `N ≥ 2`; cf. the merged private `gdn_STKbound_win`). -/
private theorem ProcK_stKbound_eventually {E : ℕ → ℝ} (hKb : sz.STKbound E)
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
private theorem ProcK_Bctl_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hell : ((sz.L n : ℕ) : ℝ) ^ d * (1 - t) ≤ sz.lam n ^ 2) :
    sz.Bctl n t ≤ 2 * (((sz.size n : ℕ) : ℝ) * etaT E t)⁻¹ := by
  have hx : 0 < 1 - t := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := ProcK_size_pos sz n
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have hηpos : 0 < etaT E t := etaT_pos hE ht
  have hηle : etaT E t ≤ 1 - t := by
    unfold etaT
    calc (1 - t) * (mE E).im ≤ (1 - t) * 1 :=
          mul_le_mul_of_nonneg_left (ProcK_im_le_one E) hx.le
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
the band K-loop and the conversion `ProcK_Bctl_le` (`hell`); the `≺` is unfolded
(`ProcK_stKbound_eventually`), the finitely many lengths are intersected, and
`Tendsto sz.size atTop atTop` turns the `∀ᶠ` along `sz.size` into `∀ᶠ n`.  (RBM2D `Proc_initial`
`:1133`, from `Kbound_prec_uncond`.) -/
private theorem ProcK_initial {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ}
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
      ProcK_stKbound_eventually sz hKb hsz t1 ht1 (fun n => lt_of_le_of_lt (ht10 n) (ht0 n)) ℓ
        (by have := (Finset.mem_Icc.1 hℓ).1; omega) (half_pos hτ')
  have hpow : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (2 * n0) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) :=
    hsz.eventually (eventually_le_rpow ((2 : ℝ) ^ (2 * n0)) (half_pos hτ'))
  filter_upwards [hall, hpow, hell] with n hn hp hellN I hWF h2 h2n
  have ht1lt : t1 n < 1 := lt_of_le_of_lt (ht10 n) (ht0 n)
  have hE2 : |E n| < 2 := lt_of_le_of_lt (hE n) (by linarith)
  have hIlen : I.length ∈ Finset.Icc 2 (2 * n0) := Finset.mem_Icc.2 ⟨h2, h2n⟩
  have hb := hn I.length hIlen (fun i : Fin I.length => I.σ.getD i false)
    (fun i : Fin I.length => I.a.getD i (0 : Zd d (sz.L n)))
  rw [← hKinit n, ProcK_loopOf_eq I hWF] at hb
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := ProcK_size_pos sz n
  have hBle : sz.Bctl n (t1 n) ≤ 2 * (gueScale sz E n (t1 n))⁻¹ :=
    ProcK_Bctl_le sz n hE2 ht1lt hellN
  have hB0 : 0 ≤ sz.Bctl n (t1 n) := by
    have hx : 0 < 1 - t1 n := by linarith
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hx]
    positivity
  have hsc : 0 < gueScale sz E n (t1 n) := ProcK_gueScale_pos sz hE hκ n ht1lt
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
private theorem ProcK_hbase {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) {E t1 t0 : ℕ → ℝ}
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
  filter_upwards [ProcK_initial sz hκ n0 hE ht1 ht10 ht0 hsz hell hKb Kt hKinit hτ'0, h730,
    hsz.eventually (eventually_small (n := 2 * n0) hτ'U),
    hsz.eventually (eventually_le_rpow 2 (sub_pos.2 hτ'τ))] with n hinit h730n hε h2
  intro t ht I hWF h2I hIn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := ProcK_size_pos sz n
  have ht1lt : ∀ u ∈ Set.Icc (t1 n) (t0 n), u < 1 := fun u hu => lt_of_le_of_lt hu.2 (ht0 n)
  have hlam : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < gueScale sz E n u := fun u hu =>
    ProcK_gueScale_pos sz hE hκ n (ht1lt u hu)
  have hanti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ v ∈ Set.Icc (t1 n) (t0 n), u ≤ v →
      gueScale sz E n v ≤ gueScale sz E n u := by
    intro u _ v _ huv
    unfold gueScale
    exact mul_le_mul_of_nonneg_left (ProcK_etaT_anti (E n) huv) hN0.le
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
    have h2' : etaT (E n) (t0 n) ≤ etaT (E n) u := ProcK_etaT_anti (E n) hu.2
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

/-- **`hK` for `gueKproc`**: `K̃ ≺ Λ^{m-1}` on the grid, interpolated, in the explicit size-scale
form `∀ ε > 0, ∀ᶠ n, … ≤ (sz.size n)^ε · (N η_t)^{-(m-1)}`, with `N = sz.size n = (W L)^d` (`h730`,
`hscale` on `N^{-τ_U}`).  The initial data at `t₁` come from `STKbound` (`hKb`, the pin) at the
sequence `t₁` under `hell : L^d (1 - t₁) ≤ ilambda²`, the bootstrap
`eq736` is applied at each `n`, and `Tendsto sz.size atTop atTop` (`hsz`) turns `∀ᶠ N` into
`∀ᶠ n`.  The hypothesis `hscale` is not used and is kept as stated. -/
theorem gueKproc_detDom {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n)
    (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (hsz : Tendsto sz.size atTop atTop)
    (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n : ℕ in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (m : Set.Icc 2 (2 * n0)),
      gueKproc sz t1 t0 (gueGridK sz n0) Kt n (m : ℕ) (t : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (gueScale sz E n (t : ℝ))⁻¹ ^ ((m : ℕ) - 1) := by
  have _hs := hscale
  intro τ hτ
  have hτ'0 : 0 < τ / 2 := by positivity
  filter_upwards [ProcK_hbase sz hκ hτU n0 hE ht1 ht10 ht0 hsz h730 hell hKb Kt hKinit
      (fun n t ht I hWF h2 hlen => hK n t ht I hWF (by omega) (by omega)) hτ'0, h730,
    hsz.eventually (eventually_le_rpow ((2 : ℝ) ^ (2 * n0 + 1)) hτ'0)] with n hbaseN h730n h2pow
  rintro ⟨t, ht⟩ ⟨m, hm⟩
  simp only [Set.mem_Icc] at hm ht
  change gueKproc sz t1 t0 (gueGridK sz n0) Kt n m t ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n t)⁻¹ ^ (m - 1)
  set Nn : ℝ := ((sz.size n : ℕ) : ℝ) with hNn
  have hN0 : 0 < Nn := ProcK_size_pos sz n
  have hN1 : 1 ≤ Nn := ProcK_one_le_size sz n
  have ht1lt : ∀ u ∈ Set.Icc (t1 n) (t0 n), u < 1 := fun u hu => lt_of_le_of_lt hu.2 (ht0 n)
  have hlam_pos : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < gueScale sz E n u := fun u hu =>
    ProcK_gueScale_pos sz hE hκ n (ht1lt u hu)
  have hlam_anti : ∀ u ∈ Set.Icc (t1 n) (t0 n), ∀ v ∈ Set.Icc (t1 n) (t0 n), u ≤ v →
      gueScale sz E n v ≤ gueScale sz E n u := by
    intro u _ v _ huv
    unfold gueScale
    exact mul_le_mul_of_nonneg_left (ProcK_etaT_anti (E n) huv) hN0.le
  have hKne : gueGridK sz n0 n ≠ 0 := gueGridK_ne_zero sz n0 n
  have hstepN : gridStep t1 t0 (gueGridK sz n0) n ≤ etaT (E n) (t0 n) := by
    have hetat0nonneg : 0 ≤ etaT (E n) (t0 n) := ProcK_etaT_nonneg (ht0 n).le
    have hK1 : (1 : ℝ) ≤ (gueGridK sz n0 n : ℝ) := by
      have hge1 : 1 ≤ gueGridK sz n0 n := Nat.one_le_iff_ne_zero.2 hKne
      exact_mod_cast hge1
    have hNpow_le1 : Nn ^ (-τU) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    unfold gridStep
    have hK0 : (0 : ℝ) < (gueGridK sz n0 n : ℝ) := by linarith
    rw [div_le_iff₀ hK0]
    calc t0 n - t1 n ≤ Nn ^ (-τU) * etaT (E n) (t0 n) := h730n
      _ ≤ 1 * etaT (E n) (t0 n) := mul_le_mul_of_nonneg_right hNpow_le1 hetat0nonneg
      _ = etaT (E n) (t0 n) := one_mul _
      _ ≤ etaT (E n) (t0 n) * (gueGridK sz n0 n : ℝ) := by nlinarith [hK1, hetat0nonneg]
  have hperk : ∀ k : ℕ, k ≤ gueGridK sz n0 n →
      gueKbar sz t1 t0 (gueGridK sz n0) Kt n m k ≤
        Nn ^ (τ / 2) * (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ (m - 1) :=
    fun k hk => ProcK_gueKbar_le_of_hbase sz t1 t0 (gueGridK sz n0) n n0 m Kt (gueScale sz E n)
      (Nn ^ (τ / 2)) (Real.rpow_nonneg hN0.le _) (ht10 n) hKne hlam_pos hlam_anti
      (fun u hu I hWF h2 hlen => hbaseN u hu I hWF h2 hlen) hm.1 hm.2 k hk
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
    have hgoal_eq : gueKproc sz t1 t0 (gueGridK sz n0) Kt n m t
        = gueKbar sz t1 t0 (gueGridK sz n0) Kt n m 0 := by
      unfold gueKproc gueInterp
      rw [ite_eq_left hstep0]
    rw [hgoal_eq, hteq]
    have h0 := hperk 0 (Nat.zero_le _)
    have e0 : gridTime t1 t0 (gueGridK sz n0) n 0 = t1 n := by simp [gridTime]
    rw [e0] at h0
    refine h0.trans ?_
    have hnn : (0 : ℝ) ≤ (gueScale sz E n (t1 n))⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos (t1 n) ⟨le_refl _, ht10 n⟩).le) _
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hnn
  · have hstepPos : 0 < gridStep t1 t0 (gueGridK sz n0) n :=
      lt_of_le_of_ne (div_nonneg (by linarith [ht10 n]) (Nat.cast_nonneg _)) (Ne.symm hstep0)
    obtain ⟨kstar, hkstarKN, hknear, hkdom⟩ :=
      ProcK_gueTime_kstar_near hstepPos (ht10 n) t ht.1 ht.2 hKne
    have htimekstar_mem : gridTime t1 t0 (gueGridK sz n0) n kstar ∈ Set.Icc (t1 n) (t0 n) :=
      ProcK_gueTime_mem_Icc (ht10 n) hKne hkstarKN
    have hlamnear : gueScale sz E n t ≤ 2 * gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n kstar) := by
      have hM : (0 : ℝ) ≤ Nn := hN0.le
      have hE2 : |E n| ≤ 2 := by have := hE n; have := hκ; linarith
      have him1 : (mE (E n)).im ≤ 1 := by
        have h1 := Complex.abs_im_le_norm (mE (E n))
        rw [norm_mE hE2] at h1
        exact (abs_le.mp h1).2
      have him0 : 0 ≤ (mE (E n)).im := by rw [mE_im]; positivity
      have hsmall : Nn * gridStep t1 t0 (gueGridK sz n0) n ≤
          Nn * (1 - t0 n) * (mE (E n)).im := by
        have hstepmul := mul_le_mul_of_nonneg_left hstepN hM
        rw [show Nn * etaT (E n) (t0 n) = Nn * (1 - t0 n) * (mE (E n)).im by
          unfold etaT; ring] at hstepmul
        exact hstepmul
      have hkey := ProcK_lam_near_le hM him0 him1 htimekstar_mem.2 hknear hsmall
      unfold gueScale etaT
      linarith [hkey, mul_assoc Nn (1 - t) (mE (E n)).im,
        mul_assoc Nn (1 - gridTime t1 t0 (gueGridK sz n0) n kstar) (mE (E n)).im]
    have hinvnear : (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n kstar))⁻¹
        ≤ 2 * (gueScale sz E n t)⁻¹ :=
      ProcK_inv_le_two_inv_of_le_two_mul (hlam_pos t ht) (hlam_pos _ htimekstar_mem) hlamnear
    have hkstarbound : gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar ≤
        Nn ^ (τ / 2) * (2 ^ (2 * n0) * (gueScale sz E n t)⁻¹ ^ (m - 1)) := by
      refine (hperk kstar hkstarKN).trans ?_
      have hNnn2 : (0 : ℝ) ≤ Nn ^ (τ / 2) := Real.rpow_nonneg hN0.le _
      apply mul_le_mul_of_nonneg_left _ hNnn2
      have hkstarinv_nn : (0 : ℝ) ≤ (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n kstar))⁻¹ :=
        inv_nonneg.2 (hlam_pos _ htimekstar_mem).le
      have htinv_nn : (0 : ℝ) ≤ (gueScale sz E n t)⁻¹ ^ (m - 1) :=
        pow_nonneg (inv_nonneg.2 (hlam_pos t ht).le) _
      calc (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n kstar))⁻¹ ^ (m - 1)
          ≤ (2 * (gueScale sz E n t)⁻¹) ^ (m - 1) :=
            pow_le_pow_left₀ hkstarinv_nn hinvnear (m - 1)
        _ = 2 ^ (m - 1) * (gueScale sz E n t)⁻¹ ^ (m - 1) := by rw [mul_pow]
        _ ≤ 2 ^ (2 * n0) * (gueScale sz E n t)⁻¹ ^ (m - 1) := by
            apply mul_le_mul_of_nonneg_right _ htinv_nn
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hgueKproc_le : gueKproc sz t1 t0 (gueGridK sz n0) Kt n m t
        ≤ 2 * gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar := by
      unfold gueKproc gueInterp
      rw [ite_eq_right hstep0]
      have hdomle : ∀ k, k ∈ Finset.range (gueGridK sz n0 n + 1) →
          gueKbar sz t1 t0 (gueGridK sz n0) Kt n m k * gueTent t1 t0 (gueGridK sz n0) n k t
            ≤ gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar *
              gueTent t1 t0 (gueGridK sz n0) n k t := by
        intro k hk
        by_cases hpos : 0 < gueTent t1 t0 (gueGridK sz n0) n k t
        swap
        · have htent0 : gueTent t1 t0 (gueGridK sz n0) n k t = 0 :=
            le_antisymm (not_lt.1 hpos) (ProcK_gueTent_nonneg k t)
          rw [htent0, mul_zero, mul_zero]
        · have hkkstar : k ≤ kstar :=
            hkdom k (by simpa using (Finset.mem_range.mp hk : k < gueGridK sz n0 n + 1)) hpos
          exact mul_le_mul_of_nonneg_right (ProcK_gueKbar_mono sz Kt m hkkstar)
            (ProcK_gueTent_nonneg k t)
      calc ∑ k ∈ Finset.range (gueGridK sz n0 n + 1),
            gueKbar sz t1 t0 (gueGridK sz n0) Kt n m k * gueTent t1 t0 (gueGridK sz n0) n k t
          ≤ ∑ k ∈ Finset.range (gueGridK sz n0 n + 1),
              gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar *
                gueTent t1 t0 (gueGridK sz n0) n k t :=
            Finset.sum_le_sum hdomle
        _ = gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar *
              ∑ k ∈ Finset.range (gueGridK sz n0 n + 1), gueTent t1 t0 (gueGridK sz n0) n k t := by
            rw [Finset.mul_sum]
        _ ≤ gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar * 2 := by
            have hkbar_nonneg : (0 : ℝ) ≤ gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar := by
              unfold gueKbar
              exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
            apply mul_le_mul_of_nonneg_left (ProcK_gueTent_sum_le_two t hstepPos ht.1) hkbar_nonneg
        _ = 2 * gueKbar sz t1 t0 (gueGridK sz n0) Kt n m kstar := by ring
    have hcomb : gueKproc sz t1 t0 (gueGridK sz n0) Kt n m t
        ≤ 2 * (Nn ^ (τ / 2) * (2 ^ (2 * n0) * (gueScale sz E n t)⁻¹ ^ (m - 1))) := by
      refine hgueKproc_le.trans ?_
      exact mul_le_mul_of_nonneg_left hkstarbound (by norm_num)
    refine hcomb.trans ?_
    have hfin : 2 * (Nn ^ (τ / 2) * (2 ^ (2 * n0) * (gueScale sz E n t)⁻¹ ^ (m - 1)))
        = (2 ^ (2 * n0 + 1)) * Nn ^ (τ / 2) * (gueScale sz E n t)⁻¹ ^ (m - 1) := by ring
    rw [hfin]
    have hpow2N : (2 : ℝ) ^ (2 * n0 + 1) ≤ Nn ^ (τ / 2) := h2pow
    have hNpow_split : Nn ^ τ = Nn ^ (τ / 2) * Nn ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [hNpow_split]
    have htinv_nn' : (0 : ℝ) ≤ (gueScale sz E n t)⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hlam_pos t ht).le) _
    have hfinal : (2 : ℝ) ^ (2 * n0 + 1) * Nn ^ (τ / 2) ≤ Nn ^ (τ / 2) * Nn ^ (τ / 2) :=
      mul_le_mul_of_nonneg_right hpow2N (Real.rpow_nonneg hN0.le _)
    exact mul_le_mul_of_nonneg_right hfinal htinv_nn'

end KprocInput

end RBM.Univ.GUEPhase


/-! ## Compiled instances

`ProcKInst`: the conversion at the numbers `d = 3`, `L = 3`, `W = 2`, `ilambda = 1`,
`1 - t₁ = 1/27`, and `gueKproc_detDom` at the merged `Grid.lean` sizes `SizesInst.sz0`. -/

namespace RBM.Univ.GUEPhase.ProcKInst

open MeasureTheory Filter Topology RBM RBM.Gauss RBM.Path

open RBM.Gauss.SizesInst

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : Real.sqrt (4 - (0:ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]; norm_num


/-! ### The conversion `Bctl n t₁ ≤ 2 (N η_{t₁})⁻¹` at concrete numbers

`d = 3`, `L = 3`, `W = 2`, `ilambda = 1`, `1 - t₁ = 1/27` (`L^d (1 - t₁) = 1 = ilambda²`, the
boundary case of `hell`), `E = 0` (`Im m = 1`): `N = 216`, `N η_{t₁} = 8`, `Bctl = 55/224 ≤ 1/4`. -/

/-- The toy size data: `L = 3`, `W = 2`, `ilambda = 1` at every `n`. -/
def szToy : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

theorem szToy_Bctl : szToy.Bctl 0 (26 / 27) = 55 / 224 := by
  unfold Sizes.Bctl Bparam szToy
  norm_num [abs_of_pos]

theorem szToy_scale : ((szToy.size 0 : ℕ) : ℝ) * etaT 0 (26 / 27) = 8 := by
  unfold Sizes.size etaT
  rw [mE_zero_im]
  norm_num [szToy]

/-- The conversion at the toy numbers, by direct evaluation. -/
theorem szToy_conv :
    szToy.Bctl 0 (26 / 27) ≤ 2 * (((szToy.size 0 : ℕ) : ℝ) * etaT 0 (26 / 27))⁻¹ := by
  rw [szToy_Bctl, szToy_scale]; norm_num

/-- The conversion lemma `ProcK_Bctl_le` at the toy numbers (`hell` with equality). -/
example : szToy.Bctl 0 (26 / 27) ≤ 2 * (((szToy.size 0 : ℕ) : ℝ) * etaT 0 (26 / 27))⁻¹ :=
  ProcK_Bctl_le szToy 0 (E := 0) (by norm_num) (by norm_num) (by norm_num [szToy])

/-! ### `gueKproc_detDom` at the `Grid.lean` §`GridCheck` sizes -/

private def Nn (n : ℕ) : ℝ := ((sz0.size n : ℕ) : ℝ)

private theorem size_eq (n : ℕ) : sz0.size n = 2 ^ 21 * (n + 1) ^ 18 := by
  unfold Sizes.size
  simp only [sz0]
  ring

private theorem Nn_eq (n : ℕ) : Nn n = 2 ^ 21 * ((n : ℝ) + 1) ^ 18 := by
  unfold Nn
  rw [size_eq]
  push_cast
  ring

private theorem Nn_pos (n : ℕ) : 0 < Nn n := by rw [Nn_eq]; positivity

private theorem Nn_ge_one (n : ℕ) : 1 ≤ Nn n := by
  rw [Nn_eq]
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 18 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) 21, show (1:ℝ) ≤ 2 ^ 21 by norm_num]

/-- `N^{1/500} ≤ 4 (n+1)^3`: `N = 2^21 (n+1)^18 ≤ (4 (n+1)^3)^500`. -/
private theorem Nn_rpow_le (n : ℕ) : Nn n ^ (1 / 500 : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 3 := by
  have hu : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have h1 : Nn n ≤ (4 * ((n : ℝ) + 1) ^ 3) ^ 500 := by
    rw [Nn_eq, mul_pow, ← pow_mul]
    have h2 : ((n : ℝ) + 1) ^ 18 ≤ ((n : ℝ) + 1) ^ (3 * 500) :=
      pow_le_pow_right₀ hu (by norm_num)
    have h3 : (2 : ℝ) ^ 21 ≤ 4 ^ 500 :=
      calc (2 : ℝ) ^ 21 ≤ 4 ^ 21 := pow_le_pow_left₀ (by norm_num) (by norm_num) 21
        _ ≤ 4 ^ 500 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact mul_le_mul h3 h2 (by positivity) (by positivity)
  calc Nn n ^ (1 / 500 : ℝ) ≤ ((4 * ((n : ℝ) + 1) ^ 3) ^ 500) ^ (1 / 500 : ℝ) :=
        Real.rpow_le_rpow (Nn_pos n).le h1 (by norm_num)
    _ = 4 * ((n : ℝ) + 1) ^ 3 := by
        rw [show (1 / 500 : ℝ) = ((500 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)

/-- `1 - t₀ = N^{1/500} / N = N^{-1 + 2τ_U}` with `τ_U = 1/1000` (the `η_LL` scale). -/
private def x0 (n : ℕ) : ℝ := Nn n ^ (1 / 500 : ℝ) / Nn n

private def t0 (n : ℕ) : ℝ := 1 - x0 n

/-- `t₀ - t₁ = N^{-τ_U} (1 - t₀) / 2`. -/
private def t1 (n : ℕ) : ℝ := t0 n - Nn n ^ (-(1 / 1000 : ℝ)) * x0 n / 2

private theorem x0_pos (n : ℕ) : 0 < x0 n := by
  unfold x0
  exact div_pos (Real.rpow_pos_of_pos (Nn_pos n) _) (Nn_pos n)

private theorem x0_le (n : ℕ) : x0 n ≤ 1 / (2 ^ 19 * ((n : ℝ) + 1) ^ 15) := by
  unfold x0
  have hu : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ (Nn_pos n) (by positivity)]
  have := Nn_rpow_le n
  have h2 : Nn n ^ (1 / 500 : ℝ) * (2 ^ 19 * ((n : ℝ) + 1) ^ 15)
      ≤ 4 * ((n : ℝ) + 1) ^ 3 * (2 ^ 19 * ((n : ℝ) + 1) ^ 15) :=
    mul_le_mul_of_nonneg_right this (by positivity)
  calc Nn n ^ (1 / 500 : ℝ) * (2 ^ 19 * ((n : ℝ) + 1) ^ 15)
      ≤ 4 * ((n : ℝ) + 1) ^ 3 * (2 ^ 19 * ((n : ℝ) + 1) ^ 15) := h2
    _ = 1 * Nn n := by rw [Nn_eq]; ring

private theorem Npow_le_one (n : ℕ) : Nn n ^ (-(1 / 1000 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (Nn_ge_one n) (by norm_num)

private theorem Npow_nonneg (n : ℕ) : 0 ≤ Nn n ^ (-(1 / 1000 : ℝ)) :=
  Real.rpow_nonneg (Nn_pos n).le _

private theorem x0_small (n : ℕ) : x0 n ≤ 1 / 2 ^ 19 := by
  refine (x0_le n).trans ?_
  have hu : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 15 := one_le_pow₀ hu
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) 19]


private theorem t0_lt_one (n : ℕ) : t0 n < 1 := by unfold t0; linarith [x0_pos n]

private theorem etaT_t0 (n : ℕ) : etaT 0 (t0 n) = x0 n := by
  unfold etaT t0
  rw [mE_zero_im]
  ring

private theorem t1_nonneg (n : ℕ) : 0 ≤ t1 n := by
  unfold t1 t0
  have h1 := x0_small n
  have h2 := mul_le_mul_of_nonneg_right (Npow_le_one n) (x0_pos n).le
  have h3 : (0 : ℝ) < 1 / 2 ^ 19 := by positivity
  have h4 : (1 : ℝ) / 2 ^ 19 ≤ 1 / 4 := by norm_num
  nlinarith

private theorem t1_le_t0 (n : ℕ) : t1 n ≤ t0 n := by
  unfold t1
  linarith [mul_nonneg (Npow_nonneg n) (x0_pos n).le]

private theorem h730_at (n : ℕ) :
    t0 n - t1 n ≤ Nn n ^ (-(1 / 1000 : ℝ)) * etaT 0 (t0 n) := by
  rw [etaT_t0]
  unfold t1
  nlinarith [mul_nonneg (Npow_nonneg n) (x0_pos n).le]

private theorem hscale_at (n : ℕ) :
    (gueScale sz0 (fun _ => (0 : ℝ)) n (t0 n))⁻¹ ≤ Nn n ^ (-(1 / 1000 : ℝ)) := by
  have h : gueScale sz0 (fun _ => (0 : ℝ)) n (t0 n) = Nn n ^ (1 / 500 : ℝ) := by
    unfold gueScale
    change Nn n * etaT 0 (t0 n) = _
    rw [etaT_t0]
    unfold x0
    have := (Nn_pos n).ne'
    field_simp
  rw [h, ← Real.rpow_neg (Nn_pos n).le]
  exact Real.rpow_le_rpow_of_exponent_le (Nn_ge_one n) (by norm_num)

private theorem hell_at (n : ℕ) :
    ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - t1 n) ≤ sz0.lam n ^ 2 := by
  have hu : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx := x0_le n
  have h1 : 1 - t1 n ≤ 3 / 2 * x0 n := by
    unfold t1 t0
    have h2 := mul_le_mul_of_nonneg_right (Npow_le_one n) (x0_pos n).le
    nlinarith
  have hL : ((sz0.L n : ℕ) : ℝ) = 4 * ((n : ℝ) + 1) := by simp [sz0]
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  rw [hL, hlam]
  have h3 : (4 * ((n : ℝ) + 1)) ^ 3 * (1 - t1 n)
      ≤ (4 * ((n : ℝ) + 1)) ^ 3 * (3 / 2 * (1 / (2 ^ 19 * ((n : ℝ) + 1) ^ 15))) :=
    mul_le_mul_of_nonneg_left (h1.trans (by gcongr)) (by positivity)
  have h4 : (4 * ((n : ℝ) + 1)) ^ 3 * (3 / 2 * (1 / (2 ^ 19 * ((n : ℝ) + 1) ^ 15)))
      = 96 / (2 ^ 19 * ((n : ℝ) + 1) ^ 12) := by
    field_simp
    ring
  have h5 : (((2 * ((n : ℝ) + 1)) ^ 6)⁻¹) ^ 2 = 128 / (2 ^ 19 * ((n : ℝ) + 1) ^ 12) := by
    field_simp
    ring
  rw [h5]
  refine h3.trans ?_
  rw [h4]
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **`gueKproc_detDom` at the `Grid.lean` §`GridCheck` sizes** `sz0` (`d = 3`, `L = 4 (n+1)`,
`W = (2 (n+1))^5`, `lam = (2 (n+1))^{-6}`, `N = 2^21 (n+1)^18 → ∞`), `κ = 1/10`, `E = 0`
(`Im m = 1`), `τ_U = 1/1000`, `n₀ = 2`, `1 - t₀ = N^{-1+2τ_U}` (the `η_LL` scale), `t₀ - t₁ =
N^{-τ_U} (1 - t₀)/2` (so `t₁ < t₀`, a genuine window, and `L^3 (1 - t₁) ≤ ilambda²` for every `n`).
Every deterministic hypothesis is discharged (`hE`, `ht1`, `ht10`, `ht0`, `hsz`, `h730`, `hscale`,
`hell`); `hKb`, `hKinit`, `hK` stay hypotheses of the instance (the owed pin `STKbound`, the
identification with the band K-loop, the Duhamel family).  The `GridCheck` times `t₀ = 9/10`,
`t₁ = e^{-1/20} 9/10` are *not* in the zero-mode regime (`L^3 (1 - t₁) ≥ 64 · 0.14 > ilambda² =
(1/64)²`), so only the sizes are shared. -/
example (hKb : sz0.STKbound (fun _ => (0 : ℝ)))
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd 3 (sz0.L n)),
      Kt n (t1 n) (loopOf σ a) = sz0.STKloop n 0 (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd 3 (sz0.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * 2 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE 3 (sz0.L n) (sz0.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (t : TimeIcc t1 t0 n) (m : Set.Icc 2 (2 * 2)),
      gueKproc sz0 t1 t0 (gueGridK sz0 2) Kt n (m : ℕ) (t : ℝ) ≤
        ((sz0.size n : ℕ) : ℝ) ^ ε * (gueScale sz0 (fun _ => (0 : ℝ)) n (t : ℝ))⁻¹ ^ ((m : ℕ) - 1) :=
  gueKproc_detDom sz0 (κ := 1 / 10) (τU := 1 / 1000) (by norm_num) (by norm_num) 2
    (E := fun _ => (0 : ℝ)) (t1 := t1) (t0 := t0)
    (fun n => by norm_num) t1_nonneg t1_le_t0 t0_lt_one
    (Sizes.tendsto_size sz0 sz0_tendsto)
    (Filter.Eventually.of_forall h730_at) (Filter.Eventually.of_forall hscale_at)
    (Filter.Eventually.of_forall hell_at) hKb Kt hKinit hK

/-- The window of the instance is genuine: `t₁ n < t₀ n < 1` and `0 < t₁ n` at every `n`. -/
example (n : ℕ) : 0 < t1 n ∧ t1 n < t0 n ∧ t0 n < 1 := by
  refine ⟨?_, ?_, t0_lt_one n⟩
  · unfold t1 t0
    have h1 := x0_small n
    have h2 := mul_le_mul_of_nonneg_right (Npow_le_one n) (x0_pos n).le
    nlinarith [x0_pos n]
  · unfold t1
    have := mul_pos (Real.rpow_pos_of_pos (Nn_pos n) (-(1 / 1000 : ℝ))) (x0_pos n)
    linarith

end RBM.Univ.GUEPhase.ProcKInst
