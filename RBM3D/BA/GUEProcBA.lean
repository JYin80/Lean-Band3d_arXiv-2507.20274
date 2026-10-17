/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEKPrim
import RBM3D.BA.GUEOneLoop
import RBM3D.Universality.GUEPhase.Proc

/-!
# BA-C5 row a: the process layer of the §7.2 random layer on the GUE-phase grid at block Anderson

Ticket T2519 (row a; DECISIONS §344, §346, §348; Amends 1-3; design gate D1 signed by
`docs/reports/T2519-1a-audit.md`).  New BA leaf: no merged file is edited.  Band twins:
`Universality/GUEPhase/Grid.lean` (`GUEPathBounds:89`), `RandomLayerB.lean` (`RandomLayerB_KFam:63`,
`RandomLayerB_PBband:346`).  Paper: the GUE phase of Thm 2.4
(`paper/tex/1_2_Intro_model_result.tex:566-570`, "essentially identical to [YY_25, Theorem 2.6]"),
`d ≥ 3`, block Anderson `S^{(B)}(0) = 1`.

* §1 (target 1, first commit; read by rows b, b′, c, d and N2) `GUEPathBoundsBA`, `BAKFam`, `BAPB`:
  the texts `T2519_PathBoundsBA`, `T2519_KFamBA`, `T2519_PBBA` of the 1a-audit (probe `t/T2519`
  b992c2e7, with Amend 1 item 1: `n₀ = 4`, `gueGridK sz 4`, loop lengths `≤ 4 * 4`) under their
  final names.  They are `def … : Prop`; the local law of `GUEPathBoundsBA` is against
  `Mres (g Ψ_I) E m = M^{(B)} ⊗ 1`, not `m • 1`; no twist field (`hoff` is target 7,
  `gueGrid_twistBA`, row b′).
* §2 (target 2) the BA process layer, twin of `Proc.lean:83-122, 396-469`: `gueDevBA`,
  `gueStopBA`, `gueLmaxBA`, `gueDmaxBA`, `gueLprocBA`, `gueDprocBA` (the loop length is `l`, the
  flow datum is `(g, E, m)`) and the structural facts `gueLprocBA_nonneg`, …, `gueDprocBA_time`.
* §3 `norm_egtNGUEOf_le` (twin of `Proc:596`, the generic `egtNGUEOf`); §4 `gueDevBA_succ_le`
  (twin of `Proc:771`, `0 < Im m` and `‖m‖ ≤ 1` replace `|E| < 2`).
* The private band helpers are read by `open private … from RBM3D.Universality.GUEPhase.Proc`;
  `gueTent`, `gueInterp`, `gueDelta`, `gueKbar`, `gueKproc` carry no band token and are read by
  name.
* Instances: §1 `BAKFam` is nonempty at the BA flow datum of `sz0`; §2-§4 apply every fact at that
  datum.
-/

set_option linter.style.longLine false

open private Proc_gueInterp_add Proc_gueInterp_mono Proc_gueInterp_nonneg Proc_gueInterp_continuousOn
  Proc_gueInterp_sqrt_mul_le Proc_gueInterp_time Proc_gueTime_const_of_step_zero Proc_gueH_const_of_step_zero
  Proc_norm_le_norm_sub_add_norm Proc_le_ciSup_finite Proc_le_ciSup_finite_aux Proc_opNorm_le_sum_norm
  Proc_norm_green_le Proc_norm_green_sub_le Proc_gridTime_mono from RBM3D.Universality.GUEPhase.Proc

noncomputable section

namespace RBM.BA

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase

/-! ## 1. Target 1: the vocabulary -/

/-- **Target 1, `GUEPathBoundsBA`** (twin of `GUEPathBounds`, `Grid:89`; text `T2519_PathBoundsBA`): the output of the §7.2
random layer on the BA grid `gueHBA` at the grid times `k ≤ K n`: (7.28) for loops of length `1 ≤ k ≤ n₀` against a
primitive family `Kt` (first conjunct `lk`), and `‖G̃ - M‖_max ≺ (N η_u)^{-1/2}` against the deterministic
`M = Mres (g Ψ_I) E m = M^{(B)} ⊗ 1` (second conjunct `localLaw`).  The path is `gueHBA`, the flow `ztOf (m n) (E n)`, the scale
`N etaOf (m n) u`.  No twist field. -/
def GUEPathBoundsBA {d : ℕ} (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ n0 → StochDomAt (Pgue (sz.withLam 0)) sz.size
    (fun n (p : Fin (K n + 1) × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) ω =>
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n p.1 ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2) -
        Kt n (gridTime t1 t0 K n p.1) (loopOf p.2.1 p.2.2)‖)
    (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹ ^ k)) ∧
  StochDomAt (Pgue (sz.withLam 0)) sz.size
    (fun n (p : Fin (K n + 1) × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω =>
      ‖green (gueHBA sz g t1 t0 K n p.1 ω) (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) p.2.1 p.2.2 -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) p.2.1 p.2.2‖)
    (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹ ^ ((1 : ℝ) / 2))

/-- **Target 1, `BAKFam`** (twin of `RandomLayerB_KFam`, `RandomLayerB:63`; text `T2519_KFamBA`): at the flow point
`g = √t₀ λ`, `m = BAm d L g E'` (the real-axis solution), start `BAKsol` at `t₁`, the ODE `primRhsGUE` on `[t₁, t₀]`
(loops of length `≤ 4 * 4`, `n₀ = 4`), 2-loops `kTwoGUEBA`.  Every clause is guarded by `0 < g` (`gueK_existsBA` needs
it; `Sizes.lam` has no sign). -/
def BAKFam (d : ℕ) (sz : Sizes d) (E' t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I =
        BAKsol d (sz.L n) (sz.W n)
          (BAMsigma d (sz.L n) (BAMB d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)
            (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))))
          (PropSpin (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))) (t1 n) I) ∧
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * 4 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) ∧
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt (t0 n) * sz.lam n) (E' n)
          (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (t1 n) s σ₁ σ₂ a b)

/-- **Target 1, `BAPB`** (twin of `RandomLayerB_PBband`, `RandomLayerB:346`; text `T2519_PBBA`): `GUEPathBoundsBA` at the flow
point of the RBG texts, `g = √t₀ λ`, `m = BAm d L g E'`, grid `gueGridK sz 4`, `n₀ = 4` (Amend 1 item 1 (a)). -/
def BAPB (d : ℕ) (sz : Sizes d) (E' t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  GUEPathBoundsBA sz (fun n => Real.sqrt (t0 n) * sz.lam n) E' t1 t0
    (fun n => BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (gueGridK sz 4) 4 Kt

/-! ## 2. Target 2: the process layer on the BA grid

The twins of the band process layer (`Universality/GUEPhase/Proc.lean:83-122, 396-469`) at the BA grid path `gueHBA`
(`g Ψ_I + H_k`), the flow `ztOf (m n) (E n)` and the deterministic centre `M = Mres (g Ψ_I) E m = M^{(B)} ⊗ 1` of the
local law.  The flow datum is `(g, E, m)` with `E`, `g` real and `m` complex (the BA twin of the band `E ↦ mE E`); the loop
length is `l`.  `gueTent`, `gueInterp`, `gueDelta`, `gueKbar`, `gueKproc` carry no band token and are read by name. -/

section Proc

variable {d : ℕ} (sz : Sizes d)

/-- `max_{i,j} |(G_k - M)_{ij}|` at the grid step `k`, `M = Mres (g Ψ_I) E m` (twin of `gueDev`, `Proc:83`; the band centre `mE E • 1`
is the case `H₀ = 0` of `Mres`, cf. `Mres_zero_msc`, `Loop/GLoopFlow:219`). -/
def gueDevBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  ⨆ ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
    ‖(green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) ij.1 ij.2‖

/-- The freezing index: the first grid step with `gueDevBA ≥ δ_n` (else `K n`) (twin of `gueStop`, `Proc:89`). -/
def gueStopBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n : ℕ) (ω : PathΩ (sz.withLam 0)) : ℕ :=
  firstHit (fun k ω' => gueDevBA sz g E t1 t0 m K n k ω') (δ n) (K n) ω

/-- `L^{(l)}_k = max_{σ,a} |L_{σ,a}|` at the grid step `k` (twin of `gueLmax`, `Proc:93`). -/
def gueLmaxBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n l k : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
    (ztOf (m n) (E n) (gridTime t1 t0 K n k)) l

/-- `D^{(l)}_k = max_x |L_x - K̃_x|` at the grid step `k` (twin of `gueDmax`, `Proc:98`). -/
def gueDmaxBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (n l k : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  ⨆ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2)‖

/-- The stopped, interpolated `Lm` fed to `eq727GEAt`/`eq728GAt` (twin of `gueLproc`, `Proc:112`). -/
def gueLprocBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n l : ℕ) (t : ℝ)
    (ω : PathΩ (sz.withLam 0)) : ℝ :=
  gueInterp t1 t0 K n (fun k => gueLmaxBA sz g E t1 t0 m K n l (min k (gueStopBA sz g E t1 t0 m K δ n ω)) ω) t

/-- The stopped, interpolated `Dm` fed to `eq727GEAt`/`eq728GAt` (twin of `gueDproc`, `Proc:116`). -/
def gueDprocBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ) (t : ℝ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  gueInterp t1 t0 K n
    (fun k => gueDmaxBA sz g E t1 t0 m K Kt n l (min k (gueStopBA sz g E t1 t0 m K δ n ω)) ω) t

/-! ### Structural facts of the stopped processes -/

section ProcFacts

variable {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {K : ℕ → ℕ} {n : ℕ}

/-- At `Δ = 0` the BA grid path is constant in `k` (`Proc_gueH_const_of_step_zero` at `sz.withLam 0`). -/
private theorem GUEProcBA_gueHBA_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (k : ℕ)
    (ω : PathΩ (sz.withLam 0)) : gueHBA sz g t1 t0 K n k ω = gueHBA sz g t1 t0 K n 0 ω := by
  unfold gueHBA
  rw [Proc_gueH_const_of_step_zero (sz.withLam 0) h0 k ω]

private theorem GUEProcBA_gueLmaxBA_const_of_step_zero (h0 : gridStep t1 t0 K n = 0) (l k : ℕ)
    (ω : PathΩ (sz.withLam 0)) :
    gueLmaxBA sz g E t1 t0 m K n l k ω = gueLmaxBA sz g E t1 t0 m K n l 0 ω := by
  unfold gueLmaxBA
  rw [GUEProcBA_gueHBA_const_of_step_zero sz h0 k ω, Proc_gueTime_const_of_step_zero h0 k,
    Proc_gueTime_const_of_step_zero h0 0]

private theorem GUEProcBA_gueDmaxBA_const_of_step_zero (h0 : gridStep t1 t0 K n = 0)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (l k : ℕ) (ω : PathΩ (sz.withLam 0)) :
    gueDmaxBA sz g E t1 t0 m K Kt n l k ω = gueDmaxBA sz g E t1 t0 m K Kt n l 0 ω := by
  unfold gueDmaxBA
  rw [GUEProcBA_gueHBA_const_of_step_zero sz h0 k ω, Proc_gueTime_const_of_step_zero h0 k,
    Proc_gueTime_const_of_step_zero h0 0]

private theorem GUEProcBA_gueLmax_le_gueDmax_add_gueKbar (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (n l k' k : ℕ) (hk' : k' ≤ k) (ω : PathΩ (sz.withLam 0)) :
    gueLmaxBA sz g E t1 t0 m K n l k' ω ≤
      gueDmaxBA sz g E t1 t0 m K Kt n l k' ω + gueKbar sz t1 t0 K Kt n l k := by
  unfold gueLmaxBA gueDmaxBA gueKbar RBM.Ind.loopMax
  apply ciSup_le
  intro x
  have h1 := Proc_norm_le_norm_sub_add_norm
    (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
      (ztOf (m n) (E n) (gridTime t1 t0 K n k')) (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Zd d (sz.L n))))
    (Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Zd d (sz.L n))))
  have h2 : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k'))
        (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Zd d (sz.L n))) -
      Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Zd d (sz.L n)))‖
      ≤ ⨆ y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
          ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n k')) (loopOf y.1 y.2) -
            Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖ :=
    Proc_le_ciSup_finite (fun y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)) =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n k')) (loopOf y.1 y.2) -
          Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x
  have h3 : ‖Kt n (gridTime t1 t0 K n k') (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (Zd d (sz.L n)))‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
          ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ :=
    (Proc_le_ciSup_finite (fun y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)) =>
        ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x).trans
      (Proc_le_ciSup_finite (fun j : Fin (k + 1) => ⨆ y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
        ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖) (⟨k', by omega⟩ : Fin (k + 1)))
  linarith [h1, h2, h3]

private theorem GUEProcBA_gueDmax_le_gueLmax_add_gueKbar (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (n l k' k : ℕ) (hk' : k' ≤ k) (ω : PathΩ (sz.withLam 0)) :
    gueDmaxBA sz g E t1 t0 m K Kt n l k' ω ≤
      gueLmaxBA sz g E t1 t0 m K n l k' ω + gueKbar sz t1 t0 K Kt n l k := by
  unfold gueDmaxBA gueLmaxBA RBM.Ind.loopMax gueKbar
  apply ciSup_le
  intro x
  have h1 := norm_sub_le
    (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
      (ztOf (m n) (E n) (gridTime t1 t0 K n k')) (loopOf x.1 x.2))
    (Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2))
  have h2 : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k')) (loopOf x.1 x.2)‖
      ≤ ⨆ y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
          ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n k')) ⟨List.ofFn y.1, List.ofFn y.2⟩‖ :=
    Proc_le_ciSup_finite (fun y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)) =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k' ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n k')) ⟨List.ofFn y.1, List.ofFn y.2⟩‖) x
  have h3 : ‖Kt n (gridTime t1 t0 K n k') (loopOf x.1 x.2)‖
      ≤ ⨆ j : Fin (k + 1), ⨆ y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
          ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖ :=
    (Proc_le_ciSup_finite (fun y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)) =>
        ‖Kt n (gridTime t1 t0 K n k') (loopOf y.1 y.2)‖) x).trans
      (Proc_le_ciSup_finite (fun j : Fin (k + 1) => ⨆ y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
        ‖Kt n (gridTime t1 t0 K n j) (loopOf y.1 y.2)‖) (⟨k', by omega⟩ : Fin (k + 1)))
  linarith [h1, h2, h3]

private theorem GUEProcBA_gueLmax_odd_sq_le (n j k : ℕ) (hj : 1 ≤ j) (ω : PathΩ (sz.withLam 0)) :
    gueLmaxBA sz g E t1 t0 m K n (2 * j + 1) k ω ≤
      Real.sqrt (gueLmaxBA sz g E t1 t0 m K n (2 * j) k ω * gueLmaxBA sz g E t1 t0 m K n (2 * j + 2) k ω) := by
  unfold gueLmaxBA
  exact Real.le_sqrt_of_sq_le
    (RBM.Ind.loopMax_odd_sq_le ((gueHBA_isHermitian sz g t1 t0 K n k ω).submatrix _) hj)

end ProcFacts

variable (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ)

theorem gueLprocBA_nonneg (n l : ℕ) (t : ℝ) (ω : PathΩ (sz.withLam 0)) :
    0 ≤ gueLprocBA sz g E t1 t0 m K δ n l t ω := by
  unfold gueLprocBA
  exact Proc_gueInterp_nonneg (fun k => by unfold gueLmaxBA; exact RBM.Ind.loopMax_nonneg l) t

theorem gueDprocBA_nonneg (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ) (t : ℝ)
    (ω : PathΩ (sz.withLam 0)) : 0 ≤ gueDprocBA sz g E t1 t0 m K δ Kt n l t ω := by
  unfold gueDprocBA
  exact Proc_gueInterp_nonneg
    (fun k => by unfold gueDmaxBA; exact Real.iSup_nonneg fun _ => norm_nonneg _) t

theorem gueLprocBA_continuousOn (n l : ℕ) (ω : PathΩ (sz.withLam 0)) :
    ContinuousOn (fun t => gueLprocBA sz g E t1 t0 m K δ n l t ω) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueLprocBA
  exact Proc_gueInterp_continuousOn _

theorem gueDprocBA_continuousOn (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ)
    (ω : PathΩ (sz.withLam 0)) :
    ContinuousOn (fun t => gueDprocBA sz g E t1 t0 m K δ Kt n l t ω) (Set.Icc (t1 n) (t0 n)) := by
  unfold gueDprocBA
  exact Proc_gueInterp_continuousOn _

/-- `hLDK` for the stopped processes (every `t`, every `ω`). -/
theorem gueLprocBA_le (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ) (t : ℝ)
    (ω : PathΩ (sz.withLam 0)) :
    gueLprocBA sz g E t1 t0 m K δ n l t ω ≤
      gueDprocBA sz g E t1 t0 m K δ Kt n l t ω + gueKproc sz t1 t0 K Kt n l t := by
  unfold gueLprocBA gueDprocBA gueKproc
  rw [← Proc_gueInterp_add]
  exact Proc_gueInterp_mono
    (fun k => GUEProcBA_gueLmax_le_gueDmax_add_gueKbar sz Kt n l (min k (gueStopBA sz g E t1 t0 m K δ n ω)) k
      (min_le_left _ _) ω) t

/-- `hDLK` for the stopped processes (every `t`, every `ω`). -/
theorem gueDprocBA_le (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ) (t : ℝ)
    (ω : PathΩ (sz.withLam 0)) :
    gueDprocBA sz g E t1 t0 m K δ Kt n l t ω ≤
      gueLprocBA sz g E t1 t0 m K δ n l t ω + gueKproc sz t1 t0 K Kt n l t := by
  unfold gueDprocBA gueLprocBA gueKproc
  rw [← Proc_gueInterp_add]
  exact Proc_gueInterp_mono
    (fun k => GUEProcBA_gueDmax_le_gueLmax_add_gueKbar sz Kt n l (min k (gueStopBA sz g E t1 t0 m K δ n ω)) k
      (min_le_left _ _) ω) t

/-- `hodd` for the stopped processes: (6.4) at the grid, Cauchy-Schwarz for the tent weights. -/
theorem gueLprocBA_odd (n j : ℕ) (hj : 1 ≤ j) (t : ℝ) (ω : PathΩ (sz.withLam 0)) :
    gueLprocBA sz g E t1 t0 m K δ n (2 * j + 1) t ω ≤
      Real.sqrt (gueLprocBA sz g E t1 t0 m K δ n (2 * j) t ω * gueLprocBA sz g E t1 t0 m K δ n (2 * j + 2) t ω) := by
  unfold gueLprocBA
  set σ := gueStopBA sz g E t1 t0 m K δ n ω with hσ
  calc gueInterp t1 t0 K n (fun k => gueLmaxBA sz g E t1 t0 m K n (2 * j + 1) (min k σ) ω) t
      ≤ gueInterp t1 t0 K n (fun k => Real.sqrt (gueLmaxBA sz g E t1 t0 m K n (2 * j) (min k σ) ω *
          gueLmaxBA sz g E t1 t0 m K n (2 * j + 2) (min k σ) ω)) t :=
        Proc_gueInterp_mono (fun k => GUEProcBA_gueLmax_odd_sq_le sz n j (min k σ) hj ω) t
    _ ≤ Real.sqrt (gueInterp t1 t0 K n (fun k => gueLmaxBA sz g E t1 t0 m K n (2 * j) (min k σ) ω) t *
          gueInterp t1 t0 K n (fun k => gueLmaxBA sz g E t1 t0 m K n (2 * j + 2) (min k σ) ω) t) :=
        Proc_gueInterp_sqrt_mul_le (fun k => by unfold gueLmaxBA; exact RBM.Ind.loopMax_nonneg _)
          (fun k => by unfold gueLmaxBA; exact RBM.Ind.loopMax_nonneg _) t

/-- Grid values of `gueLprocBA`. -/
theorem gueLprocBA_time (n l k : ℕ) (ht10 : t1 n ≤ t0 n) (hk : k ≤ K n) (ω : PathΩ (sz.withLam 0)) :
    gueLprocBA sz g E t1 t0 m K δ n l (gridTime t1 t0 K n k) ω =
      gueLmaxBA sz g E t1 t0 m K n l (min k (gueStopBA sz g E t1 t0 m K δ n ω)) ω := by
  unfold gueLprocBA
  refine Proc_gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [GUEProcBA_gueLmaxBA_const_of_step_zero sz h0 l (min k' (gueStopBA sz g E t1 t0 m K δ n ω)) ω, Nat.zero_min]

/-- Grid values of `gueDprocBA`. -/
theorem gueDprocBA_time (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n l k : ℕ) (ht10 : t1 n ≤ t0 n)
    (hk : k ≤ K n) (ω : PathΩ (sz.withLam 0)) :
    gueDprocBA sz g E t1 t0 m K δ Kt n l (gridTime t1 t0 K n k) ω =
      gueDmaxBA sz g E t1 t0 m K Kt n l (min k (gueStopBA sz g E t1 t0 m K δ n ω)) ω := by
  unfold gueDprocBA
  refine Proc_gueInterp_time (fun h0 k' => ?_) ht10 hk
  rw [GUEProcBA_gueDmaxBA_const_of_step_zero sz h0 Kt l (min k' (gueStopBA sz g E t1 t0 m K δ n ω)) ω,
    Nat.zero_min]

end Proc

/-! ## 3. Target 2: the bound on `𝓔^{(G̃)}` for `SBgue`

`egtNGUEOf` (`Generator:79`, class P) is the generic `𝓔^{(G̃)}`: `(tr (G(σ) E_a) - m(σ))` replaces the band `avgErr`
(`Generator_avgErr`, `Generator:1090`: the two agree at `m = mE E`). -/

section EgtBound

variable {d : ℕ}

/-- **`𝓔^{(G̃)}` of the GUE profile** (twin of `norm_egtNGUE_le`, `Proc:596`; `SBgue = L^{-d}`): `|𝓔̃_GUE(I)| ≤ n · (W L)^d · ε · B`
for `|tr (G(σ) E_a) - m(σ)| ≤ ε` and `|𝓛_{cut_k^{(b)}}| ≤ B`.  The prefactor is `W^d`, `SBgue = L^{-d}` and the label sums over
`Zd d L` have `L^d` terms each, so that `W^d · (L^d · L^d) · L^{-d} = (W L)^d`.  No `|E| < 2`, no `m = mE E`. -/
theorem norm_egtNGUEOf_le (L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)) {ε B : ℝ}
    (hε : ∀ (σ : Bool) (a : Zd d L),
      ‖Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) σ * Eblk d L W a) - mSigOf m σ‖ ≤ ε)
    (hB : ∀ k ∈ Finset.Icc 1 I.length, ∀ b : Zd d L,
      ‖loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b)‖ ≤ B) :
    ‖egtNGUEOf d L W m E u M I‖ ≤ (I.length : ℝ) * (((W * L) ^ d : ℕ) : ℝ) * ε * B := by
  set e : Bool → Zd d L → ℂ := fun σ a =>
    Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) σ * Eblk d L W a) - mSigOf m σ with he
  set F : ℕ → Zd d L → ℂ := fun k b => loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b) with hF
  have hε' : ∀ σ a, ‖e σ a‖ ≤ ε := hε
  have hB' : ∀ k ∈ Finset.Icc 1 I.length, ∀ b, ‖F k b‖ ≤ B := hB
  have hgoal : egtNGUEOf d L W m E u M I =
      (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        e (I.σ.getD (k - 1) false) a * SBgue d L a b * F k b := rfl
  rw [hgoal]
  rcases Nat.eq_zero_or_pos I.length with hn0 | hn1
  · have hSempty : Finset.Icc 1 I.length = (∅ : Finset ℕ) := by
      rw [hn0]; exact Finset.Icc_eq_empty (by omega)
    rw [hSempty]
    simp [hn0]
  · have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε' true 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 1 (Finset.mem_Icc.2 ⟨le_refl 1, hn1⟩) 0)
    have hcard : Fintype.card (Zd d L) = L ^ d := card_Zd d L
    have hterm : ∀ k ∈ Finset.Icc 1 I.length, ∀ a b : Zd d L,
        ‖e (I.σ.getD (k - 1) false) a * SBgue d L a b * F k b‖ ≤ ε * ((L : ℝ) ^ d)⁻¹ * B := by
      intro k hk a b
      rw [norm_mul, norm_mul]
      have h2 : ‖SBgue d L a b‖ = ((L : ℝ) ^ d)⁻¹ := by
        rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
      rw [h2]
      have e1 : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
      calc ‖e (I.σ.getD (k - 1) false) a‖ * ((L : ℝ) ^ d)⁻¹ * ‖F k b‖
          ≤ ε * ((L : ℝ) ^ d)⁻¹ * ‖F k b‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hε' _ a) e1) (norm_nonneg _)
        _ ≤ ε * ((L : ℝ) ^ d)⁻¹ * B := mul_le_mul_of_nonneg_left (hB' k hk b) (by positivity)
    have hsum : ∀ (c : ℝ) (f : Zd d L → ℝ), (∀ x, f x ≤ c) → ∑ x, f x ≤ (L : ℝ) ^ d * c := fun c f hf => by
      calc ∑ x, f x ≤ ∑ _x : Zd d L, c := Finset.sum_le_sum fun x _ => hf x
        _ = (L : ℝ) ^ d * c := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; push_cast; ring
    have hTk : ∀ k ∈ Finset.Icc 1 I.length,
        ‖∑ a : Zd d L, ∑ b : Zd d L, e (I.σ.getD (k - 1) false) a * SBgue d L a b * F k b‖
          ≤ (L : ℝ) ^ d * ((L : ℝ) ^ d * (ε * ((L : ℝ) ^ d)⁻¹ * B)) := by
      intro k hk
      refine (norm_sum_le _ _).trans (hsum _ _ fun a => (norm_sum_le _ _).trans (hsum _ _ fun b => hterm k hk a b))
    unfold egtNGUEOf at *
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc (W : ℝ) ^ d * ‖∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
            e (I.σ.getD (k - 1) false) a * SBgue d L a b * F k b‖
        ≤ (W : ℝ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ‖∑ a : Zd d L, ∑ b : Zd d L,
            e (I.σ.getD (k - 1) false) a * SBgue d L a b * F k b‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (W : ℝ) ^ d * ∑ _k ∈ Finset.Icc 1 I.length,
            (L : ℝ) ^ d * ((L : ℝ) ^ d * (ε * ((L : ℝ) ^ d)⁻¹ * B)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hTk) (by positivity)
      _ = (W : ℝ) ^ d * ((I.length : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d *
            (ε * ((L : ℝ) ^ d)⁻¹ * B)))) := by
          have hc : (Finset.Icc 1 I.length).card = I.length := by
            rw [Nat.card_Icc]; omega
          rw [Finset.sum_const, hc, nsmul_eq_mul]
      _ = (I.length : ℝ) * (((W * L) ^ d : ℕ) : ℝ) * ε * B := by
          push_cast
          rw [mul_pow]
          field_simp

end EgtBound

/-! ## 4. Target 2: the one-step change of the entry deviation -/

section DevStep

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d)

/-- **One-step change of the entry deviation** (twin of `gueDev_succ_le`, `Proc:771`): the resolvent identity
`G' - G = G' ((H - H') + (z' - z)) G`, `H' - H = √(Δ/N) X_{k+1}` (`gueHBA_succ`), `|z' - z| = Δ |m| ≤ Δ`, and `η_u ≥ η_{t₀}` at the grid
times.  The jump of the centre `M = Mres (g Ψ_I) E m` is zero (`M` does not move with the grid), so the statement is the band one
with `etaT (E n) ↦ etaOf (m n)`; `0 < Im m` and `|m| ≤ 1` (`BAm_norm_le_one`) replace `|E| < 2`. -/
theorem gueDevBA_succ_le (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n k : ℕ) (hm : 0 < (m n).im)
    (hm1 : ‖m n‖ ≤ 1) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) (ω : PathΩ (sz.withLam 0)) :
    gueDevBA sz g E t1 t0 m K n (k + 1) ω ≤ gueDevBA sz g E t1 t0 m K n k ω +
      (etaOf (m n) (t0 n))⁻¹ ^ 2 * (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
        ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
          ‖Sizes.seqXmat (sz.withLam 0) n (ω (k + 1)) i j‖ + gridStep t1 t0 K n) := by
  have : Nonempty (Idx d (sz.L n) (sz.W n)) := ⟨(0 : Zd d (sz.W n * sz.L n))⟩
  set X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    Sizes.seqXmat (sz.withLam 0) n (ω (k + 1)) with hX
  have hKne : K n ≠ 0 := by omega
  have hstep0 : 0 ≤ gridStep t1 t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have htimeK : gridTime t1 t0 K n (K n) = t0 n := gridTime_last t1 t0 K n hKne
  have htk : gridTime t1 t0 K n k ≤ t0 n := htimeK ▸ Proc_gridTime_mono ht10 (by omega : k ≤ K n)
  have htk1 : gridTime t1 t0 K n (k + 1) ≤ t0 n := htimeK ▸ Proc_gridTime_mono ht10 (by omega : k + 1 ≤ K n)
  have hetak : etaOf (m n) (t0 n) ≤ etaOf (m n) (gridTime t1 t0 K n k) := by
    unfold etaOf; nlinarith [mul_nonneg (sub_nonneg.2 htk) hm.le]
  have hetak1 : etaOf (m n) (t0 n) ≤ etaOf (m n) (gridTime t1 t0 K n (k + 1)) := by
    unfold etaOf; nlinarith [mul_nonneg (sub_nonneg.2 htk1) hm.le]
  have het0pos : 0 < etaOf (m n) (t0 n) := by unfold etaOf; exact mul_pos (by linarith) hm
  have hzkim : (ztOf (m n) (E n) (gridTime t1 t0 K n k)).im = etaOf (m n) (gridTime t1 t0 K n k) := ztOf_im _ _ _
  have hzk1im : (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1))).im = etaOf (m n) (gridTime t1 t0 K n (k + 1)) :=
    ztOf_im _ _ _
  have hetakpos : 0 < etaOf (m n) (gridTime t1 t0 K n k) := lt_of_lt_of_le het0pos hetak
  have hetak1pos : 0 < etaOf (m n) (gridTime t1 t0 K n (k + 1)) := lt_of_lt_of_le het0pos hetak1
  have hzkim0 : (ztOf (m n) (E n) (gridTime t1 t0 K n k)).im ≠ 0 := by rw [hzkim]; linarith
  have hzk1im0 : (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1))).im ≠ 0 := by rw [hzk1im]; linarith
  have hHk := gueHBA_isHermitian sz g t1 t0 K n k ω
  have hHk1 := gueHBA_isHermitian sz g t1 t0 K n (k + 1) ω
  have hGk_le : ‖green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k))‖
      ≤ (etaOf (m n) (t0 n))⁻¹ :=
    Proc_norm_green_le hHk het0pos (by rw [hzkim, abs_of_pos hetakpos]; exact hetak)
  have hGk1_le : ‖green (gueHBA sz g t1 t0 K n (k + 1) ω) (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)))‖
      ≤ (etaOf (m n) (t0 n))⁻¹ :=
    Proc_norm_green_le hHk1 het0pos (by rw [hzk1im, abs_of_pos hetak1pos]; exact hetak1)
  have hHdiff : gueHBA sz g t1 t0 K n (k + 1) ω - gueHBA sz g t1 t0 K n k ω
      = (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) • X := by
    rw [gueHBA_succ sz g t1 t0 K n k ω]
    exact add_sub_cancel_left _ _
  have hHnorm : ‖gueHBA sz g t1 t0 K n (k + 1) ω - gueHBA sz g t1 t0 K n k ω‖
      ≤ Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ))
        * ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
            ‖X i j‖ := by
    rw [hHdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Proc_opNorm_le_sum_norm _) (Real.sqrt_nonneg _)
  have hzdiff : ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)) - ztOf (m n) (E n) (gridTime t1 t0 K n k)
      = (-(gridStep t1 t0 K n : ℂ)) * m n := by
    unfold ztOf gridTime
    push_cast
    ring
  have hznorm : ‖ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)) - ztOf (m n) (E n) (gridTime t1 t0 K n k)‖
      ≤ gridStep t1 t0 K n := by
    rw [hzdiff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hstep0]
    calc gridStep t1 t0 K n * ‖m n‖ ≤ gridStep t1 t0 K n * 1 := mul_le_mul_of_nonneg_left hm1 hstep0
      _ = gridStep t1 t0 K n := mul_one _
  have hAZ : ‖gueHBA sz g t1 t0 K n (k + 1) ω - gueHBA sz g t1 t0 K n k ω‖
        + ‖ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)) - ztOf (m n) (E n) (gridTime t1 t0 K n k)‖
      ≤ Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
          ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
            ‖X i j‖ + gridStep t1 t0 K n := add_le_add hHnorm hznorm
  have hAZ0 : 0 ≤ ‖gueHBA sz g t1 t0 K n (k + 1) ω - gueHBA sz g t1 t0 K n k ω‖
        + ‖ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)) - ztOf (m n) (E n) (gridTime t1 t0 K n k)‖ := by
    positivity
  have hGdiff := Proc_norm_green_sub_le hHk hHk1 hzkim0 hzk1im0
  have hη0 : 0 ≤ (etaOf (m n) (t0 n))⁻¹ := by positivity
  have hop : ‖green (gueHBA sz g t1 t0 K n (k + 1) ω) (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)))
        - green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k))‖
      ≤ (etaOf (m n) (t0 n))⁻¹ ^ 2 *
        (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
          ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
            ‖X i j‖ + gridStep t1 t0 K n) := by
    calc _ ≤ _ := hGdiff
      _ ≤ (etaOf (m n) (t0 n))⁻¹
            * (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
                ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
                  ‖X i j‖ + gridStep t1 t0 K n)
            * (etaOf (m n) (t0 n))⁻¹ := by
          apply mul_le_mul (mul_le_mul hGk1_le hAZ hAZ0 hη0) hGk_le (norm_nonneg _)
          positivity
      _ = _ := by ring
  unfold gueDevBA
  apply ciSup_le
  intro ij
  set Mc : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
    Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) with hMc
  have heq : (green (gueHBA sz g t1 t0 K n (k + 1) ω) (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1))) - Mc) ij.1 ij.2
      = (green (gueHBA sz g t1 t0 K n (k + 1) ω) (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k))) ij.1 ij.2
        + (green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) - Mc) ij.1 ij.2 := by
    simp only [Matrix.sub_apply]
    ring
  have hE1 := norm_add_le
    ((green (gueHBA sz g t1 t0 K n (k + 1) ω) (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k))) ij.1 ij.2)
    ((green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) - Mc) ij.1 ij.2)
  rw [← heq] at hE1
  have hE2 := RBM.Ind.norm_apply_le_l2_opNorm
    (green (gueHBA sz g t1 t0 K n (k + 1) ω) (ztOf (m n) (E n) (gridTime t1 t0 K n (k + 1)))
          - green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k))) ij.1 ij.2
  have hE3 := Proc_le_ciSup_finite_aux
    (fun ij' : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) =>
      ‖(green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) - Mc) ij'.1 ij'.2‖) ij
  linarith [hE1, hE2, hE3, hop]

end DevStep

/-! ## Compiled nonempty instances (target 5, §1)

`d = 3`, `sz0` (`L_n = 4 (n + 1)`, `W_n = (2 (n + 1))^5`, `N_0 = 2^21`, `Defs/Sizes.lean`) and the BA flow datum of `sz0` at every
`n`: `t₀ = BAflowT0 sz0 zSeq` (so `g = √t₀ λ = BAflowLam0`), `E' = BAflowEs`, `m = BAm … = BAmF` (`BAReal` at `κ = 1/2`
for every `n`, `BAflow_real`), `t₁ = t₀ / 2`.  The window is nondegenerate (`0 < t₁ < t₀ < 1`, `0 < g`). -/

/-! ### Targets 2: the process layer at the BA flow datum of `sz0`

`g = BAflowLam0`, `E = BAflowEs`, `m = BAmF` (`BAReal` at `κ = 1/2` for every `n`), the grid `t₁ = 1/4`, `t₀ = 1/2`, `K = 4`, the
a priori threshold `δ_n = 1`.  Every hypothesis is discharged. -/

-- `hLDK`, `hDLK`, `hodd`, the grid values and the continuity at the flow datum.
end RBM.BA

end
