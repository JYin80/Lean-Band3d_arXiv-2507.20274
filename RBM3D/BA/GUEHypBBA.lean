/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUEHypABA
import RBM3D.BA.GUEEntryGridBA
import RBM3D.BA.GreenLocal
import RBM3D.Universality.GUEPhase.HypB
import RBM3D.Universality.GUEPhase.BoundsA

/-!
# The pathwise assembly and the unfreezing on the BA grid

Band counterparts: `Universality/GUEPhase/HypB.lean` (`HypB_entry_le`, `HypB_eG_745`,
`HypB_eG_746`, `HypB_fixed`, the grid facts) and `BoundsA.lean` (`Bounds_path`,
`BoundsACheck.pathBounds_of_forall_highProbAt`).  Paper: the GUE
phase of Theorem 2.4 (`Thm: B_Univ`; "essentially identical to [YY_25, Theorem 2.6]"), `d ≥ 3`, block
Anderson `S^{(B)}(0) = 1`.  The equation numbers (7.26)-(7.28), (7.45), (7.46) below are those of [YY_25, §7.2].

What changes from the band (statements at the flow datum `(g, E, m)`, `g = λ₀`; path
`gueHBA`, flow `ztOf (m n) (E n)`,
scale `N etaOf (m n) u`; the local law is against `M = Mres (g Ψ_I) E m = M^{(B)} ⊗ 1`):

* `gueH sz`, `Pgue sz` become `gueHBA sz g`, `Pgue (sz.withLam 0)`; `zt E`, `mE E • 1`, `etaT E`
  become `ztOf m E`,
  `Mres (g Ψ_I) E m`, `etaOf m`; the processes are the BA ones of `BA/GUEProcBA`;
* `|E n| < 2` becomes `0 < Im m n`, `‖m n‖ ≤ 1` (for the BA flow datum, `BAReal`,
  `BAm_norm_le_one`);
* the lower-bound step (the Ward lower bound of the band `gue_inv_W_le_loopMax`) is
  `GreenLocal_floor_sample` (`BA/GreenLocal`, the BA
  analogue of `inv_Wd_le_maxLoopPM`): `W^{-d} ≤ (4/κ²) L₂` on the entry good event
  `‖G - M‖_max ≤ δ ≤ κ/2`, `M_xx = m`
  (`BAMB_diag_eq`), `|m| ≥ κ`; so the constant of the band, `1 + 2 lam²`, is `A = 1 + 4/κ²` (a
  number, not a function of `lam`)
  and the band hypothesis `hellN` of `HypB_entry_le` is not needed;
* the diagonal of `G - M` is `G_xx - m` (`M_xx = m`), so the `E^{(G)}` weight `⟨(G - m) E_a⟩` is a
  block average of the diagonal of
  `G - M` (`HypBBA_eps_le_dev`);
* the length-`1` primitive `K̃ = m_σ` is the premise `hK1` (it is `Hyp_Kt_oneBA`), in place
  of `hKinit`, `hK` of the band
  `HypB_eG_746`; the K-bound is the conclusion of `Hyp_Kt_detDomBA`.

The band privates without a band token (`HypB_size_pos`, `HypB_bil`, ...; `Bounds_unfreeze`,
`Bounds_jump`, ...) are used through
`open private`; `HypB_q_745`, `HypB_ev_grid`, `HypB_highProb_range` carry no band token and are
used by name.

* §1 `HypBBA_inv_W_le_loopMax`, `HypBBA_eps_le_dev` (the BA lower-bound step and the block average of the
  diagonal), `HypB_entry_leBA` (the entry bound at the
  stopped grid times), `HypB_eG_745BA`, `HypB_eG_746BA` (the two `E^{(G)}` drift lines);
* §2 the grid facts `HypBBA_ev_delta`, `HypBBA_step_le`, `HypBBA_Kt_le_one`, `HypBBA_Lproc_grid`,
  `HypBBA_Dproc_grid`,
  `HypBBA_sqrt_cont`;
* §3 the pathwise bound at one length `HypBBA_path` (private); §4 the exponent bookkeeping
  `HypB_fixedBA`;
* §5 the unfreezing: `Bounds_pathBA` and `pathBounds_of_forall_highProbAtBA`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private HypB_size_pos HypB_one_le_size HypB_size_cast HypB_loopOf_wf HypB_loopOf_length HypB_bil
  from RBM3D.Universality.GUEPhase.HypB
open private Hyp_norm_trace_Eblk_le Hyp_Gres_conjTranspose from RBM3D.Universality.GUEPhase.HypA
open private EntryGridBA_maxLoop_le from RBM3D.BA.GUEEntryGridBA
open private Bounds_le_firstHit Bounds_unfreeze Bounds_sq_le Bounds_jump Bounds_rpow_key Bounds_le_of_sqrt
  Bounds_le_of_sq Bounds_final Bounds_one_le_size Bounds_gridStep_nonneg Bounds_gridTime_zero Bounds_gridTime_mono
  Bounds_gridTime_le Bounds_sum_le from RBM3D.Universality.GUEPhase.BoundsA

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Topology Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

/-! ## 1. The entry bound at the stopped grid times and the two `E^{(G)}` drift lines -/

section HypBBAEntry

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent on the block-product index is the reindexed resolvent on the fine lattice. -/
private theorem HypBBA_Gres_blockMat (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) :
    Gres (blockMat d L W H) z true = (green H z).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold Gres blockMat green
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_submatrix_equiv]

/-- The centre `M = Mres (g Ψ_I) E m` of the BA local law on the block-product index is `M^{(B)} ⊗ 1` with diagonal `m`. -/
private theorem HypBBA_Mres_blockMat {g E : ℝ} {m : ℂ} (hm : 0 < m.im) (u v : Vtx d L W) :
    blockMat d L W (Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m) u v =
      if u.2 = v.2 then BAMB d L g (E : ℂ) m u.1 v.1 else 0 := by
  have h := BAMres_fine_apply d L W g (E : ℂ) m (by simpa using hm.ne') ((splitEquiv d L W).symm u)
    ((splitEquiv d L W).symm v)
  have hu' : split d L W ((splitEquiv d L W).symm u) = u := (splitEquiv d L W).apply_symm_apply u
  have hv' : split d L W ((splitEquiv d L W).symm v) = v := (splitEquiv d L W).apply_symm_apply v
  rw [hu', hv'] at h
  exact h

/-- **The BA lower-bound step** (the analogue of `gue_inv_W_le_loopMax`, through `GreenLocal_floor_sample`): on the entry good event
`‖G - M‖_max ≤ δ ≤ κ/2`, `M = Mres (g Ψ_I) E m`, `|m| ≥ κ` (`BAReal`), `W^{-d} ≤ (4/κ²) max 𝓛^{(2)}`. -/
theorem HypBBA_inv_W_le_loopMax {g E : ℝ} {m : ℂ} {κ δ : ℝ} (hκ : 0 < κ) (hr : BAReal d L g κ E m) (u : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (hδ : δ ≤ κ / 2)
    (hΩ : ∀ i j : Idx d L W,
      ‖(green H (ztOf m E u) - Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m) i j‖ ≤ δ) :
    ((W : ℝ) ^ d)⁻¹ ≤ 4 / κ ^ 2 * RBM.Ind.loopMax d L W (blockMat d L W H) (ztOf m E u) 2 := by
  have hmpos : 0 < m.im := lt_of_lt_of_le hκ hr.2
  have hκm : κ ≤ ‖m‖ := hr.2.trans (Complex.abs_im_le_norm m |>.trans' (le_abs_self _))
  have hΩ' : ∀ u' v' : Vtx d L W,
      ‖Gres (blockMat d L W H) (ztOf m E u) true u' v' -
        blockMat d L W (Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m) u' v'‖ ≤ δ := by
    intro u' v'
    have h := hΩ ((splitEquiv d L W).symm u') ((splitEquiv d L W).symm v')
    rw [HypBBA_Gres_blockMat]
    simpa [blockMat, Matrix.sub_apply] using h
  have hfl := GreenLocal_floor_sample (d := d) (L := L) (W := W) (G := Gres (blockMat d L W H) (ztOf m E u) true)
    (M := blockMat d L W (Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m)) (Mb := BAMB d L g (E : ℂ) m) (m := m)
    hκ (HypBBA_Mres_blockMat hmpos) (fun a => BAMB_diag_eq d L g (E : ℂ) m hr.1 a) hκm hδ hΩ' 0
  refine hfl.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 := GUEEntry_norm_loop_eq H hH (ztOf m E u) 0 0
  rw [← h1]
  exact (Finset.le_sup' (fun p : Zd d L × Zd d L => ‖loopFine d L W H (ztOf m E u) ![true, false] ![p.1, p.2]‖)
    (Finset.mem_univ ((0 : Zd d L), (0 : Zd d L)))).trans (EntryGridBA_maxLoop_le m E u H)

/-- **`ε ≤ ‖G - M‖_max`** at BA (the analogue of `Hyp_eps_le_dev`): the weight `⟨G(σ) E_a⟩ - m_σ` of the `E^{(G)}` drift is a block
average of the diagonal of `G - M` (`M_xx = m`, `BAMB_diag_eq`; for `σ = -`, of its complex conjugate). -/
theorem HypBBA_eps_le_dev {g E : ℝ} {m : ℂ} (hr : BASelf d L g (E : ℂ) m) (u : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) {c : ℝ}
    (hc : ∀ i : Idx d L W,
      ‖(green H (ztOf m E u) - Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m) i i‖ ≤ c)
    (σ : Bool) (a : Zd d L) :
    ‖Matrix.trace (Gres (blockMat d L W H) (ztOf m E u) σ * Eblk d L W a) - mSigOf m σ‖ ≤ c := by
  have hm : 0 < m.im := hr.1
  have hid : Matrix.trace (Gres (blockMat d L W H) (ztOf m E u) σ * Eblk d L W a) - mSigOf m σ =
      Matrix.trace ((Gres (blockMat d L W H) (ztOf m E u) σ - mSigOf m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        Eblk d L W a) := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, trace_Eblk, smul_eq_mul,
      mul_one]
  rw [hid]
  refine Hyp_norm_trace_Eblk_le _ a fun p => ?_
  have hentry : ‖(Gres (blockMat d L W H) (ztOf m E u) true - mSigOf m true • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p p‖ ≤ c := by
    have h := hc ((splitEquiv d L W).symm p)
    have hMd : Mres ((g : ℂ) • PsiI d L W) (E : ℂ) m ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm p) = m := by
      have := HypBBA_Mres_blockMat (g := g) (E := E) hm p p
      simp only [blockMat, Matrix.submatrix_apply] at this
      rw [this]
      simp [BAMB_diag_eq d L g (E : ℂ) m hr]
    rw [Matrix.sub_apply, hMd] at h
    rw [HypBBA_Gres_blockMat]
    simpa [mSigOf, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply] using h
  cases σ
  · have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
    have hconj : Gres (blockMat d L W H) (ztOf m E u) false = (Gres (blockMat d L W H) (ztOf m E u) true)ᴴ :=
      (Hyp_Gres_conjTranspose hHb (ztOf m E u) true).symm
    have e : (Gres (blockMat d L W H) (ztOf m E u) false - mSigOf m false • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p p =
        star ((Gres (blockMat d L W H) (ztOf m E u) true - mSigOf m true • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p p) := by
      rw [hconj]
      simp [mSigOf, Matrix.sub_apply, Matrix.conjTranspose_apply]
    rw [e, norm_star]
    exact hentry
  · exact hentry

end HypBBAEntry

section HypBBALines

variable {d : ℕ} (sz : Sizes d)

/-- **The entry bound at the stopped grid times, at BA** (the analogue of `HypB_entry_le`): on the entry event (at level `c`, the
hypothesis `hD4`), for `j < σ*` every diagonal entry of `G_j - M` is at most `√(A c L₂)`, `A = 1 + 4/κ²` (the lower-bound step is
`HypBBA_inv_W_le_loopMax`; the band constant is `1 + 2 lam²`).  The threshold `δ_n = N^{-τ_U/4}` is `≤ κ/2` (`hδN`). -/
theorem HypB_entry_leBA {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {τU : ℝ}
    (n : ℕ) (hr : BAReal d (sz.L n) (g n) κ (E n) (m n)) (hδN : gueDelta sz τU n ≤ κ / 2)
    (ω : PathΩ (sz.withLam 0)) {c : ℝ} (hc : 0 ≤ c)
    (hD4 : ∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      {ω' : PathΩ (sz.withLam 0) | ∀ a b : Idx d (sz.L n) (sz.W n),
          ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω')
              (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a b‖ ≤ gueDelta sz τU n}.indicator
        (fun ω' => ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω')
              (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ^ 2) ω ≤
        c * (gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹))
    {j : ℕ} (hj : j < gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω)
    (q : Idx d (sz.L n) (sz.W n)) :
    ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω)
        (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) q q‖ ≤
      Real.sqrt ((1 + 4 / κ ^ 2) * c * gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω) := by
  have hσK : gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω ≤ gueGridK sz n0 n :=
    firstHit_le _ _ _ ω
  have hjK : j < gueGridK sz n0 n + 1 := by omega
  have hj' : j < firstHit (fun k ω' => gueDevBA sz g E t1 t0 m (gueGridK sz n0) n k ω')
      (gueDelta sz τU n) (gueGridK sz n0 n) ω := hj
  have hdev : gueDevBA sz g E t1 t0 m (gueGridK sz n0) n j ω < gueDelta sz τU n :=
    lt_firstHit_imp (fun k ω' => gueDevBA sz g E t1 t0 m (gueGridK sz n0) n k ω') (gueDelta sz τU n)
      (gueGridK sz n0 n) hj'
  have hentry : ∀ i i' : Idx d (sz.L n) (sz.W n),
      ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω)
        (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i i'‖ ≤ gueDelta sz τU n := by
    intro i i'
    refine le_trans ?_ hdev.le
    unfold gueDevBA
    exact le_ciSup (f := fun ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) =>
      ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω)
        (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) ij.1 ij.2‖)
      (Set.finite_range _).bddAbove (i, i')
  have h4 : ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω)
        (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) q q‖ ^ 2 ≤
      c * (gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
    have h := hD4 ⟨j, hjK⟩ q q
    rw [Set.indicator_of_mem (show ω ∈ {ω' : PathΩ (sz.withLam 0) | ∀ a b : Idx d (sz.L n) (sz.W n),
      ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω')
        (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a b‖ ≤ gueDelta sz τU n} from hentry)] at h
    exact h
  have hW := HypBBA_inv_W_le_loopMax hκ hr (gridTime t1 t0 (gueGridK sz n0) n j)
    (gueHBA_isHermitian sz g t1 t0 (gueGridK sz n0) n j ω) hδN hentry
  have hL0 : 0 ≤ gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω := RBM.Ind.loopMax_nonneg 2
  apply Real.le_sqrt_of_sq_le
  calc _ ≤ c * (gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := h4
    _ ≤ c * (gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω +
          4 / κ ^ 2 * gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω) := by gcongr; exact hW
    _ = (1 + 4 / κ ^ 2) * c * gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω := by ring

/-- `|L_k(J) - K̃_{u_k}(J)| ≤ D^{(|J|)}_k` for every well-formed `J`. -/
private theorem HypBBA_le_Dmax (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n k : ℕ) (ω : PathΩ (sz.withLam 0))
    (J : RBM.Loop.LoopIdx (Zd d (sz.L n))) (hJ : J.WF) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k)) J -
      Kt n (gridTime t1 t0 K n k) J‖ ≤ gueDmaxBA sz g E t1 t0 m K Kt n J.length k ω := by
  obtain ⟨x, hx⟩ := Hyp_exists_loopOf J hJ
  unfold gueDmaxBA
  have h := le_ciSup (f := fun x' : (Fin J.length → Bool) × (Fin J.length → Zd d (sz.L n)) =>
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k)) (loopOf x'.1 x'.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf x'.1 x'.2)‖) (Set.finite_range _).bddAbove x
  simp only [hx] at h
  exact h

/-- **The drift line for (7.45)G at BA** (even `2l`; the analogue of `HypB_eG_745`): `|𝓔̃| ≤ 2l A c N L₂ L_{2l}`, `A = 1 + 4/κ²`, from
`ε ≤ √(A c L₂)` (the conclusion of `HypB_entry_leBA`, on the diagonal of `G - M`) and the loop inequality `L_{2l+1} ≤ √L₂ L_{2l}`. -/
theorem HypB_eG_745BA {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (K : ℕ → ℕ) (n j : ℕ) (hr : BASelf d (sz.L n) (g n) (E n : ℂ) (m n))
    (ω : PathΩ (sz.withLam 0)) {c A : ℝ} (hc : 1 ≤ c) (hA : 1 ≤ A) {l : ℕ} (hl : 1 ≤ l)
    (hdiag : ∀ q : Idx d (sz.L n) (sz.W n),
      ‖(green (gueHBA sz g t1 t0 K n j ω) (ztOf (m n) (E n) (gridTime t1 t0 K n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) q q‖ ≤
      Real.sqrt (A * c * gueLmaxBA sz g E t1 t0 m K n 2 j ω))
    (x : (Fin (2 * l) → Bool) × (Fin (2 * l) → Zd d (sz.L n))) :
    ‖egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω)
        (loopOf x.1 x.2)‖ ≤
      (((2 * l : ℕ) : ℝ) * A * c * ((sz.size n : ℕ) : ℝ)) *
        (gueLmaxBA sz g E t1 t0 m K n 2 j ω * gueLmaxBA sz g E t1 t0 m K n (2 * l) j ω) := by
  set M := gueHBA sz g t1 t0 K n j ω with hMdef
  set u := gridTime t1 t0 K n j with hudef
  have hH : M.IsHermitian := gueHBA_isHermitian sz g t1 t0 K n j ω
  have hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hH.submatrix _
  set L2 := gueLmaxBA sz g E t1 t0 m K n 2 j ω with hL2
  set Ln := gueLmaxBA sz g E t1 t0 m K n (2 * l) j ω with hLn
  have hL20 : 0 ≤ L2 := RBM.Ind.loopMax_nonneg _
  have hLn0 : 0 ≤ Ln := RBM.Ind.loopMax_nonneg _
  have hlen : (loopOf x.1 x.2).length = 2 * l := HypB_loopOf_length _ _
  have hb := norm_egtNGUEOf_le (sz.L n) (sz.W n) (m n) (E n) u M (loopOf x.1 x.2)
    (ε := Real.sqrt (A * c * L2)) (B := Real.sqrt L2 * Ln)
    (fun σ a' => HypBBA_eps_le_dev hr u hH hdiag σ a')
    (fun k hk b => (Hyp_cutGlue_le (HypB_loopOf_wf _ _) hk b).trans (by
      rw [hlen]; exact gueLoopMax_odd_succ_le hHb (ztOf (m n) (E n) u) hl))
  rw [hlen, HypB_size_cast] at hb
  refine hb.trans ?_
  have hc0 : 0 ≤ c := by linarith
  have hac1 : 1 ≤ A * c := by nlinarith
  have hs : Real.sqrt (A * c * L2) * (Real.sqrt L2 * Ln) = Real.sqrt (A * c) * (L2 * Ln) := by
    rw [Real.sqrt_mul (by positivity) L2]
    have := Real.mul_self_sqrt hL20
    calc Real.sqrt (A * c) * Real.sqrt L2 * (Real.sqrt L2 * Ln)
        = Real.sqrt (A * c) * (Real.sqrt L2 * Real.sqrt L2) * Ln := by ring
      _ = Real.sqrt (A * c) * (L2 * Ln) := by rw [this]; ring
  have h3 : Real.sqrt (A * c) ≤ A * c := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hS : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((2 * l : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * Real.sqrt (A * c * L2) * (Real.sqrt L2 * Ln)
      = ((2 * l : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * (Real.sqrt (A * c) * (L2 * Ln)) := by
        rw [mul_assoc _ (Real.sqrt (A * c * L2)), hs]
    _ ≤ ((2 * l : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * (A * c * (L2 * Ln)) := by gcongr
    _ = _ := by ring

/-- **The drift line for (7.46)G at BA** (the analogue of `HypB_eG_746`): `|𝓔̃| ≤ l N D₁ L_{l+1}`, from `ε ≤ D^{(1)}` (`K̃ = m_σ` at
length `1`, the premise `hK1`, which is `Hyp_Kt_oneBA`). -/
theorem HypB_eG_746BA {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (K : ℕ → ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n j l : ℕ) (ω : PathΩ (sz.withLam 0))
    (hK1 : ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n (gridTime t1 t0 K n j) ⟨[σ], [a]⟩ = mSigOf (m n) σ)
    (x : (Fin l → Bool) × (Fin l → Zd d (sz.L n))) :
    ‖egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω)
        (loopOf x.1 x.2)‖ ≤
      ((l : ℝ) * ((sz.size n : ℕ) : ℝ)) *
        (gueDmaxBA sz g E t1 t0 m K Kt n 1 j ω * gueLmaxBA sz g E t1 t0 m K n (l + 1) j ω) := by
  have hlen : (loopOf x.1 x.2).length = l := HypB_loopOf_length _ _
  have hε : ∀ (σ : Bool) (a : Zd d (sz.L n)),
      ‖Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n j)) σ * Eblk d (sz.L n) (sz.W n) a) - mSigOf (m n) σ‖ ≤
        gueDmaxBA sz g E t1 t0 m K Kt n 1 j ω := by
    intro σ a
    have h1 : Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n j)) σ * Eblk d (sz.L n) (sz.W n) a) - mSigOf (m n) σ =
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n j)) ⟨[σ], [a]⟩ - Kt n (gridTime t1 t0 K n j) ⟨[σ], [a]⟩ := by
      rw [hK1 σ a]; simp [loopL]
    rw [h1]
    exact HypBBA_le_Dmax sz g E t1 t0 m K Kt n j ω ⟨[σ], [a]⟩ rfl
  have hb := norm_egtNGUEOf_le (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω)
    (loopOf x.1 x.2) hε
    (fun k hk b => by
      have := Hyp_cutGlue_le (L := sz.L n) (W := sz.W n)
        (H := blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
        (z := ztOf (m n) (E n) (gridTime t1 t0 K n j)) (HypB_loopOf_wf x.1 x.2) hk b
      rwa [hlen] at this)
  rw [hlen, HypB_size_cast] at hb
  refine hb.trans (le_of_eq ?_)
  unfold gueLmaxBA
  ring

end HypBBALines

/-! ## 2. The eventual and grid facts at BA (`d ≥ 3`) -/

section HypBBAFacts

variable {d : ℕ} (sz : Sizes d)

/-- `N η_u > 0` at `η_u = (1 - u) Im m`, `u ≤ t₀ < 1` (the analogue of `HypB_scale_pos`). -/
private theorem HypBBA_scale_pos {t0 : ℕ → ℝ} {m : ℕ → ℂ} {n : ℕ} (hm : 0 < (m n).im) (ht0 : t0 n < 1) {u : ℝ}
    (hu : u ≤ t0 n) : 0 < ((sz.size n : ℕ) : ℝ) * etaOf (m n) u := by
  unfold etaOf
  exact mul_pos (HypB_size_pos sz n) (mul_pos (by linarith) hm)

/-- `Im m ≤ 1` from `‖m‖ ≤ 1`. -/
theorem HypBBA_im_le_one {m : ℂ} (hm1 : ‖m‖ ≤ 1) : m.im ≤ 1 :=
  (le_abs_self _).trans ((Complex.abs_im_le_norm m).trans hm1)

/-- `δ_n = N^{-τ_U/4} ≤ κ/2` eventually (the analogue of `HypB_ev_delta`; at BA the margin `Im m ≥ κ` is `BAReal`). -/
theorem HypBBA_ev_delta {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (hsz : Tendsto sz.size atTop atTop) :
    ∀ᶠ n : ℕ in atTop, gueDelta sz τU n ≤ κ / 2 := by
  filter_upwards [hsz.eventually (eventually_le_rpow (κ / 2)⁻¹ (by positivity : 0 < τU / 4)),
    hsz.eventually (eventually_ge_atTop 1)] with n hN hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  unfold gueDelta
  rw [Real.rpow_neg hN0.le]
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (τU / 4) := Real.rpow_pos_of_pos hN0 _
  rw [inv_le_comm₀ hpos (by positivity)]
  exact hN

/-- Step-size input: `Δ ≤ t₀ - t₁ ≤ N^{-τ_U} η_{t₀} ≤ 1 - t₀` (the analogue of `HypB_step_le`). -/
theorem HypBBA_step_le {t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {τU : ℝ} (n0 n : ℕ) (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1)
    (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (h730 : t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n)) (hτU : 0 < τU) :
    gridStep t1 t0 (gueGridK sz n0) n ≤ 1 - t0 n := by
  have hNR : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := HypB_one_le_size sz n
  have hKR : (1 : ℝ) ≤ (gueGridK sz n0 n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (gueGridK_ne_zero sz n0 n)
  have hmi := HypBBA_im_le_one hm1
  have hη0 : 0 ≤ etaOf (m n) (t0 n) := by unfold etaOf; nlinarith
  have hη1 : etaOf (m n) (t0 n) ≤ 1 - t0 n := by unfold etaOf; nlinarith
  have hNp : ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hstep : gridStep t1 t0 (gueGridK sz n0) n ≤ t0 n - t1 n := by
    unfold gridStep
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc gridStep t1 t0 (gueGridK sz n0) n ≤ t0 n - t1 n := hstep
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaOf (m n) (t0 n) := h730
    _ ≤ 1 * etaOf (m n) (t0 n) := mul_le_mul_of_nonneg_right hNp hη0
    _ ≤ 1 - t0 n := by rw [one_mul]; exact hη1

/-- `‖K̃_t(J)‖ ≤ 1` on `[t₁, t₀]` for `2 ≤ |J| ≤ 2n₀`, from the bound at `τ_U/2` (the conclusion of `Hyp_Kt_detDomBA`) and
`(N η_t)^{-1} ≤ N^{-τ_U}` (the analogue of `HypB_Kt_le_one`). -/
theorem HypBBA_Kt_le_one {t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {τU : ℝ} (hτU : 0 < τU) (n0 n : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hm : 0 < (m n).im) (ht0 : t0 n < 1)
    (hK1 : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (J.length - 1))
    (hscale : (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU)) :
    ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1 := by
  intro t ht J hJ h2 hJn
  have hNR : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := HypB_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h := hK1 t ht J hJ h2 hJn
  have hst := HypBBA_scale_pos sz hm ht0 ht.2
  have hs0 := HypBBA_scale_pos sz hm ht0 (le_refl (t0 n))
  have hle : ((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n) ≤ ((sz.size n : ℕ) : ℝ) * etaOf (m n) t := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold etaOf
    nlinarith [ht.2]
  have hinv : (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) :=
    (inv_anti₀ hs0 hle).trans hscale
  have hNp1 : ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  have hNp0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := Real.rpow_nonneg hN0.le _
  have hpow : (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (J.length - 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := by
    calc (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (J.length - 1)
        ≤ (((sz.size n : ℕ) : ℝ) ^ (-τU)) ^ (J.length - 1) := pow_le_pow_left₀ (inv_nonneg.2 hst.le) hinv _
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ (-τU)) ^ 1 := pow_le_pow_of_le_one hNp0 hNp1 (by omega)
      _ = ((sz.size n : ℕ) : ℝ) ^ (-τU) := pow_one _
  have hcomb : ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
  calc ‖Kt n t J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (J.length - 1) := h
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * ((sz.size n : ℕ) : ℝ) ^ (-τU) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hN0.le _)
    _ ≤ 1 := hcomb

/-- Grid values of the stopped process `L^{(l)}` before the stopping index (the analogue of `HypB_Lproc_grid`). -/
theorem HypBBA_Lproc_grid (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n l j : ℕ)
    (ω : PathΩ (sz.withLam 0)) (ht10 : t1 n ≤ t0 n) (hj : j < gueStopBA sz g E t1 t0 m K δ n ω) :
    gueLprocBA sz g E t1 t0 m K δ n l (gridTime t1 t0 K n j) ω =
      RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n j)) l := by
  have hσK : gueStopBA sz g E t1 t0 m K δ n ω ≤ K n := firstHit_le _ _ _ ω
  rw [gueLprocBA_time sz g E t1 t0 m K δ n l j ht10 (by omega) ω, min_eq_left hj.le]
  rfl

/-- Grid values of the stopped process `D^{(l)}` before the stopping index (the analogue of `HypB_Dproc_grid`). -/
theorem HypBBA_Dproc_grid (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n l j : ℕ)
    (ω : PathΩ (sz.withLam 0)) (ht10 : t1 n ≤ t0 n) (hj : j < gueStopBA sz g E t1 t0 m K δ n ω) :
    gueDprocBA sz g E t1 t0 m K δ Kt n l (gridTime t1 t0 K n j) ω = gueDmaxBA sz g E t1 t0 m K Kt n l j ω := by
  have hσK : gueStopBA sz g E t1 t0 m K δ n ω ≤ K n := firstHit_le _ _ _ ω
  rw [gueDprocBA_time sz g E t1 t0 m K δ Kt n l j ht10 (by omega) ω, min_eq_left hj.le]

/-- Continuity of `u ↦ √(N⁻¹ η_u⁻²)` on `[t₁, t₀]` (the analogue of `HypB_sqrt_cont`). -/
theorem HypBBA_sqrt_cont {t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (n : ℕ) (hm : 0 < (m n).im) (ht0 : t0 n < 1) :
    ContinuousOn (fun u => Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaOf (m n) u)⁻¹ ^ 2))
      (Set.Icc (t1 n) (t0 n)) := by
  have hηc : Continuous fun u => etaOf (m n) u := by unfold etaOf; fun_prop
  have hη : ∀ u ∈ Set.Icc (t1 n) (t0 n), etaOf (m n) u ≠ 0 := fun u hu => by
    unfold etaOf
    exact (mul_pos (by linarith [hu.2]) hm).ne'
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_const.mul ((hηc.continuousOn.inv₀ hη).pow 2))

end HypBBAFacts

/-! ## 3. The pathwise bound at one length and one size index -/

section HypBBAPath

variable {d : ℕ} (sz : Sizes d)

/-- **The pathwise bound at one length `l`** (the analogue of `HypB_path`): on the good event, the
stopped interpolated `D_l(t)` is bounded by a constant times the right side
`N(t-t₁) sup g₁ + (Nη_t)^{-l} + N(t-t₁) sup g₃ + √(t-t₁) sup g₄`, for all `t ∈ [t₁, t₀]`. -/
private theorem HypBBA_path (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n l : ℕ) (ω : PathΩ (sz.withLam 0))
    (g3 g4 : ℝ → ℝ) {c Ce err A : ℝ}
    (hm : 0 < (m n).im) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hK0 : K n ≠ 0)
    (hl : 1 ≤ l) (hc : 1 ≤ c) (hA : 0 ≤ A) (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * A * (l : ℝ) ^ 2 * c * ((sz.size n : ℕ) : ℝ))
    (hΔ : gridStep t1 t0 K n ≤ 1 - t0 n)
    (herr : ∀ t ∈ Set.Icc (t1 n) (t0 n), err ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ l)
    (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n 0 ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2)‖ ≤ c * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n))⁻¹ ^ l)
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
    (hKt : ∀ j ≤ K n, ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ l →
      ‖Kt n (gridTime t1 t0 K n j) J‖ ≤ c * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n j))⁻¹ ^
        (J.length - 1))
    (heG : ∀ j < gueStopBA sz g E t1 t0 m K δ n ω, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 K n j) (gueHBA sz g t1 t0 K n j ω)
          (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 K n j))
    (hdisc : ∀ k ≤ K n, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2) -
        (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ err)
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) :
    gueDprocBA sz g E t1 t0 m K δ Kt n l t ω ≤ c * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) *
      (((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 l,
          ((((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ ^ (k - 1) +
            gueDprocBA sz g E t1 t0 m K δ Kt n k u ω) * gueDprocBA sz g E t1 t0 m K δ Kt n (l - k + 2) u ω)
          (t1 n) t
        + (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ l
        + ((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t) := by
  set S : ℝ := ((sz.size n : ℕ) : ℝ) with hSdef
  have hS0 : 0 < S := HypB_size_pos sz n
  set σ := gueStopBA sz g E t1 t0 m K δ n ω with hσdef
  have hσK : σ ≤ K n := firstHit_le _ _ _ ω
  have hc0 : 0 ≤ c := by linarith
  have hηpos : ∀ u, u ≤ t0 n → 0 < etaOf (m n) u := fun u hu => by unfold etaOf; exact mul_pos (by linarith) hm
  set g1 : ℝ → ℝ := fun u => ∑ k ∈ Finset.Icc 2 l,
    ((S * etaOf (m n) u)⁻¹ ^ (k - 1) + gueDprocBA sz g E t1 t0 m K δ Kt n k u ω) *
      gueDprocBA sz g E t1 t0 m K δ Kt n (l - k + 2) u ω with hg1def
  have hg1 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g1 u := by
    intro u hu
    refine Finset.sum_nonneg fun i _ => mul_nonneg (add_nonneg (pow_nonneg (inv_nonneg.2
      (mul_nonneg hS0.le (hηpos u hu.2).le)) _) (gueDprocBA_nonneg sz g E t1 t0 m K δ Kt n _ _ ω))
      (gueDprocBA_nonneg sz g E t1 t0 m K δ Kt n _ _ ω)
  have hηc : Continuous fun u => etaOf (m n) u := by unfold etaOf; fun_prop
  have hg1c : ContinuousOn g1 (Set.Icc (t1 n) (t0 n)) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.mul (ContinuousOn.add ?_ (gueDprocBA_continuousOn sz g E t1 t0 m K δ Kt n _ ω))
      (gueDprocBA_continuousOn sz g E t1 t0 m K δ Kt n _ ω)
    refine ContinuousOn.pow (ContinuousOn.inv₀ (continuous_const.mul hηc).continuousOn
      fun u hu => (mul_pos hS0 (hηpos u hu.2)).ne') _
  -- the bilinear drift, `Cf = 3 m² c S`
  have hF : ∀ j < σ, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n j))) (loopOf x.1 x.2) -
        primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤
        (3 * (l : ℝ) ^ 2 * c * S) * g1 (gridTime t1 t0 K n j) := by
    intro j hj x
    have hjK : j ≤ K n := (le_of_lt hj).trans hσK
    have hmin : min j σ = j := min_eq_left hj.le
    have hDp : ∀ i, gueDprocBA sz g E t1 t0 m K δ Kt n i (gridTime t1 t0 K n j) ω =
        gueDmaxBA sz g E t1 t0 m K Kt n i j ω := by
      intro i; rw [gueDprocBA_time sz g E t1 t0 m K δ Kt n i j ht10 hjK ω, ← hσdef, hmin]
    have hlen : (loopOf x.1 x.2).length = l := HypB_loopOf_length _ _
    have hb := HypB_bil (W := sz.W n)
      (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n j)))
      (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2) (HypB_loopOf_wf _ _)
      (fun i => gueDprocBA sz g E t1 t0 m K δ Kt n i (gridTime t1 t0 K n j) ω)
      (lam := (S * etaOf (m n) (gridTime t1 t0 K n j))⁻¹) hc
      (inv_nonneg.2 (mul_nonneg hS0.le (hηpos _ (Hyp_time_le ht10 hK0 hjK)).le))
      (fun i => gueDprocBA_nonneg sz g E t1 t0 m K δ Kt n i _ ω)
      (fun J hJ _ _ => by rw [hDp]; exact HypBBA_le_Dmax sz g E t1 t0 m K Kt n j ω J hJ)
      (fun J hJ h2 hJn => by rw [hlen] at hJn; exact hKt j hjK J hJ h2 hJn)
    rw [hlen, HypB_size_cast] at hb
    refine hb.trans (le_of_eq ?_)
    rw [hg1def]
  have hCf0 : 0 ≤ 3 * (l : ℝ) ^ 2 * c * S := by positivity
  set Λ0 := (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n))⁻¹ ^ l with hΛ0def
  set S1 := supOn g1 (t1 n) t with hS1def
  set S3 := supOn g3 (t1 n) t with hS3def
  set S4 := supOn g4 (t1 n) t with hS4def
  have hS1n : 0 ≤ S1 := supOn_nonneg fun u hu => hg1 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS3n : 0 ≤ S3 := supOn_nonneg fun u hu => hg3 u ⟨hu.1, hu.2.trans ht.2⟩
  have hS4n : 0 ≤ S4 := supOn_nonneg fun u hu => hg4 u ⟨hu.1, hu.2.trans ht.2⟩
  have hlam : ∀ k ≤ K n, gridTime t1 t0 K n k ≤ t + gridStep t1 t0 K n →
      (fun u => (((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ ^ l) (gridTime t1 t0 K n k) ≤
        2 ^ l * (fun u => (((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ ^ l) t := by
    intro k hk hkt
    simp only
    have hmem := Hyp_time_mem (K := K) ht10 hK0 hk
    have him := hm
    have hηk : etaOf (m n) t ≤ 2 * etaOf (m n) (gridTime t1 t0 K n k) := by
      unfold etaOf
      have h1 : (gridTime t1 t0 K n k - t) * (m n).im ≤
          gridStep t1 t0 K n * (m n).im :=
        mul_le_mul_of_nonneg_right (by linarith) him.le
      have h2 : gridStep t1 t0 K n * (m n).im ≤ (1 - t0 n) * (m n).im :=
        mul_le_mul_of_nonneg_right hΔ him.le
      have h3 : (1 - t0 n) * (m n).im ≤
          (1 - gridTime t1 t0 K n k) * (m n).im :=
        mul_le_mul_of_nonneg_right (by linarith [hmem.2]) him.le
      nlinarith
    have hpk := HypBBA_scale_pos sz hm ht0 hmem.2
    have hpt := HypBBA_scale_pos sz hm ht0 ht.2
    have hinv : (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ≤ 2 * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ := by
      rw [show (2 : ℝ) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ = 2 / (((sz.size n : ℕ) : ℝ) * etaOf (m n) t) by ring, inv_eq_one_div,
        div_le_div_iff₀ hpk hpt]
      nlinarith
    calc (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ l ≤ (2 * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹) ^ l :=
          pow_le_pow_left₀ (inv_nonneg.2 hpk.le) hinv l
      _ = 2 ^ l * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ l := by rw [mul_pow]
  have hint := Hyp_interp_bound (f := fun k => gueDmaxBA sz g E t1 t0 m K Kt n l k ω) hσK hK0 ht10
    ht (fun u => (((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ ^ l) (P := c * Λ0 + err) (Q := c)
    (A := 3 * (l : ℝ) ^ 2 * c * S * S1 + Ce * S3) (B := c * S4) (C := 2 ^ l) hc0
    (by positivity) (by positivity) hlam
    (fun k hk hkt => Hyp_gridBA sz g E t1 t0 m K δ Kt n l ω g1 g3 g4 ht10 hm ht0 hc0 hCf0 hCe0
      hg1 hg3 hg4 hg1c hg3c hg4c h0 hM hq hF heG hdisc ht hk hkt)
  have hLHS : gueDprocBA sz g E t1 t0 m K δ Kt n l t ω =
      gueInterp t1 t0 K n (fun k => gueDmaxBA sz g E t1 t0 m K Kt n l (min k σ) ω) t := rfl
  rw [hLHS]
  refine hint.trans ?_
  set X2 := (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ l with hX2def
  have hpt := HypBBA_scale_pos sz hm ht0 ht.2
  have hX2n : 0 ≤ X2 := pow_nonneg (inv_nonneg.2 hpt.le) _
  have hΛ0le : Λ0 ≤ X2 := by
    have hp1 := HypBBA_scale_pos sz hm ht0 ht10
    have hle : (((sz.size n : ℕ) : ℝ) * etaOf (m n) t) ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n)) := by
      refine mul_le_mul_of_nonneg_left ?_ hS0.le
      unfold etaOf
      have := hm
      nlinarith [ht.1]
    exact pow_le_pow_left₀ (inv_nonneg.2 hp1.le) (inv_anti₀ hpt hle) l
  have herr' := herr t ht
  have htt : 0 ≤ t - t1 n := by linarith [ht.1]
  have hsq : 0 ≤ Real.sqrt (t - t1 n) := Real.sqrt_nonneg _
  have hn2 : (0 : ℝ) ≤ (l : ℝ) ^ 2 := by positivity
  have h2n : (0 : ℝ) ≤ 2 ^ l := by positivity
  have hX1 : 0 ≤ S * (t - t1 n) * S1 := by positivity
  have hX3 : 0 ≤ S * (t - t1 n) * S3 := by positivity
  have hX4 : 0 ≤ Real.sqrt (t - t1 n) * S4 := by positivity
  have e1 : c * Λ0 + err + c * (2 ^ l * X2) ≤ c * (2 + 2 ^ l) * X2 := by
    have := mul_le_mul_of_nonneg_left hΛ0le hc0
    have : err ≤ c * X2 := herr'.trans (le_mul_of_one_le_left hX2n hc)
    nlinarith
  have e2 : (3 * (l : ℝ) ^ 2 * c * S * S1 + Ce * S3) * (t - t1 n) ≤
      c * ((3 + 4 * A) * (l : ℝ) ^ 2) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) := by
    have hCe' : Ce * S3 * (t - t1 n) ≤ 4 * A * (l : ℝ) ^ 2 * c * S * S3 * (t - t1 n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCe hS3n) htt
    have ha : 0 ≤ c * (l : ℝ) ^ 2 * (S * (t - t1 n) * S1) := by positivity
    have hb : 0 ≤ c * (l : ℝ) ^ 2 * (S * (t - t1 n) * S3) := by positivity
    nlinarith
  have e3 : c * S4 * Real.sqrt (t - t1 n) ≤
      c * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) := by
    have hK1 : (1 : ℝ) ≤ 2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2 := by
      have h1 : 0 ≤ (3 + 4 * A) * (l : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h2 : (0 : ℝ) ≤ 2 ^ l := by positivity
      linarith
    have hX : 0 ≤ c * (Real.sqrt (t - t1 n) * S4) := by positivity
    have h := mul_le_mul_of_nonneg_left hK1 hX
    calc c * S4 * Real.sqrt (t - t1 n) = c * (Real.sqrt (t - t1 n) * S4) * 1 := by ring
      _ ≤ c * (Real.sqrt (t - t1 n) * S4) * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) := h
      _ = c * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) := by ring
  have hfin : c * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) *
      (S * (t - t1 n) * S1 + X2 + S * (t - t1 n) * S3 + Real.sqrt (t - t1 n) * S4) =
      c * (2 + 2 ^ l) * X2 + c * ((3 + 4 * A) * (l : ℝ) ^ 2) *
        (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
      c * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) * (Real.sqrt (t - t1 n) * S4) +
      (c * (2 + 2 ^ l) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
        c * ((3 + 4 * A) * (l : ℝ) ^ 2) * X2) := by ring
  have hextra : 0 ≤ c * (2 + 2 ^ l) * (S * (t - t1 n) * S1 + S * (t - t1 n) * S3) +
      c * ((3 + 4 * A) * (l : ℝ) ^ 2) * X2 := by
    have hq : 0 ≤ (3 + 4 * A) * (l : ℝ) ^ 2 := mul_nonneg (by linarith) hn2
    have h1 : 0 ≤ S * (t - t1 n) * S1 + S * (t - t1 n) * S3 := add_nonneg hX1 hX3
    have h2 : (0 : ℝ) ≤ 2 + 2 ^ l := by positivity
    exact add_nonneg (mul_nonneg (mul_nonneg hc0 h2) h1) (mul_nonneg (mul_nonneg hc0 hq) hX2n)
  rw [hfin]
  linarith
end HypBBAPath

/-! ## 4. The exponent bookkeeping at a fixed size index -/

section HypBBAFixed

variable {d : ℕ} (sz : Sizes d)

/-- **One length, one size index, one sample point** (the analogue of `HypB_fixed`; the constant `A` is a parameter, `A = 1 + 4/κ²` at BA): the eventual deterministic facts and the
good event at level `N^{τ/2}` give `D_l(t) ≤ N^τ · rhs(t)` for every `t ∈ [t₁, t₀]` (the bounds on
`K̃` and on the discretization error, the step-size conditions and the final absorption).
`N = sz.size n = (W L)^d`; since `1 ≤ sz.size n`, no hypotheses `1 ≤ N` or `W L ≤ N` are needed. -/
theorem HypB_fixedBA {τ : ℝ} (hτ : 0 < τ) (n0 : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (τU : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n l : ℕ) (ω : PathΩ (sz.withLam 0)) (g3 g4 : ℝ → ℝ) {Ce : ℝ}
    (hK : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (hl1 : 1 ≤ l) (hl : l ≤ 2 * n0)
    (hΔ : gridStep t1 t0 (gueGridK sz n0) n ≤ 1 - t0 n)
    (hgrid1 : ((2 * n0 : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ 1)
    (hgrid2 : 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ ≤
      (((sz.size n : ℕ) : ℝ)⁻¹) ^ (2 * n0))
    (hbd : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1)
    (hKtc : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ 2 * n0 →
      ‖Kt n t J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ (J.length - 1))
    (hbig : 2 + 2 ^ (2 * n0) + (3 + 4 * A) * ((2 * n0 : ℕ) : ℝ) ^ 2 ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hCe0 : 0 ≤ Ce)
    (hCe : Ce ≤ 4 * A * (l : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
      ((sz.size n : ℕ) : ℝ))
    (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u)
    (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n)))
    (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n)))
    (h0 : ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n 0 ω))
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf x.1 x.2) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n 0) (loopOf x.1 x.2)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n))⁻¹ ^ l)
    (hM : ∀ k ≤ gueGridK sz n0 n, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω))
            (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf x.1 x.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n 0 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf x.1 x.2)
          - (gridStep t1 t0 (gueGridK sz n0) n : ℂ) * ∑ j ∈ Finset.range k,
              genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
                (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω) (loopOf x.1 x.2)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Real.sqrt (gridTime t1 t0 (gueGridK sz n0) n k - t1 n) *
          (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω))
              (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * l)))
          + (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ l))
    (hq : ∀ j < gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω,
      Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
        (etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
        RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω))
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * l)) ≤
        g4 (gridTime t1 t0 (gueGridK sz n0) n j))
    (heG : ∀ j < gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω,
      ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖egtNGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
          (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω) (loopOf x.1 x.2)‖ ≤
        Ce * g3 (gridTime t1 t0 (gueGridK sz n0) n j))
    {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) :
    gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l t ω ≤
      ((sz.size n : ℕ) : ℝ) ^ τ *
      (((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 l,
          ((((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ ^ (k - 1) +
            gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n k u ω) *
            gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n (l - k + 2) u ω)
          (t1 n) t
        + (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ^ l
        + ((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t) := by
  have hNR : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := HypB_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set c := N ^ (τ / 2) with hcdef
  have hc : 1 ≤ c := Real.one_le_rpow hNR (by positivity)
  have hK0 : gueGridK sz n0 n ≠ 0 := gueGridK_ne_zero sz n0 n
  have hKR : (1 : ℝ) ≤ (gueGridK sz n0 n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hK0
  set Δ := gridStep t1 t0 (gueGridK sz n0) n with hΔdef
  have hΔ0 : 0 ≤ Δ := Hyp_step_nonneg ht10
  have hΔK : Δ ≤ ((gueGridK sz n0 n : ℝ))⁻¹ := by
    rw [hΔdef]; unfold gridStep
    rw [div_eq_mul_inv]
    have : t0 n - t1 n ≤ 1 := by linarith
    have hKi : 0 ≤ ((gueGridK sz n0 n : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
    have h0 : 0 ≤ t0 n - t1 n := by linarith
    calc (t0 n - t1 n) * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ 1 * ((gueGridK sz n0 n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right this hKi
      _ = ((gueGridK sz n0 n : ℝ))⁻¹ := one_mul _
  -- the discretization condition `M³ N Δ ≤ 1`
  have hsmall : ((2 * n0 : ℕ) : ℝ) ^ 3 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) * Δ ≤ 1 := by
    rw [HypB_size_cast]
    calc ((2 * n0 : ℕ) : ℝ) ^ 3 * N * Δ
        ≤ ((2 * n0 : ℕ) : ℝ) ^ 3 * N * ((gueGridK sz n0 n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hΔK (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hN0.le)
      _ ≤ 1 := hgrid1
  have hK' : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 2 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t := fun t ht I hI h1 h2 => hK t ht I hI h1 (by omega)
  set err := 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * Δ * (t0 n - t1 n) with herrdef
  have hdisc : ∀ k ≤ gueGridK sz n0 n, ∀ x : (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
      ‖Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf x.1 x.2) -
          Kt n (gridTime t1 t0 (gueGridK sz n0) n 0) (loopOf x.1 x.2) -
        (Δ : ℂ) * ∑ j ∈ Finset.range k,
          primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 (gueGridK sz n0) n j))
            (loopOf x.1 x.2)‖ ≤ err := fun k hk x => by
    have h := Hyp_Kt_disc sz Kt ht10 hK0 hK' hbd hsmall hk (loopOf x.1 x.2)
      (HypB_loopOf_wf _ _) (by rw [HypB_loopOf_length]; exact hl1)
      (by rw [HypB_loopOf_length]; exact hl)
    rw [HypB_size_cast] at h
    exact h
  have herr : ∀ t' ∈ Set.Icc (t1 n) (t0 n), err ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) t')⁻¹ ^ l := by
    intro t' ht'
    have hsc := HypBBA_scale_pos sz hm ht0 ht'.2
    have hsN : (((sz.size n : ℕ) : ℝ) * etaOf (m n) t') ≤ N := by
      have hmi := HypBBA_im_le_one hm1
      have hη1 : etaOf (m n) t' ≤ 1 := by unfold etaOf; nlinarith [ht'.1, ht'.2]
      have hη0 : 0 ≤ etaOf (m n) t' := by unfold etaOf; nlinarith [ht'.2]
      nlinarith
    have hinv : N⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) t')⁻¹ := inv_anti₀ hsc hsN
    have hNi1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNR
    have hNi0 : 0 ≤ N⁻¹ := inv_nonneg.2 hN0.le
    calc err ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ := by
          rw [herrdef]
          have h1 : t0 n - t1 n ≤ 1 := by linarith
          have h2 : 0 ≤ t0 n - t1 n := by linarith
          have h4 : Δ * (t0 n - t1 n) ≤ ((gueGridK sz n0 n : ℝ))⁻¹ := by
            calc Δ * (t0 n - t1 n) ≤ Δ * 1 := mul_le_mul_of_nonneg_left h1 hΔ0
              _ ≤ _ := by rw [mul_one]; exact hΔK
          have h5 : (0 : ℝ) ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 :=
            mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
              (sq_nonneg _)
          calc 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * Δ * (t0 n - t1 n)
              = 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * (Δ * (t0 n - t1 n)) := by ring
            _ ≤ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * N ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_left h4 h5
      _ ≤ (N⁻¹) ^ (2 * n0) := hgrid2
      _ ≤ (N⁻¹) ^ l := pow_le_pow_of_le_one hNi0 hNi1 hl
      _ ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) t')⁻¹ ^ l := pow_le_pow_left₀ hNi0 hinv l
  -- the bound on `K̃` on the grid
  have hKt : ∀ j ≤ gueGridK sz n0 n, ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ l → ‖Kt n (gridTime t1 t0 (gueGridK sz n0) n j) J‖ ≤
        c * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ (J.length - 1) :=
    fun j hj J hJ h2 hJn => hKtc _ (Hyp_time_mem ht10 hK0 hj) J hJ h2 (hJn.trans hl)
  have hn2 : (l : ℝ) ^ 2 ≤ ((2 * n0 : ℕ) : ℝ) ^ 2 := by
    have : (l : ℝ) ≤ ((2 * n0 : ℕ) : ℝ) := by exact_mod_cast hl
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hpath := HypBBA_path sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l ω g3 g4 (c := c)
    (Ce := Ce) (err := err) (A := A) hm ht10 ht0 hK0 hl1 hc hA hCe0 hCe hΔ herr hg3 hg4 hg3c hg4c h0 hM hq
    hKt heG hdisc ht
  set R := N * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 l,
          ((N * etaOf (m n) u)⁻¹ ^ (k - 1) +
            gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n k u ω) *
            gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n (l - k + 2) u ω)
          (t1 n) t
        + (N * etaOf (m n) t)⁻¹ ^ l
        + N * (t - t1 n) * supOn g3 (t1 n) t
        + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t with hRdef
  have hK0' : (0 : ℝ) < 2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2 := by
    have h1 : 0 ≤ (3 + 4 * A) * (l : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : (0 : ℝ) < 2 ^ l := by positivity
    linarith
  have hDp0 := gueDprocBA_nonneg sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l t ω
  have hcpos : 0 < c := by linarith
  have hR0 : 0 ≤ R := by
    by_contra hneg
    push Not at hneg
    have : c * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) * R < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hcpos hK0') hneg
    linarith
  have hKn : 2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2 ≤ c := by
    have h2 : (2 : ℝ) ^ l ≤ 2 ^ (2 * n0) := pow_le_pow_right₀ (by norm_num) hl
    have h3 : (3 + 4 * A) * (l : ℝ) ^ 2 ≤ (3 + 4 * A) * ((2 * n0 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hn2 (by linarith)
    rw [hcdef]
    linarith
  have hNτ : N ^ τ = c * c := by
    rw [hcdef, ← Real.rpow_add hN0]; ring_nf
  calc gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l t ω
      ≤ c * (2 + 2 ^ l + (3 + 4 * A) * (l : ℝ) ^ 2) * R := hpath
    _ ≤ c * c * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKn (by linarith)) hR0
    _ = N ^ τ * R := by rw [hNτ]
end HypBBAFixed

/-! ## 5. The pathwise unfreezing (the analogue of `BoundsA.lean`)

The band privates of `BoundsA` that carry no band token (`Bounds_unfreeze`, `Bounds_jump`, `Bounds_rpow_key`, ..., the grid
times) are used through `open private`; the entry bound, the deviation processes, the scale lemma and the jump step are
derived anew below at the flow `ztOf (m n) (E n)`, `η_u = (1 - u) Im m`, `M = Mres (g Ψ_I) E m`. -/

section BoundsBA

variable {d : ℕ} (sz : Sizes d)

/-- The conclusion of `Bounds_pathBA` at `(n, ω, τ)`: the two fields of `GUEPathBoundsBA` unfolded (the analogue of
`BoundsACheck.Concl`). -/
abbrev BoundsBA_Concl {d : ℕ} (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (τ : ℝ) (n : ℕ) (ω : PathΩ (sz.withLam 0)) : Prop :=
  (∀ l : ℕ, 1 ≤ l → l ≤ n0 → ∀ (k : Fin (gueGridK sz n0 n + 1)) (σ : Fin l → Bool) (a : Fin l → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf σ a) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf σ a)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ l) ∧
    (∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      ‖green (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω)
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) i j -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) i j‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ ((1 : ℝ) / 2))

/-- An entry of `G_k - M` is at most `gueDevBA` (the analogue of `Bounds_entry_le_dev`). -/
private theorem BoundsBA_entry_le_dev (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0))
    (a b : Idx d (sz.L n) (sz.W n)) :
    ‖(green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a b‖ ≤
      gueDevBA sz g E t1 t0 m K n k ω := by
  unfold gueDevBA
  exact le_ciSup (f := fun ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) =>
    ‖(green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) ij.1 ij.2‖)
    (Set.finite_range _).bddAbove (a, b)

/-- `gueDevBA` is at most any nonnegative entrywise bound (the analogue of `Bounds_dev_le`). -/
private theorem BoundsBA_dev_le (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0))
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b : Idx d (sz.L n) (sz.W n),
      ‖(green (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a b‖ ≤ c) :
    gueDevBA sz g E t1 t0 m K n k ω ≤ c := by
  unfold gueDevBA
  exact Real.iSup_le (fun ij => h ij.1 ij.2) hc

/-- A loop deviation is at most `gueDmaxBA` (the analogue of `Bounds_le_dmax`). -/
private theorem BoundsBA_le_dmax (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n l k : ℕ) (ω : PathΩ (sz.withLam 0))
    (σ : Fin l → Bool) (a : Fin l → Zd d (sz.L n)) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k)) (loopOf σ a) -
      Kt n (gridTime t1 t0 K n k) (loopOf σ a)‖ ≤ gueDmaxBA sz g E t1 t0 m K Kt n l k ω := by
  unfold gueDmaxBA
  exact le_ciSup (f := fun y : (Fin l → Bool) × (Fin l → Zd d (sz.L n)) =>
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k)) (loopOf y.1 y.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf y.1 y.2)‖)
    (Set.finite_range _).bddAbove (σ, a)

/-- **The scale inequality** `(W^d)⁻¹ ≤ (N η_u)⁻¹` on `[t₁, t₀]`, `N = sz.size n = W^d L^d`, `η_u = (1 - u) Im m`, `Im m ≤ ‖m‖ ≤ 1`:
`L^d η_u ≤ L^d (1 - t₁) ≤ 1` (the analogue of `Bounds_T3`). -/
private theorem BoundsBA_T3 {t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (n : ℕ) (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1) (ht0 : t0 n < 1)
    (hellN : ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1) {u : ℝ} (hu : u ∈ Set.Icc (t1 n) (t0 n)) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ := by
  have hmim : 0 < (m n).im := hm
  have hmim1 : (m n).im ≤ 1 := HypBBA_im_le_one hm1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have h1t : 0 ≤ 1 - t1 n := by linarith [hu.1]
  have hηpos : 0 < etaOf (m n) u := mul_pos hu1 hmim
  have hSpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Bounds_one_le_size sz n)
  have hstep1 : (1 - u) * (m n).im ≤ (1 - t1 n) * 1 :=
    mul_le_mul (by linarith [hu.1]) hmim1 hmim.le h1t
  have hLη : ((sz.L n : ℕ) : ℝ) ^ d * etaOf (m n) u ≤ 1 := by
    change ((sz.L n : ℕ) : ℝ) ^ d * ((1 - u) * (m n).im) ≤ 1
    calc ((sz.L n : ℕ) : ℝ) ^ d * ((1 - u) * (m n).im)
        ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((1 - t1 n) * 1) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ = ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) := by rw [mul_one]
      _ ≤ 1 := hellN
  have hSη : (((sz.size n : ℕ) : ℝ) * etaOf (m n) u) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
    have e : ((sz.size n : ℕ) : ℝ) * etaOf (m n) u
        = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * etaOf (m n) u) := by
      unfold Sizes.size; push_cast; rw [mul_pow]; ring
    rw [e]
    calc ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * etaOf (m n) u)
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * 1 := mul_le_mul_of_nonneg_left hLη (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ d := mul_one _
  exact inv_anti₀ (mul_pos hSpos hηpos) hSη

/-- **The jump step**: the increment term of `gueDevBA_succ_le` is at most `δ_n / 2` on the
truncation event (the analogue of `Bounds_jump_le`). -/
private theorem BoundsBA_jump_le {τU : ℝ} (n0 : ℕ) {t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (n : ℕ)
    (hτU : 0 < τU) (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (hscN : ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (j : ℕ) (ω : PathΩ (sz.withLam 0))
    (hF : ∀ i i' : Idx d (sz.L n) (sz.W n),
      ‖Sizes.seqXmat sz n (ω (j + 1)) i i'‖ ≤ ((sz.size n : ℕ) : ℝ)) :
    (etaOf (m n) (t0 n))⁻¹ ^ 2 *
        (Real.sqrt (gridStep t1 t0 (gueGridK sz n0) n / ((sz.size n : ℕ) : ℝ)) *
          ∑ i : Idx d (sz.L n) (sz.W n), ∑ i' : Idx d (sz.L n) (sz.W n),
            ‖Sizes.seqXmat sz n (ω (j + 1)) i i'‖ +
          gridStep t1 t0 (gueGridK sz n0) n) ≤ gueDelta sz τU n / 2 := by
  have hN1 : 1 ≤ sz.size n := Bounds_one_le_size sz n
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hK0 : gueGridK sz n0 n ≠ 0 := gueGridK_ne_zero sz n0 n
  have hmim : 0 < (m n).im := hm
  have hmim1 : (m n).im ≤ 1 := HypBBA_im_le_one hm1
  have hmim : 0 < (m n).im := hm
  have hmim1 : (m n).im ≤ 1 := HypBBA_im_le_one hm1
  have hMpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have ht0m : t0 n ∈ Set.Icc (t1 n) (t0 n) := ⟨ht10, le_rfl⟩
  have hη0 : 0 < etaOf (m n) (t0 n) := mul_pos (by linarith) hmim
  have hsc0 : (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) :=
    hscN (t0 n) ht0m
  have hq1 : ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hone : 1 ≤ ((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n) := by
    have := hsc0.trans hq1
    rwa [inv_le_one₀ (mul_pos hMpos hη0)] at this
  have heS : (etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    calc (etaOf (m n) (t0 n))⁻¹ = (etaOf (m n) (t0 n))⁻¹ * 1 := (mul_one _).symm
      _ ≤ (etaOf (m n) (t0 n))⁻¹ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n)) :=
          mul_le_mul_of_nonneg_left hone (inv_nonneg.2 hη0.le)
      _ = ((sz.size n : ℕ) : ℝ) := by field_simp
  have hΔ0 : 0 ≤ gridStep t1 t0 (gueGridK sz n0) n :=
    Bounds_gridStep_nonneg (K := gueGridK sz n0) ht10
  have hΔ : gridStep t1 t0 (gueGridK sz n0) n * (((sz.size n : ℕ) : ℝ) + 1) ^ 64 ≤ 1 := by
    have hKc : ((gueGridK sz n0 n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) + 1) ^ (32 * n0 + 64) := by
      unfold gueGridK; push_cast; ring
    have hKpos : (0 : ℝ) < (gueGridK sz n0 n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hK0
    have hXK : (((sz.size n : ℕ) : ℝ) + 1) ^ 64 ≤ (gueGridK sz n0 n : ℝ) := by
      rw [hKc]; exact pow_le_pow_right₀ (by linarith) (by omega)
    calc gridStep t1 t0 (gueGridK sz n0) n * (((sz.size n : ℕ) : ℝ) + 1) ^ 64
        ≤ gridStep t1 t0 (gueGridK sz n0) n * (gueGridK sz n0 n : ℝ) :=
          mul_le_mul_of_nonneg_left hXK hΔ0
      _ = t0 n - t1 n := by unfold gridStep; field_simp
      _ ≤ 1 := by linarith
  have hSg := Bounds_sum_le sz n (ω (j + 1)) hF
  have hδ1 : 1 / ((sz.size n : ℕ) : ℝ) ≤ gueDelta sz τU n := by
    have hη01 : etaOf (m n) (t0 n) ≤ 1 := by
      change (1 - t0 n) * (m n).im ≤ 1
      calc (1 - t0 n) * (m n).im ≤ 1 * 1 :=
            mul_le_mul (by linarith) hmim1 hmim.le (by norm_num)
        _ = 1 := one_mul 1
    calc 1 / ((sz.size n : ℕ) : ℝ) ≤ (((sz.size n : ℕ) : ℝ))⁻¹ := by rw [one_div]
      _ ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ :=
          inv_anti₀ (mul_pos hMpos hη0) (mul_le_of_le_one_right hMpos.le hη01)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) := hsc0
      _ ≤ gueDelta sz τU n := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hSg0 : 0 ≤ ∑ i : Idx d (sz.L n) (sz.W n), ∑ i' : Idx d (sz.L n) (sz.W n),
      ‖Sizes.seqXmat sz n (ω (j + 1)) i i'‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact Bounds_jump hN1 hN1' le_rfl (inv_nonneg.2 hη0.le) heS hΔ0 hΔ hSg0 hSg hδ1
/-- **Unfreezing and conclusion, pathwise at a fixed `n` and `ω`, at BA** (the analogue of `Bounds_path`): on the good events
the a-priori threshold `gueDelta sz τU` is never reached on the grid, the freezing index never acts, and the bootstrap outputs
give (7.28) and the local law against `M = Mres (g Ψ_I) E m` at every grid time.  Hypotheses (pathwise at the one `n` and the one
`ω`, `N = sz.size n`, `Λ_u = (N η_u)⁻¹`, `η_u = (1 - u) Im m`): `hA`, `hB` the outputs of `eq727GEAt` (at `2 n₀`) and `eq728GAt`
for `gueLprocBA`, `gueDprocBA` at the threshold `N^{τ₁}`; `hC` the entry bound (the pathwise form of the conclusion of `gueGrid_entry_boundBA'` at `δ = gueDelta sz τU`, threshold `N^{τ₁}`, bound `gueLmaxBA … 2 + (W^d)⁻¹`); `hD` the step-`0` local law at `t₁`;
`hF` the increment truncation; `hellN : L^d (1 - t₁) ≤ 1` gives `(W^d)⁻¹ ≤ Λ_u` on `[t₁, t₀]` (`Im m ≤ ‖m‖ ≤ 1`).  The band
hypothesis `|E n| < 2` is `0 < Im m n`, `‖m n‖ ≤ 1`.  Conclusion: the two fields of `GUEPathBoundsBA` unfolded at `n`, `ω`, `N^τ`. -/
theorem Bounds_pathBA {τU : ℝ} (n0 : ℕ) (hn0 : 2 ≤ n0) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ}
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n : ℕ) (hτU : 0 < τU)
    (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    {τ τ₁ : ℝ} (hτ₁0 : 0 < τ₁) (hτ₁τ : τ₁ < τ)
    (hscN : ∀ t ∈ Set.Icc (t1 n) (t0 n),
      (((sz.size n : ℕ) : ℝ) * etaOf (m n) t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hellN : ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1)
    (hsmallN : ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁ - τU / 2) ≤ 1 / 32)
    (h4N : 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - τ₁))
    (ω : PathΩ (sz.withLam 0))
    (hA : ∀ u : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0),
      gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n u.2 u.1 ω ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) u.1)⁻¹ ^ ((u.2 : ℕ) - 1))
    (hB : ∀ u : TimeIcc t1 t0 n × Set.Icc 1 n0,
      gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n u.2 u.1 ω ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) u.1)⁻¹ ^ (u.2 : ℕ))
    (hC : ∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      {ω' : PathΩ (sz.withLam 0) | ∀ a b : Idx d (sz.L n) (sz.W n),
          ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω')
              (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a b‖ ≤
          gueDelta sz τU n}.indicator
        (fun ω' => ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω')
              (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ^ 2) ω ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ *
          (gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹))
    (hD : ∀ i j : Idx d (sz.L n) (sz.W n),
      ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n 0 ω) (ztOf (m n) (E n) (t1 n)) -
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) i j‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t1 n))⁻¹ ^ ((1 : ℝ) / 2))
    (hF : ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n → ∀ i j : Idx d (sz.L n) (sz.W n),
      ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)) :
    BoundsBA_Concl sz g E t1 t0 m n0 Kt τ n ω := by
  classical
  have hN1 : 1 ≤ sz.size n := Bounds_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hp1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁0.le
  have hp0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := by linarith
  have hδpos : 0 < gueDelta sz τU n := Real.rpow_pos_of_pos hN0 _
  have hmim : 0 < (m n).im := hm
  have hη : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 < etaOf (m n) u := fun u hu =>
    mul_pos (by linarith [hu.2]) hmim
  have hK0 : gueGridK sz n0 n ≠ 0 := gueGridK_ne_zero sz n0 n
  have htime : ∀ k ≤ gueGridK sz n0 n,
      gridTime t1 t0 (gueGridK sz n0) n k ∈ Set.Icc (t1 n) (t0 n) := by
    intro k hk
    refine ⟨?_, Bounds_gridTime_le ht10 hK0 hk⟩
    have h := Bounds_gridTime_mono (K := gueGridK sz n0) ht10 (Nat.zero_le k)
    rwa [Bounds_gridTime_zero] at h
  have hΛ0 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ :=
    fun u hu => (inv_pos.2 (mul_pos hN0 (hη u hu))).le
  have hT3 : ∀ u ∈ Set.Icc (t1 n) (t0 n),
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * etaOf (m n) u)⁻¹ :=
    fun u hu => BoundsBA_T3 sz n hm hm1 ht0 hellN hu
  have hkey : 2 * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (-τU) ≤
      (gueDelta sz τU n / 4) ^ 2 :=
    Bounds_rpow_key hN0 hsmallN
  -- the entry bound `hC` at an step below the threshold: `|(G_j - l)_{ab}|² ≤ 2 p² Λ_{u_j}`
  have hsq : ∀ j ≤ gueGridK sz n0 n,
      j ≤ gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω →
      gueDevBA sz g E t1 t0 m (gueGridK sz n0) n j ω < gueDelta sz τU n →
      ∀ a b : Idx d (sz.L n) (sz.W n),
      ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω)
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a b‖ ^ 2 ≤
        2 * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 *
          ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j)))⁻¹ := by
    intro j hj hjσ hdev a b
    have hmem : ω ∈ {ω' : PathΩ (sz.withLam 0) | ∀ a b : Idx d (sz.L n) (sz.W n),
        ‖(green (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω')
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) -
        Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a b‖ ≤
          gueDelta sz τU n} :=
      fun a b => (BoundsBA_entry_le_dev sz g E t1 t0 m (gueGridK sz n0) n j ω a b).trans hdev.le
    have hCj := hC ⟨j, Nat.lt_succ_of_le hj⟩ a b
    rw [Set.indicator_of_mem hmem] at hCj
    have hAj := hA (⟨gridTime t1 t0 (gueGridK sz n0) n j, htime j hj⟩, ⟨2, le_rfl, by omega⟩)
    have hAj' : gueLmaxBA sz g E t1 t0 m (gueGridK sz n0) n 2 j ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
          ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j)))⁻¹ := by
      have e := gueLprocBA_time sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n 2 j ht10 hj ω
      rw [Nat.min_eq_left hjσ] at e
      have h21 : (2 : ℕ) - 1 = 1 := rfl
      have h : gueLprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n 2
          (gridTime t1 t0 (gueGridK sz n0) n j) ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
          ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j)))⁻¹ ^ ((2 : ℕ) - 1) := hAj
      rw [e, h21, pow_one] at h
      exact h
    exact (Bounds_sq_le hp1 hAj' (hT3 _ (htime j hj)) (hscN _ (htime j hj))
      (hΛ0 _ (htime j hj)) hCj).1
  have hσ : ∀ k ≤ gueGridK sz n0 n,
      (∀ i ≤ k, gueDevBA sz g E t1 t0 m (gueGridK sz n0) n i ω < gueDelta sz τU n) →
      k ≤ gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω :=
    fun k hk h => Bounds_le_firstHit
      (fun k ω' => gueDevBA sz g E t1 t0 m (gueGridK sz n0) n k ω') (gueDelta sz τU n)
      (gueGridK sz n0 n) ω hk h
  -- step `0` of the induction
  have h0 : gueDevBA sz g E t1 t0 m (gueGridK sz n0) n 0 ω < gueDelta sz τU n := by
    have hle : gueDevBA sz g E t1 t0 m (gueGridK sz n0) n 0 ω ≤ gueDelta sz τU n / 4 := by
      refine BoundsBA_dev_le sz g E t1 t0 m (gueGridK sz n0) n 0 ω (by positivity) fun a b => ?_
      have h := hD a b
      rw [← Real.sqrt_eq_rpow] at h
      have hmem1 : t1 n ∈ Set.Icc (t1 n) (t0 n) := ⟨le_rfl, ht10⟩
      have hx := Bounds_le_of_sqrt (norm_nonneg _) (hΛ0 _ hmem1) (hscN _ hmem1) hδpos.le hkey h
      rw [Bounds_gridTime_zero]
      exact hx
    linarith
  -- the one-step jump
  have hjump : ∀ j < gueGridK sz n0 n, gueDevBA sz g E t1 t0 m (gueGridK sz n0) n (j + 1) ω ≤
      gueDevBA sz g E t1 t0 m (gueGridK sz n0) n j ω + gueDelta sz τU n / 2 := fun j hj =>
    (gueDevBA_succ_le sz g E t1 t0 m (gueGridK sz n0) n j hm hm1 ht10 ht0 hj ω).trans
      (add_le_add le_rfl (BoundsBA_jump_le sz n0 n hτU hm hm1 ht1 ht10 ht0 hscN j ω
        (fun a b => hF (j + 1) (by omega) (by omega) a b)))
  -- the inductive step below the threshold
  have hstep : ∀ j < gueGridK sz n0 n,
      j ≤ gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω →
      gueDevBA sz g E t1 t0 m (gueGridK sz n0) n j ω < gueDelta sz τU n →
      gueDevBA sz g E t1 t0 m (gueGridK sz n0) n j ω ≤ gueDelta sz τU n / 4 := by
    intro j hj hjσ hdev
    refine BoundsBA_dev_le sz g E t1 t0 m (gueGridK sz n0) n j ω (by positivity) fun a b => ?_
    have hq : 2 * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 *
        ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j)))⁻¹ ≤
        2 * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (-τU) :=
      mul_le_mul_of_nonneg_left (hscN _ (htime j hj.le)) (by positivity)
    exact Bounds_le_of_sq (norm_nonneg _) hδpos.le (hsq j hj.le hjσ hdev a b) (hq.trans hkey)
  have hall := Bounds_unfreeze (K := gueGridK sz n0 n)
    (fun k => gueDevBA sz g E t1 t0 m (gueGridK sz n0) n k ω)
    (gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω) hσ h0 hstep hjump hδpos
  have hdev : ∀ k ≤ gueGridK sz n0 n,
      gueDevBA sz g E t1 t0 m (gueGridK sz n0) n k ω < gueDelta sz τU n :=
    fun k hk => hall k hk k le_rfl
  have hkσ : ∀ k ≤ gueGridK sz n0 n,
      k ≤ gueStopBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) n ω :=
    fun k hk => hσ k hk (hall k hk)
  have hpτ : ((sz.size n : ℕ) : ℝ) ^ τ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1' hτ₁τ.le
  refine ⟨fun l hm1 hmn k σ a => ?_, fun k i j => ?_⟩
  · have hk : (k : ℕ) ≤ gueGridK sz n0 n := Nat.lt_succ_iff.1 k.2
    have h1 := BoundsBA_le_dmax sz g E t1 t0 m (gueGridK sz n0) Kt n l k ω σ a
    have h2 := gueDprocBA_time sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l k ht10 hk ω
    rw [Nat.min_eq_left (hkσ k hk)] at h2
    have h3 : gueDprocBA sz g E t1 t0 m (gueGridK sz n0) (gueDelta sz τU) Kt n l
        (gridTime t1 t0 (gueGridK sz n0) n k) ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
        ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k)))⁻¹ ^ l :=
      hB (⟨gridTime t1 t0 (gueGridK sz n0) n k, htime k hk⟩, ⟨l, hm1, hmn⟩)
    rw [h2] at h3
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
          ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k)))⁻¹ ^ l :=
        mul_le_mul_of_nonneg_right hpτ (pow_nonneg (hΛ0 _ (htime k hk)) l)
  · have hk : (k : ℕ) ≤ gueGridK sz n0 n := Nat.lt_succ_iff.1 k.2
    have hx2 := hsq k hk (hkσ k hk) (hdev k hk) i j
    have hP : 2 * ((sz.size n : ℕ) : ℝ) ^ τ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
      have e : ((sz.size n : ℕ) : ℝ) ^ τ =
          ((sz.size n : ℕ) : ℝ) ^ (τ - τ₁) * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [e]; exact mul_le_mul_of_nonneg_right h4N hp0
    have hΛ := hΛ0 _ (htime k hk)
    rw [← Real.sqrt_eq_rpow]
    exact Bounds_final (norm_nonneg _) hΛ hp0 hP hx2

/-- **The interface fit**: if for every `τ > 0` the conclusion of `Bounds_pathBA` holds with high probability (on the size scale),
then `GUEPathBoundsBA` holds, by `stochDomAt_of_forall_highProbAt` applied to the two fields (the analogue of
`BoundsACheck.pathBounds_of_forall_highProbAt`). -/
theorem pathBounds_of_forall_highProbAtBA (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hmain : ∀ τ : ℝ, 0 < τ → HighProbAt (Pgue (sz.withLam 0)) sz.size
      (fun n => {ω : PathΩ (sz.withLam 0) | BoundsBA_Concl sz g E t1 t0 m n0 Kt τ n ω})) :
    GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz n0) n0 Kt := by
  refine ⟨fun l hl1 hln => stochDomAt_of_forall_highProbAt fun τ hτ => ?_,
    stochDomAt_of_forall_highProbAt fun τ hτ => ?_⟩
  · exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (hmain τ hτ)
      (Filter.Eventually.of_forall fun n ω hω u => hω.1 l hl1 hln u.1 u.2.1 u.2.2)
  · exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (hmain τ hτ)
      (Filter.Eventually.of_forall fun n ω hω u => hω.2 u.1 u.2.1 u.2.2)

end BoundsBA


end RBM.BA

end
