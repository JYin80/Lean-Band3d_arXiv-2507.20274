/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Markov
import RBM3D.Path.OneStep

/-!
# The one-step conditional drift on the walk (ST2-21, part 1)

Ticket T2083 (ST2-21).  Port of `RBM2D/Path/LoopStep.lean` at commit `c9a24cf` (cited
`LoopStep:<line>`) onto the merged MD layer (`RBM3D/Path/{Walk,Markov}`, `RBM3D/Gauss/FineModel`,
`RBM3D/Loop/GLoopFlow`) and the one-step envelope of T2072 (`RBM3D/Path/OneStep.lean`).
Renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`; in addition (merged vocabulary):
`gloop L W H z I` is `loopL d L W H z I`, `spectralZ` is `zt`, `Gsig` is `Gres`,
`BlockIndex L W` is `Vtx d L W`, `norm_gloop_le_crude` and `continuous_matrixTrace` are those of
`RBM3D/Gauss/FlowCalculus.lean`.

* `RBM.Path.pathH_succ`: the one-step recursion `H_{k+1} = H_k + √Δ X_{k+1}` (`LoopStep:48`).
* `RBM.Path.condExp_loop_step`: the freezing lemma applied to the loop observable
  (`LoopStep:205`): the conditional mean at `filt sz k` is the Gaussian integral over the one-size
  law `PF d (sz.L n) (sz.W n) (sz.lam n)` (`Sizes.seqP_map_slice`).
* `RBM.Path.condExp_loop_drift`: the drift bound by the merged envelope `oneStepEnvelope`
  (`LoopStep:307`), pointwise at `M = pathH k ω`.

As in RBM2D, the freeze is applied to the observable of the Hermitian part
`½ (A + Aᴴ)` (continuous and bounded everywhere, equal to the observable at Hermitian matrices).
Every other helper is `private`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable {d : ℕ} (sz : Sizes d)

/-! ### The one-step recursion -/

/-- **The grid walk one-step recursion** `H_{k+1} = H_k + √Δ X_{k+1}` (RBM1D `H_succ`,
`Gauss/GridLoopStep.lean:74`; RBM2D `Path/LoopStep.lean:48`). -/
theorem pathH_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    pathH sz s t K n (k + 1) ω
      = pathH sz s t K n k ω
        + (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n (ω (k + 1)) := by
  have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  unfold pathH
  rw [hins, Finset.sum_insert hnotmem, smul_add]
  abel

/-! ### The complex-valued freezing lemma -/

section FreezeC

variable {sz}

/-- The complex-valued freezing lemma (RBM1D `condExp_freezeC`, `Gauss/GridLoopStep.lean:229`;
RBM2D `Path/LoopStep.lean:68`).  The merged `condExp_freeze` is real-valued; the complex case is
its real and imaginary parts, glued with `ContinuousLinearMap.comp_condExp_comm`. -/
private theorem LoopStep_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : PathΩ sz → β} (hY : Measurable[filt sz k] Y)
    {F : β → Sizes.SeqΩ sz → ℂ} (hF : Measurable (fun p : β × Sizes.SeqΩ sz => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (Sizes.seqP sz))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (pathP sz)) :
    (pathP sz)[fun ω => F (Y ω) (ω (k + 1)) | filt sz k]
      =ᵐ[pathP sz] fun ω => ∫ x, F (Y ω) x ∂(Sizes.seqP sz) := by
  classical
  set f : PathΩ sz → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Sizes.SeqΩ sz → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Sizes.SeqΩ sz → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Sizes.SeqΩ sz => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Sizes.SeqΩ sz => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (pathP sz) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (pathP sz) := hInt.im
  have hfreezeRe := condExp_freeze k hY hFre hIntRe
  have hfreezeIm := condExp_freeze k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt sz k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt sz k) hInt
  have hReComb : (fun ω => RCLike.re ((pathP sz)[f | filt sz k] ω))
      =ᵐ[pathP sz] fun ω => ∫ x, Fre (Y ω) x ∂(Sizes.seqP sz) := by
    have hRe' : (fun ω => RCLike.re ((pathP sz)[f | filt sz k] ω))
        =ᵐ[pathP sz] (pathP sz)[fun ω => Fre (Y ω) (ω (k + 1)) | filt sz k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((pathP sz)[f | filt sz k] ω))
      =ᵐ[pathP sz] fun ω => ∫ x, Fim (Y ω) x ∂(Sizes.seqP sz) := by
    have hIm' : (fun ω => RCLike.im ((pathP sz)[f | filt sz k] ω))
        =ᵐ[pathP sz] (pathP sz)[fun ω => Fim (Y ω) (ω (k + 1)) | filt sz k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂(Sizes.seqP sz) = RCLike.re (∫ x, F p x ∂(Sizes.seqP sz)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂(Sizes.seqP sz) = RCLike.im (∫ x, F p x ∂(Sizes.seqP sz)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((pathP sz)[f | filt sz k] ω) = RCLike.re (∫ x, F (Y ω) x ∂(Sizes.seqP sz))
    rw [hωre, hreEq]
  · change RCLike.im ((pathP sz)[f | filt sz k] ω) = RCLike.im (∫ x, F (Y ω) x ∂(Sizes.seqP sz))
    rw [hωim, himEq]

end FreezeC

/-! ### The observable of the Hermitian part: continuity and a global bound -/

section Observable

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The Hermitian part `½ (A + Aᴴ)` (`LoopStep:119`). -/
private def LoopStep_herm (A : Matrix (Idx d L W) (Idx d L W) ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem LoopStep_herm_isHermitian (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    (LoopStep_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem LoopStep_herm_of_isHermitian {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) : LoopStep_herm A = A := by
  unfold LoopStep_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem LoopStep_continuous_herm :
    Continuous (LoopStep_herm : Matrix (Idx d L W) (Idx d L W) ℂ → _) := by
  unfold LoopStep_herm
  have h1 : Continuous fun A : Matrix (Idx d L W) (Idx d L W) ℂ => Aᴴ :=
    continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- The loop observable of the Hermitian part of a matrix (`LoopStep:140`). -/
private def LoopStep_Phi (d L W : ℕ) [NeZero L] [NeZero W] (z : ℂ) (I : Loop.LoopIdx (Zd d L))
    (A : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
  loopL d L W (blockMat d L W (LoopStep_herm A)) z I

/-- Continuity of a resolvent loop along a continuous Hermitian family (`LoopStep:146`). -/
private theorem LoopStep_continuous_gloop {V : Type*} [TopologicalSpace V]
    {f : V → Matrix (Vtx d L W) (Vtx d L W) ℂ} (hf : Continuous f)
    (hh : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    Continuous fun v => loopL d L W (f v) z I := by
  have hG : ∀ σ : Bool, Continuous fun v => Gres (f v) z σ := by
    intro σ
    cases σ with
    | true => exact continuous_green_of_isHermitian hf hh hz
    | false =>
        apply continuous_green_of_isHermitian hf hh
        simpa using hz
  have hfold : ∀ l : List (Bool × Zd d L), Continuous fun v =>
      l.foldr (fun p M => Gres (f v) z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
    intro l
    induction l with
    | nil => exact continuous_const
    | cons p l ih => exact (((hG p.1).mul continuous_const)).mul ih
  exact (continuous_matrixTrace d L W).comp (hfold (I.σ.zip I.a))

private theorem LoopStep_continuous_Phi {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) :
    Continuous (LoopStep_Phi d L W z I) := by
  unfold LoopStep_Phi
  exact LoopStep_continuous_gloop (f := fun A => blockMat d L W (LoopStep_herm A))
    ((LoopStep_continuous_herm (d := d) (L := L) (W := W)).matrix_submatrix _ _)
    (fun A => (LoopStep_herm_isHermitian A).submatrix _) hz I

private theorem LoopStep_norm_Phi_le {z : ℂ} (hz : z.im ≠ 0) {I : Loop.LoopIdx (Zd d L)}
    (hwf : I.WF) (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ‖LoopStep_Phi d L W z I A‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * (|z.im|⁻¹ * (((W : ℝ) ^ d)⁻¹)) ^ I.a.length :=
  norm_gloop_le_crude d L W ((LoopStep_herm_isHermitian A).submatrix _) (abs_pos.mpr hz) le_rfl I
    hwf

private theorem LoopStep_isHermitian_add_smul {p X : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hp : p.IsHermitian) (hX : X.IsHermitian) (r : ℝ) :
    (p + (r : ℂ) • X).IsHermitian :=
  hp.add (hX.smul (by simp [IsSelfAdjoint]))

end Observable

/-! ### The one-step conditional expectation -/

/-- A private copy of the (private) `StandardBorelSpace` instance of `Markov.lean`. -/
private instance LoopStep_instStandardBorelSpaceMatrix (n : ℕ) :
    StandardBorelSpace (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ))

/-- The grid walk is `filt sz k`-measurable as a matrix-valued map (entrywise from
`pathH_adapted`). -/
private theorem LoopStep_measurable_pathH_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt sz k] (pathH sz s t K n k) :=
  @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun i =>
    @measurable_pi_iff _ _ _ (filt sz k) _ _ |>.mpr fun j =>
      (pathH_adapted sz s t K n k i j).measurable

/-- **`condExp_loop_step`**: the freezing lemma applied to the one-step recursion `pathH_succ`, for
the loop observable `Φ_{u_{k+1}} = 𝓛(blockMat ·, z_{u_{k+1}}, I)` (RBM1D `condExp_loop_step`,
`Gauss/GridLoopStep.lean:300`; RBM2D `Path/LoopStep.lean:205`).  The right side is the Gaussian
integral over the one-size law `PF d (sz.L n) (sz.W n) (sz.lam n)`, as in the pin
`OneStepEnvelope`.  Needs `u_{k+1} < 1` only (so that `Im z_{u_{k+1}} > 0`). -/
theorem condExp_loop_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (hE : |E| < 2)
    {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF) (hu1 : gridTime s t K n (k + 1) < 1) :
    (pathP sz)[fun ω : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (k + 1) ω))
          (zt E (gridTime s t K n (k + 1))) I | filt sz k]
      =ᵐ[pathP sz] fun ω =>
        ∫ x, loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n k ω
            + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) x))
          (zt E (gridTime s t K n (k + 1))) I ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  classical
  have hz : (zt E (gridTime s t K n (k + 1))).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (sub_pos.2 hu1) (spectralM_im_pos hE)).ne'
  set z : ℂ := zt E (gridTime s t K n (k + 1)) with hzdef
  set Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
    LoopStep_Phi d (sz.L n) (sz.W n) z I with hΦdef
  have hΦcont : Continuous Φ := LoopStep_continuous_Phi hz I
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → Sizes.SeqΩ sz → ℂ :=
    fun p x => Φ (p + (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n x) with hFdef
  have hXmeas : Measurable (Sizes.seqXmat sz n) :=
    (continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice sz n)
  have hFmeas : Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
      Sizes.SeqΩ sz => F p.1 p.2) := by
    have h2 : Measurable fun x : Sizes.SeqΩ sz =>
        (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n x :=
      hXmeas.const_smul (Real.sqrt (gridStep s t K n) : ℂ)
    have h3 : Measurable fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
        Sizes.SeqΩ sz => p.1 + (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n p.2 :=
      measurable_fst.add (h2.comp measurable_snd)
    have h4 := hΦcont.measurable.comp h3
    exact h4
  have hFbdd : ∀ p x, ‖F p x‖ ≤ (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) *
      (|z.im|⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) ^ I.a.length :=
    fun p x => LoopStep_norm_Phi_le hz hwf _
  have hYmeas : Measurable[filt sz k] (pathH sz s t K n k) :=
    LoopStep_measurable_pathH_filt sz s t K n k
  have hYmeas' : Measurable (pathH sz s t K n k) := hYmeas.mono ((filt sz).le k) le_rfl
  have hFInt : ∀ p, Integrable (F p) (Sizes.seqP sz) := by
    intro p
    have hpair : Measurable (fun x : Sizes.SeqΩ sz => (p, x)) :=
      measurable_const.prodMk measurable_id
    have hm : Measurable (fun x : Sizes.SeqΩ sz => F p x) := by
      have h := hFmeas.comp hpair
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun x => hFbdd p x)).integrable le_top
  have hIntTarget : Integrable (fun ω : PathΩ sz => F (pathH sz s t K n k ω) (ω (k + 1)))
      (pathP sz) := by
    have hm : Measurable (fun ω : PathΩ sz => F (pathH sz s t K n k ω) (ω (k + 1))) := by
      have h := hFmeas.comp (hYmeas'.prodMk (measurable_pi_apply (k + 1)))
      exact h
    exact (memLp_top_of_bound hm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => hFbdd _ _)).integrable le_top
  have hEq : (fun ω : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (k + 1) ω)) z I)
      = fun ω => F (pathH sz s t K n k ω) (ω (k + 1)) := by
    funext ω
    have hH : (pathH sz s t K n (k + 1) ω).IsHermitian := pathH_isHermitian sz s t K n (k + 1) ω
    change _ = LoopStep_Phi d (sz.L n) (sz.W n) z I _
    rw [← pathH_succ sz s t K n k ω]
    unfold LoopStep_Phi
    rw [LoopStep_herm_of_isHermitian hH]
  rw [hEq]
  filter_upwards [LoopStep_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget] with ω hω
  rw [hω]
  have hp : (pathH sz s t K n k ω).IsHermitian := pathH_isHermitian sz s t K n k ω
  set f : Ω d (sz.L n) (sz.W n) → ℂ := fun y =>
    loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n k ω
        + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y)) z I with hfdef
  have hfeq : f = fun y => Φ (pathH sz s t K n k ω
      + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y) := by
    funext y
    have hh := LoopStep_isHermitian_add_smul hp (Xmat_isHermitian d (sz.L n) (sz.W n) y)
      (Real.sqrt (gridStep s t K n))
    simp only [hΦdef, LoopStep_Phi, LoopStep_herm_of_isHermitian hh, hfdef]
  have hfcont : Continuous f := by
    rw [hfeq]
    have h2 : Continuous fun y : Ω d (sz.L n) (sz.W n) =>
        (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) y :=
      (continuous_Xmat d (sz.L n) (sz.W n)).const_smul (Real.sqrt (gridStep s t K n) : ℂ)
    exact hΦcont.comp (continuous_const.add h2)
  have hFf : ∀ x, F (pathH sz s t K n k ω) x = f (Sizes.slice sz n x) := by
    intro x
    have hh := LoopStep_isHermitian_add_smul hp (Sizes.seqXmat_isHermitian sz n x)
      (Real.sqrt (gridStep s t K n))
    simp only [hFdef, hΦdef, LoopStep_Phi, LoopStep_herm_of_isHermitian hh, hfdef]
    rfl
  calc ∫ x, F (pathH sz s t K n k ω) x ∂(Sizes.seqP sz)
      = ∫ x, f (Sizes.slice sz n x) ∂(Sizes.seqP sz) := by simp only [hFf]
    _ = ∫ y, f y ∂((Sizes.seqP sz).map (Sizes.slice sz n)) :=
        (integral_map (Sizes.measurable_slice sz n).aemeasurable
          hfcont.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by rw [Sizes.seqP_map_slice]

/-! ### The one-step conditional drift -/

/-- **`condExp_loop_drift`**: the conditional drift of the loop observable along the grid walk,
bounded by the merged one-step envelope (`oneStepEnvelope`, T2072) applied pointwise at
`M = pathH k ω` (RBM1D `condExp_loop_drift`, `Gauss/GridLoopStep.lean:892`, whose right side
`loopDrift`, `zMotionLip`, `genPtLip` is replaced by `envConst`; RBM2D `Path/LoopStep.lean:307`).
The hypotheses `_hK`, `_hk` are not used by the proof (at `K n = 0` the step is `0` in Lean and the
bound reads `0 ≤ 0`).  The generator is `genMat` at the coupling `sz.lam n`. -/
theorem condExp_loop_drift (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (hE : |E| < 2)
    {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (_hK : K n ≠ 0) (_hk : k < K n) (hu1 : gridTime s t K n (k + 1) < 1) :
    ∀ᵐ ω ∂(pathP sz),
      ‖(pathP sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (k + 1) ω'))
              (zt E (gridTime s t K n (k + 1))) I | filt sz k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n k ω))
              (zt E (gridTime s t K n k)) I
          - (gridStep s t K n : ℂ) *
              genMat d (sz.L n) (sz.W n) (sz.lam n) E (gridTime s t K n k)
                (pathH sz s t K n k ω) I‖
        ≤ envConst d (sz.L n) (sz.W n) E I.length (gridTime s t K n (k + 1))
            * gridStep s t K n ^ ((3 : ℝ) / 2) := by
  filter_upwards [condExp_loop_step sz s t K n k E hE hwf hu1] with ω hω
  rw [hω]
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)
  have hu : gridTime s t K n (k + 1) = gridTime s t K n k + gridStep s t K n := by
    unfold gridTime
    push_cast
    ring
  have hu0 : 0 ≤ gridTime s t K n k := by
    unfold gridTime
    positivity
  have key := oneStepEnvelope d (sz.L n) (sz.W n) (sz.lam n) E hE I hwf (gridTime s t K n k)
    (gridStep s t K n) hu0 hΔ (hu ▸ hu1) (pathH sz s t K n k ω)
    (pathH_isHermitian sz s t K n k ω)
  rw [← hu] at key
  exact key

/-! ### Compiled nonempty instances at the admissible sequence `sz0`

`RBM.Gauss.SizesInst.sz0` (`RBM3D/Defs/Sizes.lean`): `d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`.
Grid data `s = 1/10`, `t = 1/2`, `K = 4` (`Δ = 1/10`, `u_0 = 1/10`, `u_1 = 1/5`), size index `n = 0`,
step `k = 0`, energy `E = 0`, the two-loop `(+,-; 0, 1)` with `a₁ ≠ a₂`.  Every deterministic
hypothesis is discharged: `|E| < 2`, `I.WF`, `0 ≤ s`, `s ≤ t`, `K ≠ 0`, `k < K`, `u_1 < 1`. -/

section Instances

open RBM.Gauss.SizesInst

/-- The two-loop `(+,-; a₁, a₂)`. -/
private def LoopStep_instLoop (L : ℕ) (a₁ a₂ : Zd 3 L) : Loop.LoopIdx (Zd 3 L) :=
  ⟨[true, false], [a₁, a₂]⟩

private theorem LoopStep_instLoop_wf (L : ℕ) (a₁ a₂ : Zd 3 L) : (LoopStep_instLoop L a₁ a₂).WF :=
  rfl

/-- The two labels of the instance loop differ (`0 ≠ 1` in `Z_4^3`). -/
theorem LoopStep_check_labels_sz0 : (0 : Zd 3 (sz0.L 0)) ≠ 1 := fun h => by
  have h0 := congrFun h 0
  revert h0
  decide

private theorem LoopStep_inst_gridTime :
    gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1) = 1 / 5 := by
  norm_num [gridTime, gridStep]

private theorem LoopStep_inst_gridTime_lt :
    gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1) < 1 := by
  rw [LoopStep_inst_gridTime]; norm_num

/-- **`condExp_loop_step` at `sz0`**: the conditional mean of the loop observable at the next grid
time, given `filt sz0 0`, is the Gaussian integral over `PF 3 4 32 (1/64)` of the same observable
at `H_0 + √Δ X`; the loop `(+,-; 0, 1)` has `0 ≠ 1`. -/
theorem LoopStep_check_step_sz0 :
    (pathP sz0)[fun ω : PathΩ sz0 =>
        loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
          (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1) ω))
          (zt 0 (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1)))
          (LoopStep_instLoop (sz0.L 0) 0 1) | filt sz0 0]
      =ᵐ[pathP sz0] fun ω =>
        ∫ x, loopL 3 (sz0.L 0) (sz0.W 0)
          (blockMat 3 (sz0.L 0) (sz0.W 0)
            (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 ω
              + (Real.sqrt (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0) : ℂ)
                • Xmat 3 (sz0.L 0) (sz0.W 0) x))
          (zt 0 (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1)))
          (LoopStep_instLoop (sz0.L 0) 0 1) ∂(PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0)) :=
  condExp_loop_step sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 0
    (by norm_num) (LoopStep_instLoop_wf _ 0 1) LoopStep_inst_gridTime_lt

/-- **`condExp_loop_drift` at `sz0`**: the envelope bound at the same data. -/
theorem LoopStep_check_drift_sz0 :
    ∀ᵐ ω ∂(pathP sz0),
      ‖(pathP sz0)[fun ω' : PathΩ sz0 =>
            loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
              (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1) ω'))
              (zt 0 (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1)))
              (LoopStep_instLoop (sz0.L 0) 0 1) | filt sz0 0] ω
          - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0)
              (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 ω))
              (zt 0 (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0))
              (LoopStep_instLoop (sz0.L 0) 0 1)
          - (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 : ℂ) *
              genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0
                (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0)
                (pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 ω)
                (LoopStep_instLoop (sz0.L 0) 0 1)‖
        ≤ envConst 3 (sz0.L 0) (sz0.W 0) 0 (LoopStep_instLoop (sz0.L 0) 0 1).length
            (gridTime (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 (0 + 1))
          * gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 ^ ((3 : ℝ) / 2) :=
  condExp_loop_drift sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 0
    (by norm_num) (LoopStep_instLoop_wf _ 0 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) LoopStep_inst_gridTime_lt

/-- `pathH_succ` at `sz0`, `k = 0`. -/
example (ω : PathΩ sz0) :
    pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 1 ω
      = pathH sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 ω
        + (Real.sqrt (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0) : ℂ)
          • Sizes.seqXmat sz0 0 (ω 1) :=
  pathH_succ sz0 _ _ _ 0 0 ω

end Instances

end RBM.Path

end
