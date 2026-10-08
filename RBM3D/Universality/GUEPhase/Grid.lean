/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.ZeroModeProfile

/-!
# The GUE-phase grid carrier, path and one-time laws (7.25)/(7.26), `d ≥ 3`

Ticket T2316 (UN-27).  Port of `RBM2D/Universality/GUEPhase/Grid.lean` at `c9a24cf` (`:1-781`,
except the dead `GUEFlow`/`loopG` `:111-123`; the instances `:783-862` are rewritten at `d = 3`).
Paper: arXiv:2507.20274, the GUE phase of Thm 2.4 (`paper/tex/1_2_Intro_model_result.tex:566-570`,
"essentially identical to [YY_25, Theorem 2.6]"); the matrix Brownian motion `(MBM)`
(`1_2:686-691`) is realised in the GUE phase as a grid walk.  The equation numbers (7.25), (7.26),
(7.28) are those of [YY_25] §7.2.

The GUE-phase flow `H̃_u = √t₁ X + √(u - t₁) Y` is realised as a discrete grid walk: the band
field `Sizes.seqP sz` at grid step `0` and independent unit GUE fields `gueUnit sz` at every later
step, on the path carrier `PathΩ sz`.  Only the one-time laws at step `0` and at the last step
`K n` are proved (against `Sizes.seqHflow` and against `√t₀ · ouMat (UNModel.band sz) n τ`,
(7.25)/(7.26)).

What changes from `d = 2` (rule R1): `d : Sizes` becomes `sz : Sizes d`; `Z2 L` becomes `Zd d L`;
`BlockIndex L W` becomes `Vtx d L W`; `Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`;
`size = (W L)^d` (a `def`); `Xmat`/`Ω`/`Coord` carry `d`; `gvar` is `gvarF d L W (sz.lam n)`
(through `seqGvar`); the OU carrier is `ouP (UNModel.band sz) n` on `SeqΩ sz × Ω d L W`; the
list-based `gloop` is `loopL` (`foldr`), `Gsig` is `Gres`.  The only `d`-dependent fact is the
variance identity of `map_gueH_last`, an identity in the band variance `S_c` (any `sz.lam`) and in
`N` (any `d`).  The Lemma 2.8 homogeneity of `loopL` uses private copies of the scaling lemmas of
`Induction/ConArg.lean:380-442`.  Not ported: `GUEFlow`, `loopG` (dead in RBM2D).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ### The GUE-phase grid measure -/

/-- Unit GUE coordinate variance: `1` on the diagonal, `1/2` per real component off it. -/
def gueUnitVar (c : Sizes.SeqCoord sz) : ℝ≥0 := if c.2.1 = c.2.2.1 then 1 else 1 / 2

/-- One unit GUE coordinate field, all sizes at once. -/
def gueUnit : Measure (Sizes.SeqΩ sz) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueUnitVar sz c)

/-- Step laws: the band field at step `0`, unit GUE fields at steps `k ≥ 1`. -/
def gueStepMeasure : ℕ → Measure (Sizes.SeqΩ sz)
  | 0 => Sizes.seqP sz
  | _ + 1 => gueUnit sz

/-- The GUE-phase grid measure on the path carrier `PathΩ sz`. -/
def Pgue : Measure (PathΩ sz) := Measure.infinitePi (gueStepMeasure sz)

instance gueUnit_isProbabilityMeasure : IsProbabilityMeasure (gueUnit sz) := by
  unfold gueUnit; infer_instance

instance gueStepMeasure_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (gueStepMeasure sz k) := by
  cases k <;> simp only [gueStepMeasure] <;> infer_instance

instance Pgue_isProbabilityMeasure : IsProbabilityMeasure (Pgue sz) := by
  unfold Pgue; infer_instance

/-! ### The GUE-phase grid path -/

/-- The GUE-phase grid path `H_k = √t₁ X + √(Δ/N) ∑_{i=1}^k Y_i`, `Δ = (t₀ - t₁)/K`,
`N = sz.size n = (W L)^d`. -/
def gueH (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (Real.sqrt (t1 n) : ℂ) • Sizes.seqXmat sz n (ω 0) +
    (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) •
      ∑ i ∈ Finset.Icc 1 k, Sizes.seqXmat sz n (ω i)

/-- `N η_u` of the GUE phase, `N = (W L)^d`. -/
def gueScale (E : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ := ((sz.size n : ℕ) : ℝ) * etaT (E n) u

/-- **The output of the §7.2 random layer** at the grid times `k ≤ K n`: (7.28) for loops of
length `1 ≤ m ≤ n₀` against a primitive family `Kt`, and `‖G̃ - m‖_max ≺ (N η_u)^{-1/2}`.
The loops are evaluated on `blockMat` with the list-based loop `loopL … (loopOf σ a)`. -/
structure GUEPathBounds (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → Loop.LoopIdx (Zd d (sz.L n)) → ℂ) : Prop where
  lk : ∀ m : ℕ, 1 ≤ m → m ≤ n0 → StochDomAt (Pgue sz) sz.size
    (fun n (p : Fin (K n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))) ω =>
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n p.1 ω))
          (zt (E n) (gridTime t1 t0 K n p.1)) (loopOf p.2.1 p.2.2) -
        Kt n (gridTime t1 t0 K n p.1) (loopOf p.2.1 p.2.2)‖)
    (fun n p _ => (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ m)
  localLaw : StochDomAt (Pgue sz) sz.size
    (fun n (p : Fin (K n + 1) × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω =>
      ‖(green (gueH sz t1 t0 K n p.1 ω) (zt (E n) (gridTime t1 t0 K n p.1)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
        p.2.1 p.2.2‖)
    (fun n p _ => (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ ((1 : ℝ) / 2))

/-- The grid size used by G1: `K n = (sz.size n + 1)^(32 n₀ + 64)` (in the matrix dimension
`sz.size n = (W L)^d`; a proof device, never a hypothesis witness). -/
def gueGridK (n0 n : ℕ) : ℕ := (sz.size n + 1) ^ (32 * n0 + 64)

theorem gueGridK_ne_zero (n0 n : ℕ) : gueGridK sz n0 n ≠ 0 := by
  unfold gueGridK; positivity

/-! ### Pointwise algebraic identities -/

section Algebra

variable {sz}

private lemma GUEPhaseGrid_slice_add (n : ℕ) (ω ν : Sizes.SeqΩ sz) :
    Sizes.slice sz n (ω + ν) = Sizes.slice sz n ω + Sizes.slice sz n ν := rfl

private lemma GUEPhaseGrid_slice_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ sz) :
    Sizes.slice sz n (a • ω) = a • Sizes.slice sz n ω := rfl

private lemma GUEPhaseGrid_slice_sum {ι : Type*} (n : ℕ) (S : Finset ι) (ω : ι → Sizes.SeqΩ sz) :
    Sizes.slice sz n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.slice sz n (ω l) := by
  funext c
  simp [Sizes.slice, Finset.sum_apply]

lemma GUEPhaseGrid_seqXmat_add (n : ℕ) (ω ν : Sizes.SeqΩ sz) :
    Sizes.seqXmat sz n (ω + ν) = Sizes.seqXmat sz n ω + Sizes.seqXmat sz n ν := by
  unfold Sizes.seqXmat
  rw [GUEPhaseGrid_slice_add, Xmat_add]

lemma GUEPhaseGrid_seqXmat_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ sz) :
    Sizes.seqXmat sz n (a • ω) = a • Sizes.seqXmat sz n ω := by
  unfold Sizes.seqXmat
  rw [GUEPhaseGrid_slice_smul, Xmat_smul]

lemma GUEPhaseGrid_seqXmat_sum {ι : Type*} (n : ℕ) (S : Finset ι)
    (ω : ι → Sizes.SeqΩ sz) :
    Sizes.seqXmat sz n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.seqXmat sz n (ω l) := by
  unfold Sizes.seqXmat
  rw [GUEPhaseGrid_slice_sum]
  exact map_sum (Xlinear d (sz.L n) (sz.W n)) (fun l => Sizes.slice sz n (ω l)) S

lemma GUEPhaseGrid_real_smul_matrix {m : Type*} (r : ℝ) (M : Matrix m m ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Complex.real_smul]

private lemma GUEPhaseGrid_measurable_seqXentry (n : ℕ) (i j : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω : Sizes.SeqΩ sz => Sizes.seqXmat sz n ω i j :=
  (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (Sizes.measurable_slice sz n)

private lemma GUEPhaseGrid_gueH_apply (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (i j : Idx d (sz.L n) (sz.W n)) (ω : PathΩ sz) :
    gueH sz t1 t0 K n k ω i j
      = (Real.sqrt (t1 n) : ℂ) * Sizes.seqXmat sz n (ω 0) i j
        + (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ)
          * ∑ l ∈ Finset.Icc 1 k, Sizes.seqXmat sz n (ω l) i j := by
  simp [gueH, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Finset.mul_sum]

end Algebra

theorem gueH_isHermitian (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    (gueH sz t1 t0 K n k ω).IsHermitian := by
  have h0 : (Sizes.seqXmat sz n (ω 0))ᴴ = Sizes.seqXmat sz n (ω 0) :=
    Sizes.seqXmat_isHermitian sz n (ω 0)
  have hsum : (∑ i ∈ Finset.Icc 1 k, Sizes.seqXmat sz n (ω i))ᴴ
      = ∑ i ∈ Finset.Icc 1 k, Sizes.seqXmat sz n (ω i) := by
    rw [conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => Sizes.seqXmat_isHermitian sz n (ω i)
  change (gueH sz t1 t0 K n k ω)ᴴ = gueH sz t1 t0 K n k ω
  unfold gueH
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
    show star (Real.sqrt (t1 n) : ℂ) = (Real.sqrt (t1 n) : ℂ) from Complex.conj_ofReal _,
    show star (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ)
        = (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ)
      from Complex.conj_ofReal _,
    h0, hsum]

theorem gueH_adapted (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (i j : Idx d (sz.L n) (sz.W n)) :
    StronglyMeasurable[filt sz k] (fun ω : PathΩ sz => gueH sz t1 t0 K n k ω i j) := by
  rw [stronglyMeasurable_iff_measurable]
  have heq : (fun ω : PathΩ sz => gueH sz t1 t0 K n k ω i j) =
      fun ω => (Real.sqrt (t1 n) : ℂ) * Sizes.seqXmat sz n (ω 0) i j
        + (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ)
          * ∑ l ∈ Finset.Icc 1 k, Sizes.seqXmat sz n (ω l) i j :=
    funext fun ω => GUEPhaseGrid_gueH_apply t1 t0 K n k i j ω
  rw [heq]
  have hmeas : ∀ l : ℕ, l ≤ k → Measurable[filt sz k] (fun ω : PathΩ sz => ω l) := by
    intro l hl
    have : (fun ω : PathΩ sz => ω l)
        = (fun g : Set.Iic k → Sizes.SeqΩ sz => g ⟨l, hl⟩)
          ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k) := rfl
    rw [this]
    exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
      (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k))
  apply Measurable.add
  · exact ((GUEPhaseGrid_measurable_seqXentry n i j).comp (hmeas 0 (by omega))).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l hl =>
      (GUEPhaseGrid_measurable_seqXentry n i j).comp
        (hmeas l (by simp only [Finset.mem_Icc] at hl; omega))

theorem gueH_measurable (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (gueH sz t1 t0 K n k) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have heq : (fun ω : PathΩ sz => gueH sz t1 t0 K n k ω i j) =
      fun ω => (Real.sqrt (t1 n) : ℂ) * Sizes.seqXmat sz n (ω 0) i j
        + (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ)
          * ∑ l ∈ Finset.Icc 1 k, Sizes.seqXmat sz n (ω l) i j :=
    funext fun ω => GUEPhaseGrid_gueH_apply t1 t0 K n k i j ω
  rw [heq]
  apply Measurable.add
  · exact ((GUEPhaseGrid_measurable_seqXentry n i j).comp (measurable_pi_apply 0)).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l _ =>
      (GUEPhaseGrid_measurable_seqXentry n i j).comp (measurable_pi_apply l)

/-! ### A mixed-step grid carrier

`mixedStepMeasure v0 v1` has the same shape as `gueStepMeasure`: the coordinate variance family
`v0` at step `0`, `v1` at steps `≥ 1`.  With `(v0, v1) = (seqGvar sz, gueUnitVar sz)` it is
`gueStepMeasure`.  The "swap" computation of `Path/Walk.lean` (private `pathP'`, `swapEquiv`,
`pathP_swap_eq`, `map_combined_eq`), generalised from a constant step law to this mixed law. -/

section MixedGrid

variable {sz}

private def GUEPhaseGrid_mixedStepMeasure (v0 v1 : Sizes.SeqCoord sz → ℝ≥0) :
    ℕ → Measure (Sizes.SeqΩ sz)
  | 0 => Measure.infinitePi fun c => gaussianReal 0 (v0 c)
  | _ + 1 => Measure.infinitePi fun c => gaussianReal 0 (v1 c)

private def GUEPhaseGrid_mixedRawStep (v0 v1 : Sizes.SeqCoord sz → ℝ≥0) (c : Sizes.SeqCoord sz)
    (i : ℕ) : Measure ℝ :=
  if i = 0 then gaussianReal 0 (v0 c) else gaussianReal 0 (v1 c)

private instance GUEPhaseGrid_mixedRawStep_isProbabilityMeasure (v0 v1 : Sizes.SeqCoord sz → ℝ≥0)
    (c : Sizes.SeqCoord sz) (i : ℕ) :
    IsProbabilityMeasure (GUEPhaseGrid_mixedRawStep v0 v1 c i) := by
  unfold GUEPhaseGrid_mixedRawStep; split_ifs <;> infer_instance

private lemma GUEPhaseGrid_mixedStepMeasure_eq (v0 v1 : Sizes.SeqCoord sz → ℝ≥0) (i : ℕ) :
    GUEPhaseGrid_mixedStepMeasure v0 v1 i
      = Measure.infinitePi (fun c => GUEPhaseGrid_mixedRawStep v0 v1 c i) := by
  cases i <;> simp [GUEPhaseGrid_mixedStepMeasure, GUEPhaseGrid_mixedRawStep]

private instance GUEPhaseGrid_mixedStepMeasure_isProbabilityMeasure
    (v0 v1 : Sizes.SeqCoord sz → ℝ≥0) (k : ℕ) :
    IsProbabilityMeasure (GUEPhaseGrid_mixedStepMeasure v0 v1 k) := by
  rw [GUEPhaseGrid_mixedStepMeasure_eq]; infer_instance

/-- Same nesting as `Path/Walk.lean`'s private `pathP'`: coordinates first, then the grid index. -/
private def GUEPhaseGrid_mixedRaw (v0 v1 : Sizes.SeqCoord sz → ℝ≥0) :
    Measure (Sizes.SeqCoord sz → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Sizes.SeqCoord sz =>
    Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i))

private def GUEPhaseGrid_swapEquiv : (Sizes.SeqCoord sz → ℕ → ℝ) → PathΩ sz :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord sz) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord sz => ℝ)
      (Equiv.prodComm (Sizes.SeqCoord sz) ℕ)) ∘
    (MeasurableEquiv.curry (Sizes.SeqCoord sz) ℕ ℝ).symm

private lemma GUEPhaseGrid_measurable_swapEquiv :
    Measurable (GUEPhaseGrid_swapEquiv (sz := sz)) :=
  (MeasurableEquiv.curry ℕ (Sizes.SeqCoord sz) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord sz => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord sz) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Sizes.SeqCoord sz) ℕ ℝ).symm.measurable)

private lemma GUEPhaseGrid_swapEquiv_apply (X : Sizes.SeqCoord sz → ℕ → ℝ) (i : ℕ)
    (c : Sizes.SeqCoord sz) : GUEPhaseGrid_swapEquiv X i c = X c i := by
  change (MeasurableEquiv.curry ℕ (Sizes.SeqCoord sz) ℝ)
      ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord sz => ℝ)
          (Equiv.prodComm (Sizes.SeqCoord sz) ℕ))
        ((MeasurableEquiv.curry (Sizes.SeqCoord sz) ℕ ℝ).symm X)) i c = X c i
  rw [MeasurableEquiv.coe_curry]
  change (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord sz => ℝ)
      (Equiv.prodComm (Sizes.SeqCoord sz) ℕ))
      ((MeasurableEquiv.curry (Sizes.SeqCoord sz) ℕ ℝ).symm X) (i, c) = X c i
  have key := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.prodComm (Sizes.SeqCoord sz) ℕ)
    (β := fun _ : ℕ × Sizes.SeqCoord sz => ℝ)
    ((MeasurableEquiv.curry (Sizes.SeqCoord sz) ℕ ℝ).symm X) (c, i)
  rw [show Equiv.prodComm (Sizes.SeqCoord sz) ℕ (c, i) = (i, c) from rfl] at key
  rw [key, MeasurableEquiv.coe_curry_symm]
  rfl

private lemma GUEPhaseGrid_mixedRaw_swap_eq (v0 v1 : Sizes.SeqCoord sz → ℝ≥0) :
    (GUEPhaseGrid_mixedRaw v0 v1).map GUEPhaseGrid_swapEquiv
      = Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1) := by
  have ha : (GUEPhaseGrid_mixedRaw v0 v1).map
        ((MeasurableEquiv.curry (Sizes.SeqCoord sz) ℕ ℝ).symm)
      = Measure.infinitePi
          (fun p : Sizes.SeqCoord sz × ℕ => GUEPhaseGrid_mixedRawStep v0 v1 p.1 p.2) :=
    Measure.infinitePi_map_curry_symm
      (μ := fun (c : Sizes.SeqCoord sz) (i : ℕ) => GUEPhaseGrid_mixedRawStep v0 v1 c i)
  have hb : (Measure.infinitePi
        (fun p : Sizes.SeqCoord sz × ℕ => GUEPhaseGrid_mixedRawStep v0 v1 p.1 p.2)).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord sz => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord sz) ℕ))
      = Measure.infinitePi
          (fun p : ℕ × Sizes.SeqCoord sz => GUEPhaseGrid_mixedRawStep v0 v1 p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Sizes.SeqCoord sz => GUEPhaseGrid_mixedRawStep v0 v1 p.2 p.1)
      (Equiv.prodComm (Sizes.SeqCoord sz) ℕ)
  have hc : (Measure.infinitePi
        (fun p : ℕ × Sizes.SeqCoord sz => GUEPhaseGrid_mixedRawStep v0 v1 p.2 p.1)).map
      (MeasurableEquiv.curry ℕ (Sizes.SeqCoord sz) ℝ)
      = Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1) := by
    rw [Measure.infinitePi_map_curry
      (μ := fun (i : ℕ) (c : Sizes.SeqCoord sz) => GUEPhaseGrid_mixedRawStep v0 v1 c i)]
    exact congrArg Measure.infinitePi
      (funext fun i => (GUEPhaseGrid_mixedStepMeasure_eq v0 v1 i).symm)
  change (GUEPhaseGrid_mixedRaw v0 v1).map ((MeasurableEquiv.curry ℕ (Sizes.SeqCoord sz) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Sizes.SeqCoord sz => ℝ)
        (Equiv.prodComm (Sizes.SeqCoord sz) ℕ)) ∘
      (MeasurableEquiv.curry (Sizes.SeqCoord sz) ℕ ℝ).symm)
      = Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    ha, hb, hc]

/-- **The one-dimensional mixed-variance sum lemma**: the law is uniform `w` only from index `1`
on. -/
private lemma GUEPhaseGrid_sumIcc_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w : ℝ≥0} (hYd : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w) (k : ℕ) :
    μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w) := by
  induction k with
  | zero =>
      have hEmpty : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      simp only [hEmpty, Finset.sum_empty]
      rw [Measure.map_const, measure_univ, one_smul, zero_smul, gaussianReal_zero_var]
  | succ k ih =>
      have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
      have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hfun : (fun ω => ∑ i ∈ Finset.Icc 1 (k + 1), Y i ω)
          = (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) + Y (k + 1) := by
        funext ω
        rw [hins, Finset.sum_insert hnotmem, add_comm]
        rfl
      rw [hfun]
      have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
        Finset.measurable_sum _ fun i _ => hYm i
      have hlaw1 : HasLaw (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (gaussianReal 0 (k • w)) μ' :=
        ⟨hsummeas.aemeasurable, ih⟩
      have hlaw2 : HasLaw (Y (k + 1)) (gaussianReal 0 w) μ' :=
        ⟨(hYm (k + 1)).aemeasurable, hYd (k + 1) (by omega)⟩
      have hindep : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y (k + 1)) μ' := by
        have h := hY.indepFun_finsetSum_of_notMem hYm hnotmem
        have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
          funext ω; simp [Finset.sum_apply]
        rwa [heq] at h
      have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw1 hlaw2
      rw [hres, add_zero, ← succ_nsmul]

/-- **The two-scale mixed weighted sum lemma**: `Y 0` has variance `w0`, `Y 1, Y 2, …` the common
variance `w1`. -/
private lemma GUEPhaseGrid_weightedSum_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w0 w1 : ℝ≥0} (hY0 : μ'.map (Y 0) = gaussianReal 0 w0)
    (hY1 : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w1) (a b : ℝ) (k : ℕ) :
    μ'.map (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * w1)) := by
  classical
  have hindep : IndepFun (fun ω => a * Y 0 ω) (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω) μ' := by
    have h0 : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y 0) μ' := by
      have h := hY.indepFun_finsetSum_of_notMem hYm (s := Finset.Icc 1 k) (i := 0) (by simp)
      have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
        funext ω; simp [Finset.sum_apply]
      rwa [heq] at h
    exact h0.symm.comp (φ := (a * ·)) (ψ := (b * ·)) (by fun_prop) (by fun_prop)
  have hlaw0 : HasLaw (fun ω => a * Y 0 ω)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0)) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω => a * Y 0 ω) = (a * ·) ∘ Y 0 := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hYm 0), hY0, gaussianReal_map_const_mul, mul_zero]
  have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
    Finset.measurable_sum _ fun i _ => hYm i
  have hlawsum : μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w1) :=
    GUEPhaseGrid_sumIcc_map_gaussianReal_mixed hYm hY hY1 k
  have hlaw1 : HasLaw (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b) * (k • w1))) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have heq : (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
        = (b * ·) ∘ (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) := rfl
    rw [heq, ← Measure.map_map (by fun_prop) hsummeas, hlawsum, gaussianReal_map_const_mul,
      mul_zero]
  have hgoal_eq : (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = (fun ω => a * Y 0 ω) + fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω := rfl
  rw [hgoal_eq]
  have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw0 hlaw1
  rw [hres, add_zero]
  congr 1
  rw [nsmul_eq_mul, nsmul_eq_mul]
  apply NNReal.coe_injective
  push_cast
  ring

private lemma GUEPhaseGrid_map_column_eq_mixed (v0 v1 : Sizes.SeqCoord sz → ℝ≥0)
    (c : Sizes.SeqCoord sz) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hY0 : (Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y 0) = gaussianReal 0 (v0 c) := by
    rw [Measure.infinitePi_map_eval]
    simp [GUEPhaseGrid_mixedRawStep]
  have hY1 : ∀ i : ℕ, 1 ≤ i → (Measure.infinitePi
      (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i)).map (fun y : ℕ → ℝ => y i)
        = gaussianReal 0 (v1 c) := by
    intro i hi
    rw [Measure.infinitePi_map_eval]
    have hi0 : i ≠ 0 := by omega
    simp [GUEPhaseGrid_mixedRawStep, hi0]
  exact GUEPhaseGrid_weightedSum_map_gaussianReal_mixed hYm hY hY0 hY1 a b k

/-- **The mixed-grid combined law.** -/
lemma GUEPhaseGrid_map_combined_eq_mixed (v0 v1 : Sizes.SeqCoord sz → ℝ≥0) (a b : ℝ)
    (k : ℕ) :
    (Measure.infinitePi (GUEPhaseGrid_mixedStepMeasure v0 v1)).map
        (fun ω : PathΩ sz => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i)
      = Measure.infinitePi (fun c : Sizes.SeqCoord sz => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
            + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c))) := by
  have hmeasComb : Measurable (fun ω : PathΩ sz => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : PathΩ sz => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : PathΩ sz => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hcomp : (fun ω : PathΩ sz => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i)
        ∘ GUEPhaseGrid_swapEquiv
      = (fun X : Sizes.SeqCoord sz → ℕ → ℝ =>
          fun c => a * X c 0 + b * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      GUEPhaseGrid_swapEquiv_apply]
  rw [← GUEPhaseGrid_mixedRaw_swap_eq v0 v1,
    Measure.map_map hmeasComb GUEPhaseGrid_measurable_swapEquiv, hcomp]
  have hfmeas : ∀ c : Sizes.SeqCoord sz,
      Measurable (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) := fun c => by
    have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
    have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Sizes.SeqCoord sz =>
        Measure.infinitePi (fun i : ℕ => GUEPhaseGrid_mixedRawStep v0 v1 c i))
      (f := fun c : Sizes.SeqCoord sz => fun y : ℕ → ℝ =>
        a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [GUEPhaseGrid_mixedRaw]
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => GUEPhaseGrid_map_column_eq_mixed v0 v1 c a b k))

end MixedGrid

/-! ### Identification of `Pgue sz` as the mixed-grid carrier, and the size slice -/

section Identification

variable {sz}

lemma GUEPhaseGrid_Pgue_eq_mixed :
    Pgue sz = Measure.infinitePi
      (GUEPhaseGrid_mixedStepMeasure (Sizes.seqGvar sz) (gueUnitVar sz)) := by
  unfold Pgue
  refine congrArg Measure.infinitePi (funext fun k => ?_)
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The size-`n` slice of an independent Gaussian family on `SeqCoord sz` (generalising
`Sizes.seqP_map_slice` from `seqGvar sz` to any variance family). -/
lemma GUEPhaseGrid_map_slice_infinitePi (w : Sizes.SeqCoord sz → ℝ≥0) (n : ℕ) :
    (Measure.infinitePi fun c => gaussianReal 0 (w c)).map (Sizes.slice sz n)
      = Measure.infinitePi fun c : CoordF d (sz.L n) (sz.W n) => gaussianReal 0 (w ⟨n, c⟩) := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  let e : CoordF d (sz.L n) (sz.W n) → Sizes.SeqCoord sz := fun c => ⟨n, c⟩
  have he : Function.Injective e := by
    intro c c' h
    simpa [e] using h
  let t' : Sizes.SeqCoord sz → Set ℝ := fun c =>
    if h : c.1 = n then t (h ▸ c.2) else Set.univ
  have hpre : Sizes.slice sz n ⁻¹' Set.pi (↑s) t = Set.pi (↑(s.image e)) t' := by
    ext ω
    constructor
    · intro h c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      simpa [t', e, Sizes.slice] using h a ha
    · intro h a ha
      have hc : e a ∈ s.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [t', e, Sizes.slice] using h (e a) hc
  have ht' : ∀ c ∈ s.image e, MeasurableSet (t' c) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    simpa [t', e] using ht a
  rw [Measure.map_apply (Sizes.measurable_slice sz n)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)),
    hpre, Measure.infinitePi_pi _ ht']
  rw [Finset.prod_image he.injOn]
  apply Finset.prod_congr rfl
  intro a ha
  simp [t', e]

lemma GUEPhaseGrid_measurable_Xmat (L W : ℕ) [NeZero L] [NeZero W] :
    Measurable (Xmat d L W) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d L W i j

/-- Scaling every coordinate of an independent centred Gaussian family by `s` multiplies the
variances by `s²` (as `Path/Walk.lean`'s private `map_smul_eq`). -/
private lemma GUEPhaseGrid_map_smul_infinitePi {ι : Type*} (s : ℝ) (v : ι → ℝ≥0) :
    (Measure.infinitePi fun c => gaussianReal 0 (v c)).map (fun x : ι → ℝ => s • x)
      = Measure.infinitePi (fun c => gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s) * v c)) := by
  have hfmeas : ∀ c : ι, Measurable (s * ·) := fun c => by fun_prop
  have h1 : (Measure.infinitePi fun c => gaussianReal 0 (v c)).map
        (fun x : ι → ℝ => fun c => s * x c)
      = Measure.infinitePi (fun c => (gaussianReal 0 (v c)).map (s * ·)) :=
    Measure.infinitePi_map_pi (μ := fun c => gaussianReal 0 (v c)) (f := fun _ => (s * ·)) hfmeas
  have heq : (fun x : ι → ℝ => s • x) = (fun x : ι → ℝ => fun c => s * x c) := by
    funext x c; simp [smul_eq_mul]
  rw [heq, h1]
  congr 1
  funext c
  rw [gaussianReal_map_const_mul, mul_zero]

end Identification

/-! ### The one-time laws (7.25)/(7.26) -/

/-- Step `0` has the law of the band flow at `t₁`. -/
theorem map_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (_ht1 : 0 ≤ t1 n) :
    (Pgue sz).map (gueH sz t1 t0 K n 0) = (Sizes.seqP sz).map (Sizes.seqHflow sz n (t1 n)) := by
  have heq : gueH sz t1 t0 K n 0 = (Sizes.seqHflow sz n (t1 n)) ∘ (fun ω : PathΩ sz => ω 0) := by
    funext ω
    change gueH sz t1 t0 K n 0 ω = Sizes.seqHflow sz n (t1 n) (ω 0)
    unfold gueH
    simp [Sizes.seqHflow_eq_smul]
  have hmeasHflow : Measurable (Sizes.seqHflow sz n (t1 n)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      Sizes.measurable_seqHflow_entry sz n (t1 n) i j
  rw [heq, ← Measure.map_map hmeasHflow (measurable_pi_apply (0 : ℕ))]
  congr 1
  unfold Pgue
  rw [Measure.infinitePi_map_eval]
  rfl

/-- Step `K` with `t₁ = (1 - ζ(τ)) t₀` has the law of `√t₀ · H_τ` ((7.25), (7.26)). -/
theorem map_gueH_last (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ht0 : 0 ≤ t0 n) (hτ : 0 ≤ τ n)
    (hK : K n ≠ 0) :
    (Pgue sz).map (gueH sz (fun n => (1 - ouZeta (τ n)) * t0 n) t0 K n (K n)) =
      (ouP (UNModel.band sz) n).map
        (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (τ n) ω) := by
  set t1fn : ℕ → ℝ := fun n => (1 - ouZeta (τ n)) * t0 n with ht1fndef
  have hζ0 : 0 ≤ ouZeta (τ n) := by
    unfold ouZeta
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hτ)
    linarith
  have hζ1 : ouZeta (τ n) ≤ 1 := by
    unfold ouZeta
    have := (Real.exp_pos (-(τ n))).le
    linarith
  have ht1n : t1fn n = (1 - ouZeta (τ n)) * t0 n := rfl
  have ht1n0 : 0 ≤ t1fn n := by rw [ht1n]; exact mul_nonneg (by linarith) ht0
  have ht1nt0 : t1fn n ≤ t0 n := by rw [ht1n]; nlinarith
  have hΔ : 0 ≤ gridStep t1fn t0 K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  set M : ℝ := ((sz.size n : ℕ) : ℝ) with hMdef
  have hMpos : (0 : ℝ) < M := by
    rw [hMdef]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (sz.one_le_size n)
  set a : ℝ := Real.sqrt (t1fn n) with hadef
  set b : ℝ := Real.sqrt (gridStep t1fn t0 K n / M) with hbdef
  -- Step 1: the left side is `seqXmat sz n` of a real-linear combination of the raw draws.
  have hHeq : gueH sz t1fn t0 K n (K n)
      = fun ω => Sizes.seqXmat sz n (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i) := by
    funext ω
    rw [GUEPhaseGrid_seqXmat_add, GUEPhaseGrid_seqXmat_smul, GUEPhaseGrid_seqXmat_smul,
      GUEPhaseGrid_seqXmat_sum, GUEPhaseGrid_real_smul_matrix, GUEPhaseGrid_real_smul_matrix]
    rfl
  have hLHSmeas : Measurable (fun ω : PathΩ sz =>
      a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i) := by
    have h1 : Measurable (fun ω : PathΩ sz => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : PathΩ sz => ∑ i ∈ Finset.Icc 1 (K n), ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  -- The left side as the `Xmat` image of the size-`n` slice of the combined draw.
  have hLHS : (Pgue sz).map (gueH sz t1fn t0 K n (K n))
      = (Measure.infinitePi fun c : CoordF d (sz.L n) (sz.W n) => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * Sizes.seqGvar sz ⟨n, c⟩
            + (K n) • (NNReal.mk (b ^ 2) (sq_nonneg b) * gueUnitVar sz ⟨n, c⟩))).map
          (Xmat d (sz.L n) (sz.W n)) := by
    rw [hHeq]
    have hfun : (fun ω : PathΩ sz => Sizes.seqXmat sz n
          (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i))
        = Xmat d (sz.L n) (sz.W n) ∘ Sizes.slice sz n ∘
            (fun ω : PathΩ sz => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K n), ω i) := rfl
    rw [hfun, ← Measure.map_map (GUEPhaseGrid_measurable_Xmat _ _)
        ((Sizes.measurable_slice sz n).comp hLHSmeas),
      ← Measure.map_map (Sizes.measurable_slice sz n) hLHSmeas,
      GUEPhaseGrid_Pgue_eq_mixed,
      GUEPhaseGrid_map_combined_eq_mixed (Sizes.seqGvar sz) (gueUnitVar sz) a b (K n)]
    congr 1
    exact GUEPhaseGrid_map_slice_infinitePi _ n
  -- The right side as the `Xmat` image of `√t₀ • ouSample`.
  have hRHSeq : (fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) =>
        ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (τ n) ω)
      = Xmat d (sz.L n) (sz.W n) ∘ (fun x => Real.sqrt (t0 n) • x) ∘
          ouSample sz n (τ n) := by
    funext ω
    simp only [Function.comp_apply]
    rw [ouMat_eq_Xmat_ouSample, Xmat_smul, GUEPhaseGrid_real_smul_matrix]
  have hRHS : (ouP (UNModel.band sz) n).map
        (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (τ n) ω)
      = (Measure.infinitePi fun c : CoordF d (sz.L n) (sz.W n) => gaussianReal 0
          (NNReal.mk (Real.sqrt (t0 n) ^ 2) (sq_nonneg _) *
            ouVar d (sz.L n) (sz.W n) (sz.lam n) (τ n) c)).map
          (Xmat d (sz.L n) (sz.W n)) := by
    have hsm : Measurable (fun x : Ω d (sz.L n) (sz.W n) => Real.sqrt (t0 n) • x) :=
      by fun_prop
    rw [hRHSeq, ← Measure.map_map (GUEPhaseGrid_measurable_Xmat _ _)
        (hsm.comp (measurable_ouSample sz n (τ n))),
      ← Measure.map_map hsm (measurable_ouSample sz n (τ n)),
      ouSample_law sz n hτ, GUEPhaseGrid_map_smul_infinitePi]
  rw [hLHS, hRHS]
  congr 1
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  congr 1
  -- Step 2: the coordinate variances agree.
  apply NNReal.coe_injective
  have ha2 : a ^ 2 = t1fn n := by rw [hadef, Real.sq_sqrt ht1n0]
  have hb2 : b ^ 2 = gridStep t1fn t0 K n / M := by
    rw [hbdef, Real.sq_sqrt (div_nonneg hΔ hMpos.le)]
  have ht02 : Real.sqrt (t0 n) ^ 2 = t0 n := Real.sq_sqrt ht0
  have hstepval : gridStep t1fn t0 K n = (t0 n - t1fn n) / (K n : ℝ) := rfl
  have hKcast : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  have hex : Real.exp (-τ n) = 1 - ouZeta (τ n) := by unfold ouZeta; ring
  have hexle : Real.exp (-τ n) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hsz : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  have hunit : ((gueUnitVar sz ⟨n, c⟩ : ℝ≥0) : ℝ) / M
      = (RBM.Univ.gueVar d (sz.L n) (sz.W n) c : ℝ) := by
    unfold gueUnitVar RBM.Univ.gueVar
    by_cases hc : c.1 = c.2.1
    · simp only [hc, ite_true, hMdef, hsz]
      push_cast
      simp
    · simp only [hc, ite_false, hMdef, hsz]
      push_cast
      field_simp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul,
    ouVar, Real.coe_toNNReal _ (Real.exp_pos _).le, Real.coe_toNNReal _ (sub_nonneg.2 hexle)]
  have hseq : ((Sizes.seqGvar sz ⟨n, c⟩ : ℝ≥0) : ℝ)
      = (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) := rfl
  have hkey : (K n : ℝ) * (gridStep t1fn t0 K n / M * ((gueUnitVar sz ⟨n, c⟩ : ℝ≥0) : ℝ))
      = (t0 n - t1fn n) * ((gueUnitVar sz ⟨n, c⟩ : ℝ≥0) / M : ℝ) := by
    rw [hstepval]
    field_simp
  push_cast
  rw [ha2, hb2, hseq, ht02, mul_assoc, hkey, hunit, ht1n, ← hex]
  ring

/-! ### Homogeneity of `loopL` under `z ↦ (E, u) = (lemE z, lemT z)`

Used by the law (7.26) of row G1-10b.  The form is on `H : Matrix (Vtx d L W) (Vtx d L W) ℂ`
(callers pass `blockMat d L W M`); the scaling lemmas of `Induction/ConArg.lean:386-440` are
private, so the steps are reproduced here. -/

section Homogeneity

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a nonzero scalar (copy of `Induction/ConArg.lean:386`). -/
private theorem GUEPhaseGrid_inv_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℂ} (hc : c ≠ 0)
    (A : Matrix ι ι ℂ) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv c]
  · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- `G(cH, cz) = c⁻¹ G(H, z)` (copy of `Induction/ConArg.lean:400`). -/
private theorem GUEPhaseGrid_green_smul_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℂ}
    (hc : c ≠ 0) (H : Matrix ι ι ℂ) (z : ℂ) :
    green (c • H) (c * z) = c⁻¹ • green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix ι ι ℂ) = c • (H - z • (1 : Matrix ι ι ℂ)) := by
    rw [smul_sub, smul_smul]
  unfold green
  rw [hsub, GUEPhaseGrid_inv_smul hc]

/-- `Gres H z σ = green H (z or z̄)` (unfolding `Gres`/`green` through
`Matrix.nonsing_inv_eq_ringInverse`; the content of `Induction/ConArgDet.lean:367`). -/
private theorem GUEPhaseGrid_Gres_eq_green {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (z : ℂ) (σ : Bool) :
    Gres H z σ = green H (if σ then z else (starRingEnd ℂ) z) := by
  simp only [green, Gres, Matrix.nonsing_inv_eq_ringInverse]

/-- The same for `Gres` with a real scalar (copy of `Induction/ConArg.lean:409`). -/
private theorem GUEPhaseGrid_Gres_smul_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ}
    (hr : (r : ℂ) ≠ 0) (H : Matrix ι ι ℂ) (z : ℂ) (σ : Bool) :
    Gres ((r : ℂ) • H) ((r : ℂ) * z) σ = ((r : ℂ))⁻¹ • Gres H z σ := by
  rw [GUEPhaseGrid_Gres_eq_green, GUEPhaseGrid_Gres_eq_green]
  cases σ with
  | true => simpa only [ite_true] using GUEPhaseGrid_green_smul_mul hr H z
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [map_mul, Complex.conj_ofReal]
    exact GUEPhaseGrid_green_smul_mul hr H _

/-- The word of a list of `(σ, a)` pairs scales by `c⁻¹` per factor (copy of
`Induction/ConArg.lean:422`). -/
private theorem GUEPhaseGrid_foldr_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (l : List (Bool × Zd d L)) :
    l.foldr (fun p M => Gres ((r : ℂ) • H) ((r : ℂ) * z) p.1 * Eblk d L W p.2 * M) 1
      = (((r : ℂ))⁻¹ ^ l.length) • l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [ih, GUEPhaseGrid_Gres_smul_mul hr, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      smul_smul, pow_succ']

/-- `L(cH, cz) = c⁻ⁿ L(H, z)` (copy of `Induction/ConArg.lean:435`). -/
private theorem GUEPhaseGrid_loopL_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = ((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length * loopL d L W H z I := by
  unfold loopL
  rw [GUEPhaseGrid_foldr_smul_mul hr, Matrix.trace_smul, smul_eq_mul]

/-- `z_u^{(E)} = √u z` for `(E, u) = (lemE z, lemT z)` (`eq:zztE`). -/
private lemma GUEPhaseGrid_zt_eq {z : ℂ} (hz : 0 < z.im) :
    zt (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z := by
  have hu := lemT_pos hz
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have h := eq_inv_sqrt_mul_zt hz
  calc zt (lemE z) (lemT z)
      = (Real.sqrt (lemT z) : ℂ) *
          ((Real.sqrt (lemT z) : ℂ)⁻¹ * zt (lemE z) (lemT z)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = (Real.sqrt (lemT z) : ℂ) * z := by rw [← h]

/-- **General homogeneity of `loopL`** for `0 < z.im`:
`L(H, z) = (√t₀)^n · L(√t₀ H, z_{t₀}^{(E)})`, `(E, t₀) = (lemE z, lemT z)`, `n` the loop length. -/
theorem GUEPhaseGrid_gloop_smul_lemT_eq
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ : List Bool) (a : List (Zd d L)) :
    loopL d L W M z ⟨σ, a⟩
      = ((Real.sqrt (lemT z) : ℝ) : ℂ) ^ (σ.zip a).length *
        loopL d L W (((Real.sqrt (lemT z) : ℝ) : ℂ) • M)
          (zt (lemE z) (lemT z)) ⟨σ, a⟩ := by
  have hs : ((Real.sqrt (lemT z) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (lemT_pos hz)).ne'
  rw [GUEPhaseGrid_zt_eq hz, GUEPhaseGrid_loopL_smul_mul hs]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]

/-- **General homogeneity of the 2-loop**: for `0 < z.im`,
`L(H, z) = t₀ · L(√t₀ H, z_{t₀}^{(E)})` on the loop `loopOf ![true, σ₂] ![a, b]`, `t₀ = lemT z`. -/
theorem GUEPhaseGrid_gloop_two_smul_lemT_eq
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ₂ : Bool) (a b : Zd d L) :
    loopL d L W M z (loopOf ![true, σ₂] ![a, b])
      = ((lemT z : ℝ) : ℂ) *
        loopL d L W (((Real.sqrt (lemT z) : ℝ) : ℂ) • M)
          (zt (lemE z) (lemT z)) (loopOf ![true, σ₂] ![a, b]) := by
  have hl : (loopOf ![true, σ₂] ![a, b] : Loop.LoopIdx (Zd d L)) = ⟨[true, σ₂], [a, b]⟩ := by
    simp [loopOf, List.ofFn_succ]
  have hlen : (([true, σ₂] : List Bool).zip [a, b]).length = 2 := rfl
  rw [hl, GUEPhaseGrid_gloop_smul_lemT_eq M hz [true, σ₂] [a, b], hlen, ← Complex.ofReal_pow,
    Real.sq_sqrt (lemT_pos hz).le]

end Homogeneity

end RBM.Univ.GUEPhase

/-! ## Compiled instances

The merged instance sizes `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`,
`N = 2097152`), `t₀ = 9/10`, `τ = 1/20`, `K = fun _ => 4`, `t₁ = (1 - ζ(τ)) t₀ = e^{-1/20} · 9/10`;
the homogeneity at `d = 3`, `L = 3`, `W = 2`. -/

namespace RBM.Univ.GUEPhase.GridCheck

open MeasureTheory ProbabilityTheory Matrix RBM RBM.Gauss RBM.Path RBM.Univ

/-- `t₁ = (1 - ζ(1/20)) · 9/10 = e^{-1/20} · 9/10 > 0`. -/
theorem t1_pos : 0 ≤ (1 - ouZeta (1 / 20)) * (9 / 10 : ℝ) := by
  unfold ouZeta
  have := Real.exp_pos (-(1 / 20 : ℝ))
  nlinarith

-- `gueH_isHermitian` at the instance data (`k = 4 = K`, and every `n`, `k`)
example (ω : PathΩ SizesInst.sz0) :
    (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
      (fun _ => 4) 0 4 ω).IsHermitian :=
  gueH_isHermitian SizesInst.sz0 _ _ _ 0 4 ω

example (n k : ℕ) (ω : PathΩ SizesInst.sz0) :
    (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
      (fun _ => 4) n k ω).IsHermitian :=
  gueH_isHermitian SizesInst.sz0 _ _ _ n k ω

-- `gueH_adapted` at the instance data: every entry `(i, j)` of size `n = 0` at step `4`
example (i j : Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0)) :
    StronglyMeasurable[filt SizesInst.sz0 4]
      (fun ω : PathΩ SizesInst.sz0 =>
        gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
          (fun _ => 4) 0 4 ω i j) :=
  gueH_adapted SizesInst.sz0 _ _ _ 0 4 i j

-- `gueH_measurable` at the instance data
example : Measurable
    (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
      (fun _ => 4) 0 4) :=
  gueH_measurable SizesInst.sz0 _ _ _ 0 4

-- `map_gueH_zero` at the instance data and `n = 0` (`L = 4`, `W = 32`, `N = 2097152`)
example :
    (Pgue SizesInst.sz0).map
        (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (fun _ => 4) 0 0) =
      (Sizes.seqP SizesInst.sz0).map
        (Sizes.seqHflow SizesInst.sz0 0 ((1 - ouZeta (1 / 20)) * (9 / 10))) :=
  map_gueH_zero SizesInst.sz0 _ _ _ 0 t1_pos

-- `map_gueH_last` at the instance data and `n = 0`
example :
    (Pgue SizesInst.sz0).map
        (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (fun _ => 4) 0 4) =
      (ouP (UNModel.band SizesInst.sz0) 0).map
        (fun ω => ((Real.sqrt (9 / 10) : ℝ) : ℂ) • ouMat (UNModel.band SizesInst.sz0) 0 (1 / 20) ω) :=
  map_gueH_last SizesInst.sz0 (fun _ => 9 / 10) (fun _ => 1 / 20) (fun _ => 4) 0
    (by norm_num) (by norm_num) (by norm_num)

-- the same for every size index `n`
example (n : ℕ) :
    (Pgue SizesInst.sz0).map
        (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (fun _ => 4) n 4) =
      (ouP (UNModel.band SizesInst.sz0) n).map
        (fun ω => ((Real.sqrt (9 / 10) : ℝ) : ℂ) •
          ouMat (UNModel.band SizesInst.sz0) n (1 / 20) ω) :=
  map_gueH_last SizesInst.sz0 (fun _ => 9 / 10) (fun _ => 1 / 20) (fun _ => 4) n
    (by norm_num) (by norm_num) (by norm_num)

-- the carrier is a probability measure
example : IsProbabilityMeasure (Pgue SizesInst.sz0) := inferInstance

-- `gueGridK_ne_zero` at the instance data
example : gueGridK SizesInst.sz0 0 0 ≠ 0 := gueGridK_ne_zero SizesInst.sz0 0 0

/-- `gueGridK sz n0 n` dominates `sz.size n + 1` at every size and every `n₀`. -/
theorem gueGridK_size_le {d : ℕ} (sz : Sizes d) (n0 n : ℕ) :
    sz.size n + 1 ≤ gueGridK sz n0 n := by
  unfold gueGridK
  exact Nat.le_self_pow (by omega) _

-- the 2-loop homogeneity at `d = 3`, `L = 3`, `W = 2`, `M = blockMat (2 • 1)`, `z = i`, `σ₂ = false`,
-- `a = b = 0`
example :
    loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
        Complex.I (loopOf ![true, false] ![(0 : Zd 3 3), 0]) =
      ((lemT Complex.I : ℝ) : ℂ) *
        loopL 3 3 2
          (((Real.sqrt (lemT Complex.I) : ℝ) : ℂ) •
            blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (zt (lemE Complex.I) (lemT Complex.I)) (loopOf ![true, false] ![(0 : Zd 3 3), 0]) :=
  GUEPhaseGrid_gloop_two_smul_lemT_eq _ (by simp) false 0 0

-- the general homogeneity at the same data, on the loop `[true, false]`, `[0, 0]`
example :
    loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
        Complex.I ⟨[true, false], [(0 : Zd 3 3), 0]⟩ =
      ((Real.sqrt (lemT Complex.I) : ℝ) : ℂ) ^ (([true, false] : List Bool).zip [(0 : Zd 3 3), 0]).length *
        loopL 3 3 2
          (((Real.sqrt (lemT Complex.I) : ℝ) : ℂ) •
            blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (zt (lemE Complex.I) (lemT Complex.I)) ⟨[true, false], [(0 : Zd 3 3), 0]⟩ :=
  GUEPhaseGrid_gloop_smul_lemT_eq _ (by simp) _ _

end RBM.Univ.GUEPhase.GridCheck

end
