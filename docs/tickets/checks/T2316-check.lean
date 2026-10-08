/-
Release check for T2316 (UN-27) (dispatcher V1, Thu Oct  8 01:40 UTC 2026; CLAUDE.md §4 step 0;
DECISIONS §16, §20, §29, §45 O2, §54, §57 (1)(2), §90, §91 (1)).
UN-27 (bulk universality, GUE phase): port of RBM2D `Universality/GUEPhase/Grid.lean` at `c9a24cf`
(888 lines; `:1-781` ported except the dead `GUEFlow`/`loopG` `:111-123` (no consumer at `c9a24cf`, deleted by
RBM2D 99d6fe0); the instance namespace `GridCheck` `:783-862` rewritten at `d = 3`) to `d ≥ 3`:
the GUE-phase grid carrier `Pgue sz` (the band field `seqP sz` at step `0`, unit GUE fields at steps `≥ 1`),
the path `gueH` (`H_k = √t₁ X + √(Δ/N) Σ_{i ≤ k} Y_i`, `N = (WL)^d`), the one-time laws (7.25)/(7.26)
(`map_gueH_zero`, `map_gueH_last`), `gueScale = N η_u`, `gueGridK`, the random-layer output `GUEPathBounds`,
and the Lemma 2.8 homogeneity of `loopL` (`GUEPhaseGrid_gloop_smul_lemT_eq`, `GUEPhaseGrid_gloop_two_smul_lemT_eq`).
Class G of T2173 (`docs/reports/T2173-portmap.md:248`): nothing is model-generic here; rule R1 `d : Sizes ↦
sz : Sizes d`; the BA step-0 field is the instance `Pgue (sz.withLam 0)`.
New file `RBM3D/Universality/GUEPhase/Grid.lean`, namespace `RBM.Univ.GUEPhase`.
Section 1: the merged names the new file builds on (full namespaces).
Section 2: vocabulary (`gueUnitVarV`, `gueUnitV`, `gueStepMeasureV`, `PgueV`, `gueHV`, `gueScaleV`, `gueGridKV`,
the two fields of `GUEPathBounds` as `GUEPathBoundsLkV`, `GUEPathBoundsLocalLawV`) and the pinned statements as
`def … : Prop` in the temporary namespace `RBM.Univ.GUEPhase.T2316Check`.  The library states each pin as a
theorem in `RBM.Univ.GUEPhase` whose type is exactly this body after unfolding the vocabulary.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2316-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- `RBM3D/Path/Walk.lean` (ddf5f74, MD-4 = T2018): the path carrier, the grid, the band walk and its laws
-- (the private `:281-597` are the d≥3 model of the source's `Algebra`/`MixedGrid`/`Identification` sections)
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.gridTime_last
#check @RBM.Path.pathH
#check @RBM.Path.pathH_isHermitian
#check @RBM.Path.measurable_pathH
#check @RBM.Path.pathH_adapted
#check @RBM.Path.map_pathH_eq
-- (namespace `RBM.Gauss`, `Path/Walk.lean:713-803`: measurability of `Gres`, `loopL`, `blockMat` in the matrix)
#check @RBM.Gauss.walk_measurable_Gres_apply
#check @RBM.Gauss.walk_measurable_loopL
#check @RBM.Gauss.walk_measurable_blockMat
-- `RBM3D/Defs/Sizes.lean`, `RBM3D/Gauss/FineModel.lean` (0a873f1, MD-1 = T2006)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.Sizes.neZeroW
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.card_Idx
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.SeqCoord
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqGvar
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.measurable_slice
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqXmat_isHermitian
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqHflow_eq_smul
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.Gauss.Sizes.measurable_seqHflow_entry
#check @RBM.Gauss.Idx
#check @RBM.Gauss.card_Idx
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.PF
#check @RBM.Gauss.Xentry
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Xmat_isHermitian
#check @RBM.Gauss.measurable_Xentry
#check @RBM.Gauss.Xmat_add
#check @RBM.Gauss.Xmat_smul
#check @RBM.Gauss.Xlinear
#check @RBM.Gauss.Hflow
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f, MD-2 = T2012): the one `≺` at the scale `size`
#check @RBM.badSetAt
#check @RBM.StochDomAt
#check @RBM.Gauss.Sizes.one_le_size
-- `RBM3D/Universality/Pins.lean` (f8ad4b4, UN-01 = T2174): `gueVar` at `N = (WL)^d`, the OU carrier on
-- `SeqΩ sz × Ω d L W`; `RBM3D/Universality/OU.lean` (a52eb85, UN-02a = T2177): the one-time Gaussian law
#check @RBM.Univ.gueVar
#check @RBM.Univ.gueP
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.ouP
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouMat_isHermitian
#check @RBM.Univ.isProbabilityMeasure_ouP
#check @RBM.Univ.ouSample
#check @RBM.Univ.ouVar
#check @RBM.Univ.ouMat_eq_Xmat_ouSample
#check @RBM.Univ.measurable_ouSample
#check @RBM.Univ.measurable_ouMat
#check @RBM.Univ.ouSample_law
#check @RBM.Univ.seqXmat_map_eq_ouMat_zero
-- `RBM3D/Universality/PinsK.lean` (fdbb6f0, UN-01b = T2187): the bridge to the model-generic OU interface
-- (consumers: `ouMatC (UNModel.band sz).toC = ouMat (UNModel.band sz)`)
#check @RBM.Univ.UNModel.toC
#check @RBM.Univ.ouMatC
#check @RBM.Univ.ouMatC_toC
#check @RBM.Univ.UNKind.band
-- `RBM3D/Universality/ZeroModeProfile.lean` (66cddb4, UN-51a = T2276)
#check @RBM.Univ.ouZeta
-- `RBM3D/Defs/Semicircle.lean` (fbc9870): the band flow and Lemma 2.8 (the RBM2D `Main/ZRescale` names)
#check @RBM.mE
#check @RBM.msc
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.zt
#check @RBM.zt_im
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.norm_msc_pos
#check @RBM.lemT_pos
#check @RBM.lemT_lt_one
#check @RBM.msc_eq_sqrt_mul_mE
#check @RBM.eq_inv_sqrt_mul_zt
#check @RBM.zt_im_lemma28
-- `RBM3D/Loop/GLoop.lean` (e0c58e6), `RBM3D/Loop/GLoopFlow.lean` (868b3b4, MD-3 = T2013),
-- `RBM3D/Loop/TreeRep.lean` (b06ff9b), `RBM3D/Gauss/Model.lean` (a722f63), `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_eq_zt_im
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.Gres
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.loopOf
#check @RBM.Gauss.loopL
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.gloopProd
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.σ
#check @RBM.Loop.LoopIdx.a
#check @RBM.Zd
-- `RBM3D/Green/EntryCore.lean` (890a89f): `green H z = (H - z)⁻¹` (the entry local law of `GUEPathBounds`);
-- `RBM3D/Induction/ConArgDet.lean` (bbd22a5): `Gres H z s = green H (zSig z s)` (not in the import closure
-- of the new file: import it, or unfold `Gres`/`green` through `Matrix.nonsing_inv_eq_ringInverse`)
#check @RBM.green
#check @RBM.Ind.zSig
#check @RBM.Ind.Gres_eq_green_zSig
-- the d≥3 model of the homogeneity section (private, copy): `RBM3D/Induction/ConArg.lean:380-442` (8a8cfeb)
#check @RBM.Ind.conArg
-- the consumers' tools, merged: `RBM3D/Universality/GUEPhase/BootstrapAt.lean` (0bc4633, UN-26b = T2212)
#check @RBM.Univ.GUEPhase.UnifDetDomAt
#check @RBM.Univ.GUEPhase.stochDomAt_of_forall_highProbAt

/-! ## 2. Vocabulary and pins -/

namespace RBM.Univ.GUEPhase.T2316Check

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **`gueUnitVar`** (RBM2D `Grid.lean:55`): unit GUE coordinate variance, `1` on the diagonal, `1/2` per
real component off it. -/
noncomputable def gueUnitVarV {d : ℕ} (sz : RBM.Gauss.Sizes d) (c : RBM.Gauss.Sizes.SeqCoord sz) : ℝ≥0 :=
  if c.2.1 = c.2.2.1 then 1 else 1 / 2

/-- **`gueUnit`** (`:58`): one unit GUE coordinate field, all sizes at once. -/
noncomputable def gueUnitV {d : ℕ} (sz : RBM.Gauss.Sizes d) : Measure (RBM.Gauss.Sizes.SeqΩ sz) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueUnitVarV sz c)

/-- **`gueStepMeasure`** (`:62`): the band field at step `0`, unit GUE fields at steps `k ≥ 1`. -/
noncomputable def gueStepMeasureV {d : ℕ} (sz : RBM.Gauss.Sizes d) : ℕ → Measure (RBM.Gauss.Sizes.SeqΩ sz)
  | 0 => RBM.Gauss.Sizes.seqP sz
  | _ + 1 => gueUnitV sz

/-- **`Pgue`** (`:67`): the GUE-phase grid measure on the path carrier `PathΩ sz`. -/
noncomputable def PgueV {d : ℕ} (sz : RBM.Gauss.Sizes d) : Measure (RBM.Path.PathΩ sz) :=
  Measure.infinitePi (gueStepMeasureV sz)

/-- **`gueH`** (`:83`): the GUE-phase grid path `H_k = √t₁ X + √(Δ/N) Σ_{i=1}^k Y_i`, `Δ = (t₀ - t₁)/K`,
`N = sz.size n = (W L)^d`. -/
noncomputable def gueHV {d : ℕ} (sz : RBM.Gauss.Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (ω : RBM.Path.PathΩ sz) :
    Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ :=
  (Real.sqrt (t1 n) : ℂ) • RBM.Gauss.Sizes.seqXmat sz n (ω 0) +
    (Real.sqrt (RBM.Path.gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) •
      ∑ i ∈ Finset.Icc 1 k, RBM.Gauss.Sizes.seqXmat sz n (ω i)

/-- **`gueScale`** (`:90`): `N η_u` of the GUE phase, `N = (W L)^d`. -/
noncomputable def gueScaleV {d : ℕ} (sz : RBM.Gauss.Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ((sz.size n : ℕ) : ℝ) * RBM.Gauss.etaT (E n) u

/-- **`gueGridK`** (`:126`): the grid size `K n = (sz.size n + 1)^(32 n₀ + 64)` (in the matrix dimension
`N = (W L)^d`; a proof device, never a hypothesis witness). -/
def gueGridKV {d : ℕ} (sz : RBM.Gauss.Sizes d) (n0 n : ℕ) : ℕ := (sz.size n + 1) ^ (32 * n0 + 64)

/-- The field `lk` of **`GUEPathBounds`** (`:96-104`): (7.28) for loops of length `1 ≤ m ≤ n₀` against a
primitive family `Kt`, on `blockMat` with the list-based loop `loopL … (loopOf σ a)`. -/
def GUEPathBoundsLkV {d : ℕ} (sz : RBM.Gauss.Sizes d) (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (RBM.Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n0 → RBM.StochDomAt (PgueV sz) sz.size
    (fun n (p : Fin (K n + 1) × (Fin m → Bool) × (Fin m → RBM.Zd d (sz.L n))) ω =>
      ‖RBM.Gauss.loopL d (sz.L n) (sz.W n)
          (RBM.Gauss.blockMat d (sz.L n) (sz.W n) (gueHV sz t1 t0 K n p.1 ω))
          (RBM.zt (E n) (RBM.Path.gridTime t1 t0 K n p.1)) (RBM.Gauss.loopOf p.2.1 p.2.2) -
        Kt n (RBM.Path.gridTime t1 t0 K n p.1) (RBM.Gauss.loopOf p.2.1 p.2.2)‖)
    (fun n p _ => (gueScaleV sz E n (RBM.Path.gridTime t1 t0 K n p.1))⁻¹ ^ m)

/-- The field `localLaw` of **`GUEPathBounds`** (`:105-111`): `‖G̃ - m‖_max ≺ (N η_u)^{-1/2}` at the grid
times, with `RBM.green` and the scalar `mE (E n)` (band form; the BA form is BA-C5). -/
def GUEPathBoundsLocalLawV {d : ℕ} (sz : RBM.Gauss.Sizes d) (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  RBM.StochDomAt (PgueV sz) sz.size
    (fun n (p : Fin (K n + 1) ×
        (RBM.Gauss.Idx d (sz.L n) (sz.W n) × RBM.Gauss.Idx d (sz.L n) (sz.W n))) ω =>
      ‖(RBM.green (gueHV sz t1 t0 K n p.1 ω) (RBM.zt (E n) (RBM.Path.gridTime t1 t0 K n p.1)) -
          RBM.mE (E n) •
            (1 : Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ))
        p.2.1 p.2.2‖)
    (fun n p _ => (gueScaleV sz E n (RBM.Path.gridTime t1 t0 K n p.1))⁻¹ ^ ((1 : ℝ) / 2))

/-- Pin `T2316_Pgue_isProbabilityMeasure` (`:76`, the instance `Pgue_isProbabilityMeasure`). -/
def T2316_Pgue_isProbabilityMeasure : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d), IsProbabilityMeasure (PgueV sz)

/-- Pin `T2316_gueH_isHermitian` (`:188`). -/
def T2316_gueH_isHermitian : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : RBM.Path.PathΩ sz),
    (gueHV sz t1 t0 K n k ω).IsHermitian

/-- Pin `T2316_gueH_adapted` (`:205`): the entries of `H_k` are `filt sz k`-measurable. -/
def T2316_gueH_adapted : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (i j : RBM.Gauss.Idx d (sz.L n) (sz.W n)),
    StronglyMeasurable[RBM.Path.filt sz k] (fun ω : RBM.Path.PathΩ sz => gueHV sz t1 t0 K n k ω i j)

/-- Pin `T2316_gueH_measurable` (`:229`). -/
def T2316_gueH_measurable : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ),
    Measurable (gueHV sz t1 t0 K n k)

/-- Pin `T2316_map_gueH_zero` (`:560`; (7.25) at step `0`): the law of the band flow at `t₁`. -/
def T2316_map_gueH_zero : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ), 0 ≤ t1 n →
    (PgueV sz).map (gueHV sz t1 t0 K n 0) =
      (RBM.Gauss.Sizes.seqP sz).map (RBM.Gauss.Sizes.seqHflow sz n (t1 n))

/-- Pin `T2316_map_gueH_last` (`:577`; (7.25)/(7.26) at the last step): with `t₁ = (1 - ζ(τ)) t₀` the law of
`H_K` is that of `√t₀ · 𝐇_τ` of the band OU flow (`ouP (UNModel.band sz) n` on `SeqΩ sz × Ω`, the merged
`ouSample_law` form; coordinate variances `t₀ (e^{-τ} S_c + (1 - e^{-τ}) N⁻¹_c)`, every `sz.lam`). -/
def T2316_map_gueH_last : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ),
    0 ≤ t0 n → 0 ≤ τ n → K n ≠ 0 →
    (PgueV sz).map (gueHV sz (fun n => (1 - RBM.Univ.ouZeta (τ n)) * t0 n) t0 K n (K n)) =
      (RBM.Univ.ouP (RBM.Univ.UNModel.band sz) n).map
        (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n (τ n) ω)

/-- Pin `T2316_gueGridK_ne_zero` (`:128`). -/
def T2316_gueGridK_ne_zero : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n0 n : ℕ), gueGridKV sz n0 n ≠ 0

/-- Pin `T2316_gloop_smul_lemT_eq` (`:751`, `GUEPhaseGrid_gloop_smul_lemT_eq`): for `0 < z.im`,
`L(H, z) = (√t₀)^n · L(√t₀ H, z_{t₀}^{(E)})`, `(E, t₀) = (lemE z, lemT z)`, `n` the loop length; on the
block-product index `Vtx d L W` (callers pass `blockMat … M`). -/
def T2316_gloop_smul_lemT_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (M : Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ)
    (z : ℂ), 0 < z.im → ∀ (σ : List Bool) (a : List (RBM.Zd d L)),
    RBM.Gauss.loopL d L W M z ⟨σ, a⟩ =
      ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ^ (σ.zip a).length *
        RBM.Gauss.loopL d L W (((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • M)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨σ, a⟩

/-- Pin `T2316_gloop_two_smul_lemT_eq` (`:766`, `GUEPhaseGrid_gloop_two_smul_lemT_eq`): the 2-loop form
`L(H, z) = t₀ · L(√t₀ H, z_{t₀}^{(E)})` on `loopOf ![true, σ₂] ![a, b]` (consumer UN-47 `Eq729B`). -/
def T2316_gloop_two_smul_lemT_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (M : Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ)
    (z : ℂ), 0 < z.im → ∀ (σ₂ : Bool) (a b : RBM.Zd d L),
    RBM.Gauss.loopL d L W M z (RBM.Gauss.loopOf ![true, σ₂] ![a, b]) =
      ((RBM.lemT z : ℝ) : ℂ) *
        RBM.Gauss.loopL d L W (((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • M)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) (RBM.Gauss.loopOf ![true, σ₂] ![a, b])

/-! Prop-valued shape checks (no proof obligation): the two fields of `GUEPathBounds` as one statement, and
the instance data of the ticket at `SizesInst.sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`, `N = 2097152`), `t₀ = 9/10`,
`τ = 1/20`, `K ≡ 4`, `t₁ = (1 - ζ(1/20)) · 9/10`; the homogeneity at `d = 3`, `L = 3`, `W = 2`, `z = i`. -/

example : Prop := T2316_Pgue_isProbabilityMeasure ∧ T2316_gueH_isHermitian ∧ T2316_gueH_adapted ∧
  T2316_gueH_measurable ∧ T2316_map_gueH_zero ∧ T2316_map_gueH_last ∧ T2316_gueGridK_ne_zero ∧
  T2316_gloop_smul_lemT_eq ∧ T2316_gloop_two_smul_lemT_eq

example {d : ℕ} (sz : RBM.Gauss.Sizes d) (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (RBM.Zd d (sz.L n)) → ℂ) : Prop :=
  GUEPathBoundsLkV sz E t1 t0 K n0 Kt ∧ GUEPathBoundsLocalLawV sz E t1 t0 K

example : Prop :=
  ∀ ω : RBM.Path.PathΩ RBM.Gauss.SizesInst.sz0,
    (gueHV RBM.Gauss.SizesInst.sz0 (fun _ => (1 - RBM.Univ.ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
      (fun _ => 4) 0 4 ω).IsHermitian

example : Prop :=
  ∀ i j : RBM.Gauss.Idx 3 (RBM.Gauss.SizesInst.sz0.L 0) (RBM.Gauss.SizesInst.sz0.W 0),
    StronglyMeasurable[RBM.Path.filt RBM.Gauss.SizesInst.sz0 4]
      (fun ω : RBM.Path.PathΩ RBM.Gauss.SizesInst.sz0 =>
        gueHV RBM.Gauss.SizesInst.sz0 (fun _ => (1 - RBM.Univ.ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (fun _ => 4) 0 4 ω i j)

example : Prop :=
  (PgueV RBM.Gauss.SizesInst.sz0).map
      (gueHV RBM.Gauss.SizesInst.sz0 (fun _ => (1 - RBM.Univ.ouZeta (1 / 20)) * (9 / 10))
        (fun _ => 9 / 10) (fun _ => 4) 0 0) =
    (RBM.Gauss.Sizes.seqP RBM.Gauss.SizesInst.sz0).map
      (RBM.Gauss.Sizes.seqHflow RBM.Gauss.SizesInst.sz0 0 ((1 - RBM.Univ.ouZeta (1 / 20)) * (9 / 10)))

example : Prop :=
  (PgueV RBM.Gauss.SizesInst.sz0).map
      (gueHV RBM.Gauss.SizesInst.sz0 (fun _ => (1 - RBM.Univ.ouZeta (1 / 20)) * (9 / 10))
        (fun _ => 9 / 10) (fun _ => 4) 0 4) =
    (RBM.Univ.ouP (RBM.Univ.UNModel.band RBM.Gauss.SizesInst.sz0) 0).map
      (fun ω => ((Real.sqrt (9 / 10) : ℝ) : ℂ) •
        RBM.Univ.ouMat (RBM.Univ.UNModel.band RBM.Gauss.SizesInst.sz0) 0 (1 / 20) ω)

example : Prop :=
  ∀ n0 n : ℕ, RBM.Gauss.SizesInst.sz0.size n + 1 ≤ gueGridKV RBM.Gauss.SizesInst.sz0 n0 n

example : Prop :=
  RBM.Gauss.loopL 3 3 2 (RBM.Gauss.blockMat 3 3 2 (Matrix.diagonal fun _ : RBM.Gauss.Idx 3 3 2 => (2 : ℂ)))
      Complex.I (RBM.Gauss.loopOf ![true, false] ![(0 : RBM.Zd 3 3), 0]) =
    ((RBM.lemT Complex.I : ℝ) : ℂ) *
      RBM.Gauss.loopL 3 3 2
        (((Real.sqrt (RBM.lemT Complex.I) : ℝ) : ℂ) •
          RBM.Gauss.blockMat 3 3 2 (Matrix.diagonal fun _ : RBM.Gauss.Idx 3 3 2 => (2 : ℂ)))
        (RBM.zt (RBM.lemE Complex.I) (RBM.lemT Complex.I))
        (RBM.Gauss.loopOf ![true, false] ![(0 : RBM.Zd 3 3), 0])

end RBM.Univ.GUEPhase.T2316Check
