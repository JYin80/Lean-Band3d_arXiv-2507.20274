/-
Release check for T2212 (dispatcher V1, Mon Oct  5 19:54 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §29, §45 O2,
§54, §57 (2), §66).
UN-26b (bulk universality, GUE phase, third ticket): the abstract bootstraps of the GUE phase on the size scale, port of
RBM2D `Universality/GUEPhase/BootstrapAt.lean` at `c9a24cf` (all 855 lines; every declaration is live at RBM2D HEAD
`9e0f275`) to `d` dimensions: `UnifDetDomAt`, `eventually_size_rpow_le_of_neg`, `stochDomAt_of_forall_highProbAt`,
`eq736_detDomAt` ((7.36), the only `d`-dependent statement: `LoopIdx (Zd d (Lf N))`, `primRhsGUE d`, `LoopSet d`,
`(W L)^d` in (7.30)), `eq728GAt` ((7.46)G ⟹ (7.28)), `eq727GEAt` ((7.45)G at even lengths ⟹ (7.27)), plus the new
bridge `unifDetDom_iff_at_id`.  Class G of T2173 (`docs/reports/T2173-portmap.md:236`): no matrix model, no `m`; the
measure `P`, the scale `size` and the size function `Nf` are abstract, so the file is model-generic over `UNKind` /
`UNModelC` as it stands (DECISIONS §57 (2)).  No `UNDens`, `UNStep1Good`, `UNInfty1Row`, `UNCore`, `UNStep1GoodC`,
`UNCoreC` (§66) or primed successor occurs.
Section 1: the merged names the new file builds on (and the consumer-side `Sizes.size`), and the Mathlib names of the
route (same Mathlib revision `5ed2965` as RBM2D `c9a24cf`).
Section 2: vocabulary (`UnifDetDomAtV`) and the pinned statements as `def … : Prop` in the temporary namespace
`RBM.Univ.GUEPhase.T2212Check`.  The library states each pin as a theorem in `RBM.Univ.GUEPhase` whose type unfolds to
exactly this body (only `Type` → `Type*` in the binders `Ω`, `U` may differ: instance as `@name.{0, 0}` / `.{0}`);
`UnifDetDomAtV` is `rfl`-equal to the library `UnifDetDomAt`.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2212-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- `RBM3D/Universality/GUEPhase/Bootstrap.lean` (98e6d5b, UN-26a = T2202): used by the port
#check @RBM.Univ.GUEPhase.continuity_argument
#check @RBM.Univ.GUEPhase.supOn
#check @RBM.Univ.GUEPhase.supOn_le
#check @RBM.Univ.GUEPhase.supOn_nonneg
#check @RBM.Univ.GUEPhase.rhs745G
#check @RBM.Univ.GUEPhase.rhs746G
#check @RBM.Univ.GUEPhase.supOn_line1_le
#check @RBM.Univ.GUEPhase.mul_le_of_eq730
#check @RBM.Univ.GUEPhase.sqrt_mul_sqrt_le
#check @RBM.Univ.GUEPhase.inv_mul_pow
#check @RBM.Univ.GUEPhase.eventually_rpow_le_of_neg
#check @RBM.Univ.GUEPhase.eventually_small
#check @RBM.Univ.GUEPhase.eq736
#check @RBM.Univ.GUEPhase.LoopSet
#check @RBM.Univ.GUEPhase.primRhsGUE
-- instance data of UN-26a reused by the instances of this ticket
#check @RBM.Univ.GUEPhase.BootstrapCheck.primRhsGUE_zero
#check @RBM.Univ.GUEPhase.BootstrapCheck.kTight
#check @RBM.Univ.GUEPhase.BootstrapCheck.kTight_hasDerivAt
#check @RBM.Univ.GUEPhase.BootstrapCheck.kTight_zero
#check @RBM.Univ.GUEPhase.BootstrapCheck.primRhsGUE_const_len_two
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f): replaces the `At` part of RBM2D `Defs/StochDom` and `Gauss/Domination`
#check @RBM.badSetAt
#check @RBM.StochDomAt
#check @RBM.stochDom_iff_at_id
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.highProb_iff_at_id
#check @RBM.Path.TimeIcc
#check @RBM.StochDomAt.refl
#check @RBM.StochDomAt.of_le_left
#check @RBM.StochDomAt.of_unifDetDom
#check @RBM.Gauss.HighProbAt.of_eventually_univ
-- `RBM3D/Gauss/DominationAt.lean` (9e2b00f): the RBM2D instance pattern's `highProbAt_univ` (optional import)
#check @RBM.Gauss.highProbAt_univ
-- `RBM3D/Induction/PerTimeCalc.lean` (5d1e6b1)
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt
-- `RBM3D/Defs/Domination.lean` (4c5302f), `RBM3D/Defs/StochDom.lean` (1c2e756): the index-scale notions (`size = id`)
#check @RBM.UnifDetDom
#check @RBM.UnifDetDom.of_le
#check @RBM.eventually_le_rpow
#check @RBM.StochDom
#check @RBM.HighProb
-- `RBM3D/Defs/Lattice.lean` (51f1a17), `RBM3D/Loop/TreeRep.lean` (b06ff9b)
#check @RBM.Zd
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.WF
#check @RBM.Loop.LoopIdx.length
-- consumer side (not imported by the new file): `RBM3D/Defs/Sizes.lean` (0a873f1) `size n = (W n * L n)^d`
-- (`:157`), the scale of UN-33/47/50; the `NeZero (sz.L n)` instance (`:152`)
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.neZeroL
-- Mathlib names of the route (all used verbatim in the RBM2D source)
#check @Set.finite_Icc
#check @Set.Icc_subset_Icc_right
#check @Set.eq_empty_of_forall_notMem
#check @Nat.even_or_odd
#check @even_two_mul
#check @Filter.tendsto_atTop_mono
#check @Real.one_le_rpow
#check @Real.rpow_le_one_of_one_le_of_nonpos
#check @Real.rpow_natCast
#check @Real.rpow_mul
#check @Real.rpow_add
#check @Real.rpow_nonneg
#check @Real.rpow_pos_of_pos
#check @Real.rpow_neg_one
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_mul
#check @Real.sqrt_sq
#check @one_div_le_one_div_of_le
#check @pow_le_pow_right₀
#check @one_le_pow₀
#check @inv_anti₀
#check @ContinuousOn.inv₀
#check @MeasureTheory.measure_mono
#check @MeasureTheory.Measure.dirac

/-! ## 2. Vocabulary and pinned statements -/

set_option linter.unusedVariables false

noncomputable section

namespace RBM.Univ.GUEPhase.T2212Check

open Filter

/-- `UnifDetDom` along a scale `size`: `f ≺ g` with the factor `(size N)^τ`.  RBM2D `UnifDetDomAt`
(`BootstrapAt.lean:532`), verbatim. -/
def UnifDetDomAtV (size : ℕ → ℕ) {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ ((size N : ℕ) : ℝ) ^ τ * g N u

/-- Target 1' (new, `unifDetDom_iff_at_id`): the merged `RBM.UnifDetDom` (`Defs/Domination.lean:52`) is
`UnifDetDomAt` at `size = id` (`Iff.rfl`), as `RBM.stochDom_iff_at_id` (`Defs/StochDomAt.lean:67`) and
`RBM.Gauss.highProb_iff_at_id` (`:86`) are: the index-scale `eq736_detDom` of RBM2D is `eq736_detDomAt` at `size = id`. -/
def T2212_unifDetDom_iff_at_id : Prop :=
  ∀ {U : ℕ → Type} (f g : ∀ N, U N → ℝ), RBM.UnifDetDom f g ↔ UnifDetDomAtV id f g

/-- Target 2 (`eventually_size_rpow_le_of_neg`): RBM2D `BootstrapAt.lean:536`, verbatim. -/
def T2212_eventually_size_rpow_le_of_neg : Prop :=
  ∀ {size : ℕ → ℕ}, Tendsto size atTop atTop → ∀ {a ρ : ℝ}, a < 0 → 0 < ρ →
    ∀ᶠ N : ℕ in atTop, ((size N : ℕ) : ℝ) ^ a ≤ ρ

/-- Target 3 (`stochDomAt_of_forall_highProbAt`): RBM2D `BootstrapAt.lean:543`, verbatim (consumer RBM2D
`BoundsA.lean:756-757`, UN-33). -/
def T2212_stochDomAt_of_forall_highProbAt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type}
    {ξ ζ : ∀ N, U N → Ω → ℝ},
    (∀ τ > (0 : ℝ), RBM.Gauss.HighProbAt P size
      (fun N => {ω | ∀ u, ξ N u ω ≤ ((size N : ℕ) : ℝ) ^ τ * ζ N u ω})) →
    RBM.StochDomAt P size ξ ζ

/-- Target 4 (`eq736_detDomAt`): (7.36) on the size scale.  RBM2D `BootstrapAt.lean:565` with the dimension `d`
explicit after `hsize`, `Z2 (Lf N) ↦ Zd d (Lf N)`, `primRhsGUE (Lf N) (Wf N) ↦ primRhsGUE d (Lf N) (Wf N)`,
`LoopSet (Lf N) n ↦ LoopSet d (Lf N) n`, `((Wf N * Lf N)^2 : ℕ) ↦ ((Wf N * Lf N)^d : ℕ)` in (7.30) (consumer RBM2D
`Eq729B.lean:317`, `:323`, UN-47; there `size = Sizes.size`, `((W L)^d : ℕ) = size` by `rfl`, `Defs/Sizes.lean:157`). -/
def T2212_eq736_detDomAt : Prop :=
  ∀ (size : ℕ → ℕ), Tendsto size atTop atTop → ∀ (d : ℕ) (Lf Wf : ℕ → ℕ) [∀ N, NeZero (Lf N)]
    (Kt : ∀ N, ℝ → RBM.Loop.LoopIdx (RBM.Zd d (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ),
    (∀ N, t1 N ≤ t0 N) → ∀ (lam : ℕ → ℝ → ℝ),
    (∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), 0 < lam N t) →
    (∀ N, ∀ u ∈ Set.Icc (t1 N) (t0 N), ∀ t ∈ Set.Icc (t1 N) (t0 N), u ≤ t → lam N t ≤ lam N u) →
    (∀ N, ContinuousOn (lam N) (Set.Icc (t1 N) (t0 N))) →
    (∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), ∀ I : RBM.Loop.LoopIdx (RBM.Zd d (Lf N)), I.WF →
      2 ≤ I.length → I.length ≤ n →
      HasDerivWithinAt (fun s => Kt N s I)
        (RBM.Univ.GUEPhase.primRhsGUE d (Lf N) (Wf N) (Kt N t) I) (Set.Icc (t1 N) (t0 N)) t) →
    ∀ {τU : ℝ}, 0 < τU →
    (∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      (((Wf N * Lf N) ^ d : ℕ) : ℝ) * (t - t1 N) ≤ ((size N : ℕ) : ℝ) ^ (-τU) * lam N t) →
    UnifDetDomAtV size (fun N (I : RBM.Univ.GUEPhase.LoopSet d (Lf N) n) => ‖Kt N (t1 N) I.1‖)
      (fun N I => (lam N (t1 N))⁻¹ ^ (I.1.length - 1)) →
    UnifDetDomAtV size
      (fun N (p : RBM.Path.TimeIcc t1 t0 N × RBM.Univ.GUEPhase.LoopSet d (Lf N) n) => ‖Kt N p.1 p.2.1‖)
      (fun N p => (lam N p.1)⁻¹ ^ (p.2.1.length - 1))

/-- Target 5 (`eq728GAt`): (7.46)G ⟹ (7.28) on the size scale.  RBM2D `BootstrapAt.lean:619`, verbatim (`d`-free:
`Nf` abstract, `size N = (W L)^d` at the consumer RBM2D `PathBounds.lean:507`, UN-50). -/
def T2212_eq728GAt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (size : ℕ → ℕ),
    Tendsto size atTop atTop → ∀ {n0 : ℕ} (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ),
    (∀ N, 0 < Nf N) → (∀ N, t1 N ≤ t0 N) →
    (∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), 0 < η N t) →
    (∀ N, ∀ u ∈ Set.Icc (t1 N) (t0 N), ∀ t ∈ Set.Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u) →
    (∀ N, ContinuousOn (η N) (Set.Icc (t1 N) (t0 N))) →
    ∀ {τU : ℝ}, 0 < τU →
    (∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      t - t1 N ≤ ((size N : ℕ) : ℝ) ^ (-τU) * η N t) →
    (∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      (Nf N * η N t)⁻¹ ≤ ((size N : ℕ) : ℝ) ^ (-τU)) →
    (∀ N m t ω, 0 ≤ Lm N m t ω) → (∀ N m t ω, 0 ≤ Dm N m t ω) →
    RBM.StochDomAt P size
      (fun N (p : RBM.Path.TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) →
    RBM.Gauss.HighProbAt P size (fun N => {ω | ∀ m ∈ Set.Icc 1 n0,
      ContinuousOn (fun t => Dm N m t ω) (Set.Icc (t1 N) (t0 N))}) →
    RBM.StochDomAt P size
      (fun N (p : RBM.Path.TimeIcc t1 t0 N × Set.Icc 1 n0) ω => Dm N p.2 p.1 ω)
      (fun N p ω => RBM.Univ.GUEPhase.rhs746G (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω)
        (fun m t => Dm N m t ω) p.2 p.1) →
    RBM.StochDomAt P size
      (fun N (p : RBM.Path.TimeIcc t1 t0 N × Set.Icc 1 n0) ω => Dm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ (p.2 : ℕ))

/-- Target 6 (`eq727GEAt`): (7.45)G at even lengths ⟹ (7.27) on the size scale, the odd lengths by
`L_{2l+1} ≤ √(L_{2l} L_{2l+2})`.  RBM2D `BootstrapAt.lean:683`, verbatim (consumer RBM2D `PathBounds.lean:491`, UN-50,
at `n0 := 2 * n0`, whose output is the `h727` of target 5). -/
def T2212_eq727GEAt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (size : ℕ → ℕ),
    Tendsto size atTop atTop → ∀ {n0 : ℕ}, Even n0 → ∀ (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ) (Km : ℕ → ℕ → ℝ → ℝ),
    (∀ N, 0 < Nf N) → (∀ N, t1 N ≤ t0 N) →
    (∀ N, ∀ t ∈ Set.Icc (t1 N) (t0 N), 0 < η N t) →
    (∀ N, ∀ u ∈ Set.Icc (t1 N) (t0 N), ∀ t ∈ Set.Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u) →
    (∀ N, ContinuousOn (η N) (Set.Icc (t1 N) (t0 N))) →
    ∀ {τU : ℝ}, 0 < τU →
    (∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      t - t1 N ≤ ((size N : ℕ) : ℝ) ^ (-τU) * η N t) →
    (∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (t1 N) (t0 N),
      (Nf N * η N t)⁻¹ ≤ ((size N : ℕ) : ℝ) ^ (-τU)) →
    (∀ N m t ω, 0 ≤ Lm N m t ω) → (∀ N m t ω, 0 ≤ Dm N m t ω) →
    (∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Set.Icc (t1 N) (t0 N), Lm N m t ω ≤ Dm N m t ω + Km N m t) →
    (∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Set.Icc (t1 N) (t0 N), Dm N m t ω ≤ Lm N m t ω + Km N m t) →
    (∀ N ω, ∀ l : ℕ, 1 ≤ l → 2 * l + 2 ≤ n0 → ∀ t ∈ Set.Icc (t1 N) (t0 N),
      Lm N (2 * l + 1) t ω ≤ Real.sqrt (Lm N (2 * l) t ω * Lm N (2 * l + 2) t ω)) →
    UnifDetDomAtV size (fun N (p : RBM.Path.TimeIcc t1 t0 N × Set.Icc 2 n0) => Km N p.2 p.1)
      (fun N p => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) →
    RBM.Gauss.HighProbAt P size (fun N => {ω | ∀ m ∈ Set.Icc 2 n0, Even m →
      ContinuousOn (fun t => Lm N m t ω) (Set.Icc (t1 N) (t0 N))}) →
    RBM.StochDomAt P size
      (fun N (p : RBM.Path.TimeIcc t1 t0 N × {m : ℕ // m ∈ Set.Icc 2 n0 ∧ Even m}) ω =>
        Dm N p.2.1 p.1 ω)
      (fun N p ω => RBM.Univ.GUEPhase.rhs745G (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω)
        (fun m t => Dm N m t ω) p.2.1 p.1) →
    RBM.StochDomAt P size
      (fun N (p : RBM.Path.TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1))

/-- The data of the instances are nondegenerate: (a) the tight `eq736_detDomAt` instance (`d = 3`, `L = 3`, `W = 2`,
`(W L)^d = 216`, window `[0, 1/(N+1)]`, `λ ≡ 7000`, `τ_U = 1`, `size N = N + 1`): `216 t ≤ (N+1)^{-1} · 7000` at
`t = 1/(N+1)`; (b) `x_N = (N + 1)^{-1} ≤ 1` (the positive `L`/`D`/`K` data of targets 5 and 6); (c) the zero
`eq736_detDomAt` instance (window `[0, 1]`, `λ_N = 216 (N + 1)`, the RBM2D `lamD` with `36 ↦ 216`): `216 ≤ 216`. -/
def T2212_inst_bounds : Prop :=
  (∀ N : ℕ, (((2 * 3) ^ 3 : ℕ) : ℝ) * (1 / ((N : ℝ) + 1) - 0) ≤
      ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) * 7000) ∧
    (∀ N : ℕ, ((N : ℝ) + 1)⁻¹ ≤ 1) ∧
    (∀ N : ℕ, (((2 * 3) ^ 3 : ℕ) : ℝ) * (1 - 0) ≤
      ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) * (216 * ((N : ℝ) + 1)))

/-- Consumer shape (UN-47, RBM2D `Eq729B.lean:304-313`): the count `(W L)^d` of (7.30) in target 4 is the scale
`Sizes.size` (`Defs/Sizes.lean:157`); the library proof at the consumer is `rfl`. -/
example (sz : RBM.Gauss.Sizes 3) (n : ℕ) : Prop :=
  (((sz.W n * sz.L n) ^ 3 : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ)

/-- Consumer shape (UN-47, RBM2D `Eq729B.lean:317`): the hypothesis `h732` of target 4 at `size = Sizes.size`,
`Lf = Sizes.L`, `n = 3` (the instance `[∀ N, NeZero (Lf N)]` of target 4 is then `Sizes.neZeroL`). -/
example (sz : RBM.Gauss.Sizes 3) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (RBM.Zd 3 (sz.L n)) → ℂ) (t1 : ℕ → ℝ)
    (lam : ℕ → ℝ → ℝ) : Prop :=
  UnifDetDomAtV sz.size (fun n (I : RBM.Univ.GUEPhase.LoopSet 3 (sz.L n) 3) => ‖Kt n (t1 n) I.1‖)
    (fun n I => (lam n (t1 n))⁻¹ ^ (I.1.length - 1))

end RBM.Univ.GUEPhase.T2212Check

end

#check @RBM.Univ.GUEPhase.T2212Check.UnifDetDomAtV
#check (RBM.Univ.GUEPhase.T2212Check.T2212_unifDetDom_iff_at_id : Prop)
#check (RBM.Univ.GUEPhase.T2212Check.T2212_eventually_size_rpow_le_of_neg : Prop)
#check (RBM.Univ.GUEPhase.T2212Check.T2212_stochDomAt_of_forall_highProbAt : Prop)
#check (RBM.Univ.GUEPhase.T2212Check.T2212_eq736_detDomAt : Prop)
#check (RBM.Univ.GUEPhase.T2212Check.T2212_eq728GAt : Prop)
#check (RBM.Univ.GUEPhase.T2212Check.T2212_eq727GEAt : Prop)
#check (RBM.Univ.GUEPhase.T2212Check.T2212_inst_bounds : Prop)
