/-
Release check for T2330 (dispatcher V1, Thu Oct  8 11:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §146, §145, §91 (1), §54).
UN-33 (bulk universality, GUE phase): `RBM3D/Universality/GUEPhase/BoundsA.lean`, port of RBM2D
`Universality/GUEPhase/BoundsA.lean` (718 lines): the pathwise unfreezing `Bounds_path` and the interface
`pathBounds_of_forall_highProbAt` with `GUEPathBounds`.
Section 1: merged names (exact namespaces; `main` c99e133).  Section 2: `HC`, `Concl` (definitions, copied verbatim into
`RBM.Univ.GUEPhase.BoundsACheck`) and the seven target statements (renaming of `GUEPhase/Grid.lean`, T2316, and `Proc.lean`,
T2322: `d : Sizes` ↦ `sz : Sizes d`, `Idx (d.L n) (d.W n)` ↦ `Idx d (sz.L n) (sz.W n)`, `Z2` ↦ `Zd d`,
`spectralZ`/`spectralM` ↦ `zt`/`mE`, `gloop L W (blockMat M)` ↦ `loopL d L W (blockMat d L W M)`; the two `d`-dependent
lines: `(W²)⁻¹` ↦ `(W^d)⁻¹` and `hellN : L² (1 - t₁) ≤ 1` ↦ `L^d (1 - t₁) ≤ 1`).
Statements, definitions and `#check` only.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2330-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Proc
import RBM3D.Universality.GUEPhase.BootstrapAt
import RBM3D.Universality.GUEPhase.Markov

/-! ## 1. Merged names -/

#check @RBM.Univ.GUEPhase.GUEPathBounds                       -- Grid.lean:89
#check @RBM.Univ.GUEPhase.Pgue                                -- Grid.lean:61
#check @RBM.Univ.GUEPhase.gueH                                -- Grid.lean:77
#check @RBM.Univ.GUEPhase.gueScale                            -- Grid.lean:84
#check @RBM.Univ.GUEPhase.gueGridK                            -- Grid.lean:106
#check @RBM.Univ.GUEPhase.gueDelta                            -- Proc.lean:71
#check @RBM.Univ.GUEPhase.gueDev                              -- Proc.lean:83
#check @RBM.Univ.GUEPhase.gueStop                             -- Proc.lean:89
#check @RBM.Univ.GUEPhase.gueLmax                             -- Proc.lean:93
#check @RBM.Univ.GUEPhase.gueDmax                             -- Proc.lean:98
#check @RBM.Univ.GUEPhase.gueLproc                            -- Proc.lean:112
#check @RBM.Univ.GUEPhase.gueDproc                            -- Proc.lean:116
#check @RBM.Univ.GUEPhase.gueDev_succ_le                      -- Proc.lean:771
#check @RBM.Univ.GUEPhase.gueLproc_time                       -- Proc.lean:460
#check @RBM.Univ.GUEPhase.gueDproc_time                       -- Proc.lean:469
#check @RBM.Univ.GUEPhase.gue_highProb_incr_le                -- Markov.lean:863 (T2327)
#check @RBM.Univ.GUEPhase.stochDomAt_of_forall_highProbAt     -- BootstrapAt.lean:551
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono       -- Induction/PerTimeCalc.lean:112
#check @RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt  -- Induction/PerTimeCalc.lean:130
#check @RBM.Path.firstHit                                     -- Path/Stop.lean:42
#check @RBM.Path.gridTime                                     -- Path/Walk.lean:70
#check @RBM.Path.gridStep                                     -- Path/Walk.lean:67
#check @RBM.Gauss.loopL                                       -- Loop/GLoopFlow.lean:123
#check @RBM.Gauss.blockMat                                    -- Loop/GLoopFlow.lean:105
#check @RBM.Gauss.loopOf                                      -- Loop/GLoopFlow.lean:117
#check @RBM.green                                             -- Green/EntryCore.lean:34
#check @RBM.zt                                                -- Defs/Semicircle.lean:179
#check @RBM.mE                                                -- Defs/Semicircle.lean:38
#check @RBM.Gauss.spectralM_im_pos                            -- Gauss/FlowCalculus.lean:48
#check @RBM.Gauss.HighProbAt                                  -- Defs/StochDomAt.lean:82
#check @RBM.StochDomAt                                        -- Defs/StochDomAt.lean:61
#check @RBM.Gauss.etaT                                        -- Loop/GLoop.lean:75

noncomputable section

namespace RBM.Univ.GUEPhase.T2330Check

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

variable {d : ℕ} (sz : Sizes d)

/-! ## 2. Definitions (copied verbatim into `RBM.Univ.GUEPhase.BoundsACheck`) and target statements -/

/-- `HC` (RBM2D `BoundsA.lean:596`): the pathwise form of the conclusion of `gueGrid_entry_bound`. -/
def HC (E t1 t0 : ℕ → ℝ) (n0 : ℕ) (τU τ₁ : ℝ) (n : ℕ) (ω : PathΩ sz) : Prop :=
  ∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
    {ω' : PathΩ sz | ∀ a b : Idx d (sz.L n) (sz.W n),
        ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω')
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) a b‖ ≤
        gueDelta sz τU n}.indicator
      (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω')
            (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ^ 2) ω ≤
      ((sz.size n : ℕ) : ℝ) ^ τ₁ *
        (gueLmax sz E t1 t0 (gueGridK sz n0) n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)

/-- `Concl` (RBM2D `BoundsA.lean:611`): the two fields of `GUEPathBounds` unfolded at `(n, ω, τ)`. -/
abbrev Concl (E t1 t0 : ℕ → ℝ) (n0 : ℕ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (τ : ℝ) (n : ℕ) (ω : PathΩ sz) : Prop :=
  (∀ m : ℕ, 1 ≤ m → m ≤ n0 → ∀ (k : Fin (gueGridK sz n0 n + 1)) (σ : Fin m → Bool)
      (a : Fin m → Zd d (sz.L n)),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n k ω))
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf σ a) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf σ a)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ m) ∧
    (∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
      ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω)
          (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ ((1 : ℝ) / 2))

/-- `Bounds_path` (RBM2D `:416`), namespace `RBM.Univ.GUEPhase`. -/
def T2330_Bounds_path : Prop :=
  ∀ {τU : ℝ} (n0 : ℕ), 2 ≤ n0 → ∀ {E t1 t0 : ℕ → ℝ}
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n : ℕ), 0 < τU →
    |E n| < 2 → 0 ≤ t1 n → t1 n ≤ t0 n → t0 n < 1 → ∀ {τ τ₁ : ℝ}, 0 < τ₁ → τ₁ < τ →
    (∀ t ∈ Set.Icc (t1 n) (t0 n), (gueScale sz E n t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU)) →
    ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1 →
    ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁ - τU / 2) ≤ 1 / 32 →
    2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - τ₁) →
    ∀ ω : PathΩ sz,
    (∀ u : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0),
      gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n u.2 u.1 ω ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^ ((u.2 : ℕ) - 1)) →
    (∀ u : TimeIcc t1 t0 n × Set.Icc 1 n0,
      gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n u.2 u.1 ω ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^ (u.2 : ℕ)) →
    HC sz E t1 t0 n0 τU τ₁ n ω →
    (∀ i j : Idx d (sz.L n) (sz.W n),
      ‖(green (gueH sz t1 t0 (gueGridK sz n0) n 0 ω) (zt (E n) (t1 n)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) →
    (∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n → ∀ i j : Idx d (sz.L n) (sz.W n),
      ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)) →
    Concl sz E t1 t0 n0 Kt τ n ω

/-- `highProbAt_HC` (RBM2D `:633`), namespace `RBM.Univ.GUEPhase.BoundsACheck`. -/
def T2330_highProbAt_HC : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (n0 : ℕ) {τ₁ : ℝ} (τU : ℝ), 0 < τ₁ →
    StochDomAt (Pgue sz) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω =>
        {ω' : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
            ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω')
                (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤
            gueDelta sz τU n}.indicator
          (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω')
                (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) -
              mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
                p.2.1 p.2.2‖ ^ 2) ω)
      (fun n p ω => gueLmax sz E t1 t0 (gueGridK sz n0) n 2 p.1 ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) →
    HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | HC sz E t1 t0 n0 τU τ₁ n ω})

/-- `highProbAt_hA` (RBM2D `:653`). -/
def T2330_highProbAt_hA : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (n0 : ℕ) {τ₁ : ℝ} (τU : ℝ), 0 < τ₁ →
    StochDomAt (Pgue sz) sz.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0)) ω =>
        gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n p.2 p.1 ω)
      (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaT (E n) p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) →
    HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz |
      ∀ u : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0),
        gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n u.2 u.1 ω ≤
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^ ((u.2 : ℕ) - 1)})

/-- `highProbAt_hB` (RBM2D `:665`). -/
def T2330_highProbAt_hB : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (n0 : ℕ) {τ₁ : ℝ} (τU : ℝ), 0 < τ₁ →
    ∀ (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ),
    StochDomAt (Pgue sz) sz.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 1 n0) ω =>
        gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n p.2 p.1 ω)
      (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaT (E n) p.1)⁻¹ ^ (p.2 : ℕ)) →
    HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz |
      ∀ u : TimeIcc t1 t0 n × Set.Icc 1 n0,
        gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n u.2 u.1 ω ≤
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^ (u.2 : ℕ)})

/-- `highProbAt_hD` (RBM2D `:678`). -/
def T2330_highProbAt_hD : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (n0 : ℕ) {τ₁ : ℝ}, 0 < τ₁ →
    StochDomAt (Pgue sz) sz.size
      (fun n (ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ω =>
        ‖(green (gueH sz t1 t0 (gueGridK sz n0) n 0 ω) (zt (E n) (t1 n)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))
            ij.1 ij.2‖)
      (fun n _ _ => (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) →
    HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
      ‖(green (gueH sz t1 t0 (gueGridK sz n0) n 0 ω) (zt (E n) (t1 n)) -
          mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)})

/-- `highProbAt_hF` (RBM2D `:694`). -/
def T2330_highProbAt_hF : Prop :=
  ∀ (n0 : ℕ), Tendsto (fun n => sz.size n) atTop atTop →
    HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n →
      ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)})

/-- `pathBounds_of_forall_highProbAt` (RBM2D `:704`). -/
def T2330_pathBounds_of_forall_highProbAt : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (n0 : ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ),
    (∀ τ : ℝ, 0 < τ → HighProbAt (Pgue sz) sz.size
      (fun n => {ω : PathΩ sz | Concl sz E t1 t0 n0 Kt τ n ω})) →
    GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt

example : Prop := T2330_Bounds_path sz
example : Prop := T2330_pathBounds_of_forall_highProbAt sz

end RBM.Univ.GUEPhase.T2330Check

end
