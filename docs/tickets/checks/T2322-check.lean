/-
Release check for T2322 (dispatcher V1, Thu Oct  8 03:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §134, §91 (1), §54).
UN-31a (bulk universality, GUE phase, process layer, first cut): `RBM3D/Universality/GUEPhase/Proc.lean`, port of RBM2D
`Universality/GUEPhase/Proc.lean:1-860` (definitions, interpolation helpers, structural facts, loop-maximum facts, the
`𝓔^{(G̃)}` bound, the one-step entry deviation); `:862-1424` (`gueKproc_detDom`) is T2323 (UN-31b).
Section 1: merged names (exact namespaces; file:line on `main` 8f90d6d).
Section 2: the definitions, copied verbatim by T2322 into namespace `RBM.Univ.GUEPhase` (renaming rules of
`Induction/LoopGenN.lean:15-20` and of the merged `GUEPhase/Grid.lean`: `d : Sizes` ↦ `sz : Sizes d`, `PathΩ d` ↦ `PathΩ sz`,
`Idx (d.L n) (d.W n)` ↦ `Idx d (sz.L n) (sz.W n)`, `Z2 L` ↦ `Zd d L`, `spectralZ` ↦ `zt`, `spectralM` ↦ `mE`, `gloop L W` ↦
`loopL d L W`, `blockMat M` ↦ `blockMat d L W M`, `RBM.Ind.loopMax L W` ↦ `RBM.Ind.loopMax d L W`).
Section 3: three target statements as `Prop`s (T2322 proves them with these texts).
Statements, definitions and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2322-check.lean`.
-/
import RBM3D.Universality.GUEPhase.Grid
import RBM3D.Universality.GUEPhase.Bootstrap
import RBM3D.Universality.GUEPhase.Generator
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.GUEPhase.EntryDet
import RBM3D.Induction.Split
import RBM3D.Induction.ConArgDet
import RBM3D.Path.Stop

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- UN-27 Grid (T2316, d133012), namespace `RBM.Univ.GUEPhase`
#check @RBM.Univ.GUEPhase.gueH                  -- Grid.lean:77
#check @RBM.Univ.GUEPhase.gueScale              -- :84
#check @RBM.Univ.GUEPhase.gueGridK              -- :106
#check @RBM.Univ.GUEPhase.gueGridK_ne_zero      -- :108
#check @RBM.Univ.GUEPhase.gueH_isHermitian      -- :164
#check @RBM.Univ.GUEPhase.Pgue                  -- :61
#check @RBM.Univ.GUEPhase.GUEPathBounds
-- UN-26 Bootstrap, UN-28 Generator, UN-30 EntryDet
#check @RBM.Univ.GUEPhase.SBgue                 -- Bootstrap.lean:54
#check @RBM.Univ.GUEPhase.SBgue_apply           -- :56
#check @RBM.Univ.GUEPhase.ellT_eq_L             -- :148
#check @RBM.Univ.GUEPhase.primRhsGUE            -- :178
#check @RBM.Univ.GUEPhase.eq736                 -- :442
#check @RBM.Univ.GUEPhase.eventually_small      -- :481
#check @RBM.Univ.GUEPhase.egtNGUE               -- Generator.lean:97
#check @RBM.Univ.inv_N_le_maxLoopPM             -- EntryDet.lean:354
-- path, stopping, grid (`RBM.Path`)
#check @RBM.Path.PathΩ                          -- Path/Walk.lean:54
#check @RBM.Path.gridStep                       -- :67
#check @RBM.Path.gridTime                       -- :70
#check @RBM.Path.gridTime_last                  -- :160
#check @RBM.Path.firstHit                       -- Path/Stop.lean:42
#check @RBM.Path.TimeIcc                        -- Defs/StochDomAt.lean:100
-- loops, model, semicircle
#check @RBM.Ind.loopMax                         -- Induction/Split.lean:515
#check @RBM.Ind.loopMax_nonneg                  -- :538
#check @RBM.Ind.norm_gloop_le_loopMax           -- :520
#check @RBM.Ind.loopMax_two_mul_add_le          -- :582
#check @RBM.Ind.loopMax_odd_sq_le               -- :598
#check @RBM.Ind.norm_apply_le_l2_opNorm         -- :670
#check @RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero  -- Induction/ConArgDet.lean:380
#check @RBM.Gauss.loopL                         -- Loop/GLoopFlow.lean:123
#check @RBM.Gauss.blockMat                      -- :105
#check @RBM.Gauss.loopOf                        -- :117
#check @RBM.Gauss.gloop                         -- Loop/GLoop.lean:97
#check @RBM.Gauss.etaT                          -- Loop/GLoop.lean:75
#check @RBM.Gauss.etaT_pos                      -- :83
#check @RBM.Gauss.Sizes.seqXmat                 -- Gauss/FineModel.lean:218
#check @RBM.Gauss.Sizes.size                    -- Defs/Sizes.lean:157
#check @RBM.Gauss.Idx                           -- Defs/Sizes.lean:46
#check @RBM.Gauss.Vtx                           -- Gauss/Model.lean:60
#check @RBM.Zd                                  -- Defs/Lattice.lean:63
#check @RBM.Loop.LoopIdx                        -- Loop/TreeRep.lean:56
#check @RBM.Loop.LoopIdx.cutGlue                -- Loop/GLoopFlow.lean:317
#check @RBM.green                               -- Green/EntryCore.lean:34
#check @RBM.Green.GoodEvent                     -- Green/EntryCore.lean:406
#check @RBM.Green.greenBlk                      -- Green/Pins.lean:83
#check @RBM.Green.avgErr                        -- Green/Pins.lean:89
#check @RBM.Green.maxLoopPM                     -- Green/Pins.lean:94
#check @RBM.Green.maxLoopPM_nonneg              -- Green/Pins.lean:1209
#check @RBM.zt                                  -- Defs/Semicircle.lean:179
#check @RBM.mE                                  -- Defs/Semicircle.lean:38
#check @RBM.Gauss.norm_spectralM                -- Gauss/FlowCalculus.lean:96
#check @RBM.Gauss.spectralM_im_pos              -- :48
#check @RBM.Gauss.spectralZ_im                  -- :51
#check @RBM.eventually_le_rpow                  -- Defs/Domination.lean:68

noncomputable section

namespace RBM.Univ.GUEPhase.T2322Check

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ RBM.Univ.GUEPhase

variable {d : ℕ} (sz : Sizes d)

/-! ## 2. Definitions (copied verbatim into `RBM.Univ.GUEPhase`) -/

/-- The a priori threshold `δ_n = N^{-τU/4}`, `N = sz.size n`. -/
def gueDelta (τU : ℝ) (n : ℕ) : ℝ := ((sz.size n : ℕ) : ℝ) ^ (-(τU / 4))

/-- The tent function at the grid time `u_k`. -/
def gueTent (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (t : ℝ) : ℝ :=
  max 0 (1 - |t - gridTime t1 t0 K n k| / gridStep t1 t0 K n)

/-- Piecewise-linear interpolation of grid values (`f 0` if `Δ = 0`). -/
def gueInterp (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  if gridStep t1 t0 K n = 0 then f 0
  else ∑ k ∈ Finset.range (K n + 1), f k * gueTent t1 t0 K n k t

/-- `max_{i,j} |(G_k - m)_{ij}|` at the grid step `k`. -/
def gueDev (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) : ℝ :=
  ⨆ ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
    ‖(green (gueH sz t1 t0 K n k ω) (zt (E n) (gridTime t1 t0 K n k)) -
        mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) ij.1 ij.2‖

/-- The freezing index: the first grid step with `gueDev ≥ δ_n` (else `K n`). -/
def gueStop (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n : ℕ) (ω : PathΩ sz) : ℕ :=
  firstHit (fun k ω' => gueDev sz E t1 t0 K n k ω') (δ n) (K n) ω

/-- `L^{(m)}_k = max_{σ,a} |L_{σ,a}|` at the grid step `k`. -/
def gueLmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n m k : ℕ) (ω : PathΩ sz) : ℝ :=
  RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
    (zt (E n) (gridTime t1 t0 K n k)) m

/-- `D^{(m)}_k = max_{x} |L_x - K̃_x|` at the grid step `k`. -/
def gueDmax (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m k : ℕ) (ω : PathΩ sz) : ℝ :=
  ⨆ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
        (zt (E n) (gridTime t1 t0 K n k)) (loopOf x.1 x.2) -
      Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2)‖

/-- `K̄^{(m)}_k = max_{j ≤ k} max_x |K̃(u_j, x)|`, the deterministic running maximum. -/
def gueKbar (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m k : ℕ) : ℝ :=
  ⨆ j : Fin (k + 1), ⨆ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
    ‖Kt n (gridTime t1 t0 K n j) (loopOf x.1 x.2)‖

/-- The stopped, interpolated `Lm` fed to `eq727GEAt`/`eq728GAt`. -/
def gueLproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz) : ℝ :=
  gueInterp t1 t0 K n (fun k => gueLmax sz E t1 t0 K n m (min k (gueStop sz E t1 t0 K δ n ω)) ω) t

/-- The stopped, interpolated `Dm` fed to `eq727GEAt`/`eq728GAt`. -/
def gueDproc (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz) : ℝ :=
  gueInterp t1 t0 K n
    (fun k => gueDmax sz E t1 t0 K Kt n m (min k (gueStop sz E t1 t0 K δ n ω)) ω) t

/-- The deterministic `Km` fed to `eq727GEAt`. -/
def gueKproc (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (n m : ℕ) (t : ℝ) : ℝ :=
  gueInterp t1 t0 K n (fun k => gueKbar sz t1 t0 K Kt n m k) t

/-! ## 3. Target statements -/

/-- `gueLproc_nonneg` (RBM2D `Proc.lean:382`). -/
def T2322_gueLproc_nonneg : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m : ℕ) (t : ℝ) (ω : PathΩ sz),
    0 ≤ gueLproc sz E t1 t0 K δ n m t ω

/-- `gueLproc_time` (RBM2D `:446`). -/
def T2322_gueLproc_time : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m k : ℕ), t1 n ≤ t0 n → k ≤ K n → ∀ ω : PathΩ sz,
    gueLproc sz E t1 t0 K δ n m (gridTime t1 t0 K n k) ω =
      gueLmax sz E t1 t0 K n m (min k (gueStop sz E t1 t0 K δ n ω)) ω

/-- `gueDev_succ_le` (RBM2D `:723`): the one-step jump of the entry deviation (resolvent identity). -/
def T2322_gueDev_succ_le : Prop :=
  ∀ (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), |E n| < 2 → t1 n ≤ t0 n → t0 n < 1 → k < K n →
    ∀ ω : PathΩ sz,
      gueDev sz E t1 t0 K n (k + 1) ω ≤ gueDev sz E t1 t0 K n k ω +
        (etaT (E n) (t0 n))⁻¹ ^ 2 * (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) *
          ∑ i : Idx d (sz.L n) (sz.W n), ∑ j : Idx d (sz.L n) (sz.W n),
            ‖Sizes.seqXmat sz n (ω (k + 1)) i j‖ + gridStep t1 t0 K n)

example : Prop := T2322_gueLproc_nonneg sz ∧ T2322_gueLproc_time sz ∧ T2322_gueDev_succ_le sz

end RBM.Univ.GUEPhase.T2322Check

end
