/-
Release check for T2517 (dispatcher V4, 2026-10-15; DECISIONS §339; supervisor 2026-10-15-0643
MNO-C4 `:88`, route note `:91`; 2049 GMN-C2 (b) `:76-90`; 1457 UBA-C1 `:68-82`; 0349 U5S-C3 `:106-111`; 1152 X1-C4 `:100`).
BA stage M/N row C4 (T2449 §5 `:135`; T2173 pm `:276`): Lemma 5.15 on the GUE-phase grid at block Anderson (stability of
`1 - M^{(+,+)} Ŝ`, matrix `M`), the GUE drift at `ztOf` on the BA path, the BA twin of `Eq729A`, `eq729_Kdisc` at the BA primitive.
Part 1: merged names (`main` b2326aac; `file:line` relative to `RBM3D/`; private band helpers in comments only).
Part 2: the D1 proposals as `Prop` values (prefix `T2517_`): binding after the 1a-audit.  The BA grid path `gueHBA` (target 1)
is written inline: `((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n k ω`, `ω : PathΩ (sz.withLam 0)`.
Unmerged C3 row a names (`kTwoGUEBA`, `kTwoGUELoopBA`, `hasDerivAt_kTwoGUELoopBA`: T2515 target 7, text `T2515-prove.md:23`
(iv)) appear in prose only (target 8); C4 reads none of the `T2515_*` pins of `T2515-check.lean:115-173`.
Statements only; no proofs; not compiled by the dispatcher.
Run: lake env lean docs/tickets/checks/T2517-check.lean
-/
import RBM3D.Universality.GUEPhase.Eq729B
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Chain.ExpAvgGen
import RBM3D.BA.GreenStab
import RBM3D.BA.EKNonzero
import RBM3D.BA.EMn2BA
import RBM3D.BA.KCactus
import RBM3D.BA.FlowPins
import RBM3D.BA.UNPins

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 1: merged names -/

-- the band twins (UN-44/45/46, T2350/T2353; UN-34/35 Drift, T2343) and the consumer (UN-47, C5's twin)
#check @RBM.Univ.GUEPhase.gueGrid_expect_oneLoop   -- Universality/GUEPhase/OneLoop:1308 (private: `OneLoop_contraction` :484,
                                                   --   `OneLoop_stein` :621, `OneLoop_selfcons` :700, `OneLoop_stable` :857)
#check @RBM.Univ.GUEPhase.ol_gueH_eq               -- OneLoop:125 (one-time law of grid step `k`)
#check @RBM.Univ.GUEPhase.olVar                    -- OneLoop:101
#check @RBM.Univ.GUEPhase.eq729_primBil2           -- Universality/GUEPhase/Eq729A:52 (model-free)
#check @RBM.Univ.GUEPhase.eq729_eG2                -- Eq729A:80 (reads `mSigma`: twin with `mSigOf`)
#check @RBM.Univ.GUEPhase.eq729_norm_primRhs2_le   -- Eq729A:555
#check @RBM.Univ.GUEPhase.eq729_Kdisc              -- Eq729A:562 (generic in `Kf`; target 8 instantiates it)
#check @RBM.Univ.GUEPhase.eq729_duhamel            -- Eq729A:378
#check @RBM.Univ.GUEPhase.eq729F                   -- Eq729A:275
#check @RBM.Univ.GUEPhase.eq729e                   -- Eq729A:717
#check @RBM.Univ.GUEPhase.eq729c                   -- Eq729A:723 (`d`-free constant, read by name)
#check @RBM.Univ.GUEPhase.eq729_one_step           -- Eq729A:731
#check @RBM.Univ.GUEPhase.gueGrid_eq729            -- Universality/GUEPhase/Eq729B:622 (consumer; its BA twin is C5's)
#check @RBM.Univ.GUEPhase.oneStepEnvelopeGUE       -- Universality/GUEPhase/Drift:756 (band: `zt E`, `|E| < 2`)
#check @RBM.Univ.GUEPhase.condExp_loop_step_gue    -- Drift:1208
#check @RBM.Univ.GUEPhase.condExp_loop_drift_gue   -- Drift:1318 (also read by `DuhamelA2:1075`, C5's route)
#check @RBM.Univ.GUEPhase.gueH_succ                -- Drift:925
#check @RBM.Path.envConst                          -- Path/OneStep:78 (reads `etaT E`)
-- the generic GUE-phase layer
#check @RBM.Univ.GUEPhase.Pgue                     -- Universality/GUEPhase/Grid:61 (step 0: `seqP`; BA: at `sz.withLam 0`)
#check @RBM.Univ.GUEPhase.gueH                     -- Grid:77
#check @RBM.Univ.GUEPhase.gueH_isHermitian         -- Grid:164
#check @RBM.Univ.GUEPhase.GUEPathBounds            -- Grid:89 (registry `Test/Axioms:388`, structural; BA producer C5)
#check @RBM.Univ.GUEPhase.mSigOf                   -- Universality/GUEPhase/Generator:62
#check @RBM.Univ.GUEPhase.genMatGUEOf              -- Generator:68
#check @RBM.Univ.GUEPhase.egtNGUEOf                -- Generator:79
#check @RBM.Univ.GUEPhase.loopGenGUEOf             -- Generator:1168 (any `m` with `0 < Im m`, any Hermitian `M`)
#check @RBM.Univ.GUEPhase.primRhsGUE               -- Universality/GUEPhase/Bootstrap:178
#check @RBM.Univ.GUEPhase.kTwoGUELoop              -- Universality/GUEPhase/KPrim:75 (band twin of C3's `kTwoGUELoopBA`)
#check @RBM.Univ.GUEPhase.hasDerivAt_kTwoGUELoop   -- KPrim:209
#check @RBM.Path.PathΩ                             -- Path/Walk:54
#check @RBM.Path.filt                              -- Path/Walk:62
#check @RBM.Path.gridTime                          -- Path/Walk:70
#check @RBM.Gauss.ztOf                             -- Loop/GLoopFlow:55
#check @RBM.Gauss.etaOf                            -- GLoopFlow:58
#check @RBM.Gauss.ztOf_im                          -- GLoopFlow:64
#check @RBM.Gauss.Mres                             -- GLoopFlow:81
#check @RBM.Gauss.PsiI                             -- Gauss/BlockAnderson:52
#check @RBM.Gauss.PsiI_isHermitian                 -- BlockAnderson:65
#check @RBM.Gauss.Iblk                             -- Defs/Sizes:92
#check @RBM.Gauss.Sizes.withLam                    -- Defs/Sizes:182
#check @RBM.Univ.ouP_ba_eq_band                    -- BA/UNPins:467 (BA carrier law = band law at `withLam 0`)
-- the matrix-`M` one-loop at the chain level (T2502 c, V1s1; BA bridge T2510)
#check @RBM.BA.ExpAvgGen_tM                        -- Chain/ExpAvgGen:72 (`t_{aq}`; private `ExpAvgGen_stein_trace` :348,
                                                   --   `ExpAvgGen_selfcons_fixed` :470, `ExpAvgGen_ward` :604)
#check @RBM.BA.ExpAvgGen_W1iii                     -- ExpAvgGen:81 (the chain form of `hoff`)
#check @RBM.BA.stImproveCoregL_of                  -- ExpAvgGen:1365
-- BA inputs (all merged; none is a V output)
#check @RBM.BA.BASelf                              -- BA/MFixedPoint:193
#check @RBM.BA.BAMB                                -- MFixedPoint:190
#check @RBM.BA.BAMss                               -- MFixedPoint:511
#check @RBM.BA.BAReal                              -- MFixedPoint:432
#check @RBM.BA.BAzztE_data                         -- MFixedPoint:297 (C5's bridge from `z` to the flow point)
#check @RBM.BA.BAStab                              -- BA/GreenCore:1268
#check @RBM.BA.baStab_of_real                      -- BA/GreenStab:46 (`K = 16 κ⁻⁴`)
#check @RBM.BA.baM_row_l1                          -- GreenStab:116
#check @RBM.BA.baTheta_weighted_l1                 -- GreenStab:251
#check @RBM.BA.BAoffDiag_of_real                   -- BA/Ward:289 (`ε = κ²/4`)
#check @RBM.BA.BAMB_diag_eq                        -- Ward:89
#check @RBM.BA.BAMB_symm                           -- Ward:83
#check @RBM.BA.BAMB_row_sq_real                    -- Ward:125
#check @RBM.BA.BAm_norm_le_one                     -- Ward:136
#check @RBM.BA.BAMss_ss_diag                       -- BA/Prop5Short:110
#check @RBM.BA.BAMss_row_offdiag_sum               -- Prop5Short:121
#check @RBM.BA.EKNonzero_Mss_shift                 -- BA/EKNonzero:110
#check @RBM.BA.EMn2BA_SB_zero                      -- BA/EMn2BA:77 (`SB d L 0 = 1`)
#check @RBM.BA.BAMfine                             -- BA/FlowPins:255 (alternative flow vocabulary, D1 (iii))
#check @RBM.BA.BAGamma                             -- BA/KCactus:488 (K4; read by C5, not by C4)

/-! ## Part 2: D1 proposals (prefix `T2517_`; NOT binding until the 1a-audit) -/

namespace RBM.BA.T2517Check

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase RBM.BA

/-- **Row 1, the zero-mode gap** (replaces `gapK κ ≤ |1 - u m²|`): at real-axis data, every row sum `r_a = Σ_b M_{ab}²`
satisfies `κ⁴/16 ≤ |1 - u r_a|` for `0 ≤ u ≤ 1` (`BAMss_ss_diag`, `BAMss_row_offdiag_sum`, `BAoffDiag_of_real` at `t = u`). -/
def T2517_GapBA : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a : Zd d L,
      κ ^ 4 / 16 ≤ ‖1 - (u : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b‖

/-- **Target 2, block stability of `1 - M^{(+,+)} Ŝ`** (twin of the private `OneLoop_stable`, `OneLoop:857`), `Ŝ = t₁ 1 + σ J`
(`S^{(B)}(0) = 1`), `u = t₁ + L^d σ ≤ 1`: uniform in `L`, `g`, `t₁`, `σ`.  Route: the average through `T2517_GapBA` (row sums
constant by `EKNonzero_Mss_shift`), the rest by `baStab_of_real` at `t = t₁`; expected `K = 16 κ⁻⁴ (1 + 16 κ⁻⁴)`. -/
def T2517_StableBA : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, 0 < K ∧ ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ t1 σ : ℝ, 0 ≤ t1 → 0 ≤ σ → t1 + (L : ℝ) ^ d * σ ≤ 1 →
      ∀ (x y : Zd d L → ℂ) (B : ℝ), (∀ a, ‖y a‖ ≤ B) →
        (∀ a, x a = ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b *
          ((t1 : ℂ) * x b + (σ : ℂ) * ∑ c, x c) + y a) →
        ∀ a, ‖x a‖ ≤ K * B

/-- **Target 4, Lemma 5.15 on the GUE-phase grid at BA** (twin of `gueGrid_expect_oneLoop`, `OneLoop:1308`): flow data
`(g, E, m)` (`g` = flow-point coupling `λ₀`), `M = (gΨ - E - m)⁻¹` (`BAMB`; fine `Mres (gΨ_I) E m`), path `gueHBA`,
`z_u = ztOf m E u`, `η_u = etaOf m u`.  Inputs: `h1` (diagonal 1-loop, band form) and **`hoff` (D1 (i))**: the `M`-weighted
block traces `t_{aq}` (`ExpAvgGen_tM`) against `M^{(++)}_{aq}` at `|M_{aq}| (N η_u)^{-1}` (the GUE-grid form of `ExpAvgGen_W1iii`).
Producer of `h1`, `hoff`: C5.  `0 < g n ≤ Λ` is for `baM_row_l1` only; the stability constant is `L`-, `g`-free. -/
def T2517_OneLoopBA (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ Λ : ℝ), 0 < κ → 0 < Λ →
    ∀ (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ),
    Tendsto (fun n => sz.size n) atTop atTop →
    (∀ n, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
    (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) → (∀ n, K n ≠ 0) →
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (K n + 1) × Zd d (sz.L n)) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
            (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n p.1 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ - m n‖)
      (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹) →
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ω =>
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) p.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p.2.2,
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
              Gres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n p.1 ω)
                (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) true y x -
          BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true p.2.1 p.2.2‖)
      (fun n p _ => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) p.2.1 p.2.2‖ *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹) →
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (K n + 1) × Zd d (sz.L n),
      ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
            (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n p.1 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹ ^ 2

/-- **Target 6, D1 (ii): the conditional drift at `ztOf` on the BA path** (twin of `condExp_loop_drift_gue`, `Drift:1318`;
`|E| < 2` ↦ `0 < Im m`, `‖m‖ ≤ 1`; `envConst` inline with `etaOf`).  Consumers: row b (`eq729_duhamelBA`), C5 (DuhamelA2 twin). -/
def T2517_DriftBA : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (m : ℂ), 0 < m.im → ‖m‖ ≤ 1 →
    ∀ {I : LoopIdx (Zd d (sz.L n))}, I.WF → 0 ≤ t1 n → t1 n ≤ t0 n → K n ≠ 0 → k < K n →
      gridTime t1 t0 K n (k + 1) < 1 →
      ∀ᵐ ω ∂(Pgue (sz.withLam 0)),
        ‖(Pgue (sz.withLam 0))[fun ω' : PathΩ (sz.withLam 0) =>
              loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
                (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n (k + 1) ω'))
                (ztOf m E (gridTime t1 t0 K n (k + 1))) I | filt (sz.withLam 0) k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
              (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n k ω))
              (ztOf m E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n k)
              (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n k ω) I‖
        ≤ 16 * ((I.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (etaOf m (gridTime t1 t0 K n (k + 1)))⁻¹) ^ (I.length + 4) * gridStep t1 t0 K n ^ ((3 : ℝ) / 2)

/-- **Target 7, one step of `e_k` at BA** (twin of `eq729_one_step`, `Eq729A:731`, substitution table D1 (iii)); `F`, `e` are the
bodies of `eq729FBA`, `eq729eBA`.  Consumer: C5's twin of `gueGrid_eq729` (`Eq729B:622`); `Kt` stays a parameter. -/
def T2517_OneStepBA : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 E : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n : ℕ)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ),
    let F : ℕ → PathΩ (sz.withLam 0) → LoopIdx (Zd d (sz.L n)) → ℂ := fun k ω I =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
        (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + gueH (sz.withLam 0) t1 t0 K n k ω))
        (ztOf (m n) (E n) (gridTime t1 t0 K n k)) I
    let e : ℕ → LoopIdx (Zd d (sz.L n)) → ℂ := fun k I =>
      (∫ ω, F k ω I ∂(Pgue (sz.withLam 0))) - Kt n (gridTime t1 t0 K n k) I
    0 < (m n).im → ‖m n‖ ≤ 1 → 0 ≤ t1 n → t1 n ≤ t0 n → t0 n < 1 →
    ∀ {Λ ρ p Bk : ℝ}, Λ = (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ → Λ ≤ 1 → 0 ≤ ρ → ρ * Λ ≤ 1 → 0 ≤ p →
    ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1 →
    (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ) →
    (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w, ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2) →
    (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
      (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩) (Set.Icc (t1 n) (t0 n)) s) →
    ∀ {k : ℕ}, k < K n →
    (∀ a, ‖(∫ ω, F k ω ⟨[true], [a]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤ ρ * Λ ^ 2) →
    ∀ {B : Set (PathΩ (sz.withLam 0))}, Pgue (sz.withLam 0) B ≤ ENNReal.ofReal p →
    (∀ ω ∉ B, ∀ σ a, ‖F k ω ⟨[σ], [a]⟩ - mSigOf (m n) σ‖ ≤ ρ * Λ) →
    (∀ ω ∉ B, ∀ s1 s2 x y, ‖F k ω ⟨[s1, s2], [x, y]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2) →
    (∀ ω ∉ B, ∀ s1 s2 s3 x y w,
      ‖F k ω ⟨[s1, s2, s3], [x, y, w]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3) →
    (∀ s1 s2 x y, ‖e k ⟨[s1, s2], [x, y]⟩‖ ≤ Bk) →
    ∀ (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)),
      ‖e (k + 1) ⟨[s1, s2], [a1, a2]⟩‖ ≤
        (1 + gridStep t1 t0 K n * (2 * ((sz.size n : ℕ) : ℝ) * (ρ * Λ))) * Bk +
          eq729c ((sz.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n)

end RBM.BA.T2517Check
