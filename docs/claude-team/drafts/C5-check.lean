/-
Release check for T2519 (DRAFT; dispatcher V4 drafting helper, 2026-10-15; DECISIONS §343; supervisor 2026-10-15-0643
MNO-C4 `:88`, route note `:91`; 2049 GMN-C3 `:91-96`; 0658 UP-C2 `:201-210`; 0349 U5S-C3 `:106-111`; 1457 UBA-C1; 1152 X1-C4).
BA stage M/N row C5 (T2449 §5 `:136`; T2173 pm `:277`, `:288`): the BA §7.2 random layer on the GUE-phase grid and the BA
producers of `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` at `UNKind.ba` (vocabulary `BAKFam`, `BAPB`, `GUEPathBoundsBA`), the
`hoff` producer, `baEq729_Kdisc`.
Part 1: merged names (`main` 13b68cea; `file:line` relative to `RBM3D/`).
Part 2: proposals as `Prop` values over merged names only (prefix `T2519_`): binding after the 1a-audit.
Part 3: proposals that need unmerged names, in block comments `ACTIVATE AFTER …` (C4 row a `t/T2517` `BA/GUEOneLoop`;
C4 row b `t/T2517b` `BA/GUEEq729BA`, not started; C3 row b `t/T2515b` bfaef632 `BA/GUEEntry2`).
Statements only; no proofs; not compiled by the drafting helper.
Run: lake env lean docs/tickets/checks/T2519-check.lean
-/
import RBM3D.BA.GUEKPrim
import RBM3D.BA.KBound
import RBM3D.BA.KCactus
import RBM3D.BA.GreenStab
-- ACTIVATE AFTER T2517 row a (C4 a) MERGES: import RBM3D.BA.GUEOneLoop
-- ACTIVATE AFTER T2517 row b (C4 b) MERGES: import RBM3D.BA.GUEEq729BA
-- ACTIVATE AFTER T2515 row b (C3 b) MERGES: import RBM3D.BA.GUEEntry2

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 1: merged names -/

-- C5g (T2475): the generic successors and the BA vocabulary; the N2 reading is `BA/RandomLayerBGBA:199-212`
#check @RBM.Univ.GUEPhase.RBG_Prod                  -- Universality/GUEPhase/RandomLayerBG:72 (target of `ba_prodG`)

#check @RBM.Univ.GUEPhase.RBG_Que                   -- RandomLayerBG:87 (target of `ba_QueG`)

#check @RBM.Univ.GUEPhase.RandomLayerB_LL           -- Universality/GUEPhase/RandomLayerB:151 (target of `ba_LLG`, unprimed)

#check @RBM.Univ.GUEPhase.RBG_Flow                  -- RandomLayerBG:59

#check @RBM.Univ.GUEPhase.RBG_Dom                   -- RandomLayerBG:65

#check @RBM.Univ.GUEPhase.RBG_Comp                  -- RandomLayerBG:115

#check @RBM.Univ.GUEPhase.RBG_ProfComp              -- RandomLayerBG:123

#check @RBM.Univ.GUEPhase.g1Rowk_of_inputsG         -- RandomLayerBG:399 (N2 instantiates it at `UNKind.ba`)

#check @RBM.Univ.GUEPhase.RandomLayerB_MLout        -- RandomLayerB:123

#check @RBM.Univ.GUEPhase.RandomLayerB_LLAt         -- RandomLayerB:76

#check @RBM.Univ.GUEPhase.RandomLayerB_QueAt        -- RandomLayerB:83

#check @RBM.Univ.GUEPhase.RandomLayerB_KFam         -- RandomLayerB:63 (band twin of `BAKFam`)

#check @RBM.Univ.GUEPhase.RandomLayerB_PBband       -- RandomLayerB:346 (band twin of `BAPB`)

#check @RBM.Univ.GUEPhase.RandomLayerB_prod_band    -- RandomLayerB:400 (band twin of `ba_prodG`)

#check @RBM.Univ.GUEPhase.RandomLayerB_LL_band      -- RandomLayerB:427 (band twin of `ba_LLG`)

#check @RBM.Univ.GUEPhase.RandomLayerB_Que_band     -- RandomLayerB:439 (band twin of `ba_QueG`)

#check @RBM.BA.BAfT                                 -- BA/RandomLayerBGBA:49

#check @RBM.BA.BAfE                                 -- RandomLayerBGBA:52

#check @RBM.BA.BAEd                                 -- RandomLayerBGBA:56

#check @RBM.BA.BAMO                                 -- RandomLayerBGBA:61

#check @RBM.BA.ba_dom_of_bulk                       -- RandomLayerBGBA:69

#check @RBM.BA.ba_Ed_of_im                          -- RandomLayerBGBA:87

#check @RBM.BA.ba_flowG                             -- RandomLayerBGBA:92 (`RBG_Flow` at BA)

#check @RBM.BA.ba_domG                              -- RandomLayerBGBA:103 (`RBG_Dom` at BA)

#check @RBM.BA.ba_mlout                             -- RandomLayerBGBA:115

#check @RBM.BA.RandomLayerBGBA_comp                 -- RandomLayerBGBA:126

-- C3 row a (T2515, merged 13b68cea `BA/GUEKPrim`)
#check @RBM.Univ.UNOUProfile.ba                     -- BA/GUEKPrim:77

#check @RBM.BA.baProfComp                           -- GUEKPrim:604

#check @RBM.BA.baOUProfRowk_holds                   -- GUEKPrim:584

#check @RBM.BA.baT0Cmp                              -- GUEKPrim:135 (UBA-C1 comparison)

#check @RBM.BA.kTwoGUEBA                            -- GUEKPrim:634

#check @RBM.BA.kTwoGUELoopBA                        -- GUEKPrim:639

#check @RBM.BA.kTwoGUEBA_self                       -- GUEKPrim:646

#check @RBM.BA.kTwoGUEBA_eq_ThetaTilde              -- GUEKPrim:659

#check @RBM.BA.hasDerivAt_kTwoGUELoopBA             -- GUEKPrim:776 (`hKd` of target 8)

#check @RBM.BA.gueK_existsBA                        -- GUEKPrim:1015 (the `Kt` of `BAKFam`; needs `0 < g`)

#check @RBM.BA.kTwoGUEBA_bridge                     -- GUEKPrim:1071

#check @RBM.BA.kTwoGUEBA_bridge_pm                  -- GUEKPrim:1101 (`t₀ K = P.pm` for `RBG_Que`)

#check @RBM.BA.kTwoGUEBA_bridge_pp                  -- GUEKPrim:1111

-- the band twins (census of the ticket)
#check @RBM.Univ.GUEPhase.GUEPathBounds             -- Universality/GUEPhase/Grid:89 (registry `Test/Axioms:383`, structural)

#check @RBM.Univ.GUEPhase.gueGridK                  -- Grid:106

#check @RBM.Univ.GUEPhase.gueH                      -- Grid:77 (BA: at `sz.withLam 0` inside `gueHBA` only)

#check @RBM.Univ.GUEPhase.Pgue                      -- Grid:61 (BA: at `sz.withLam 0`)

#check @RBM.Univ.GUEPhase.gueDev                    -- Proc:83 (reads `mE (E n) • 1`)

#check @RBM.Univ.GUEPhase.gueStop                   -- Proc:89

#check @RBM.Univ.GUEPhase.gueLmax                   -- Proc:93

#check @RBM.Univ.GUEPhase.gueDmax                   -- Proc:98

#check @RBM.Univ.GUEPhase.gueLproc                  -- Proc:112

#check @RBM.Univ.GUEPhase.gueDproc                  -- Proc:116

#check @RBM.Univ.GUEPhase.gueKproc                  -- Proc:122 (no band token; read by name)

#check @RBM.Univ.GUEPhase.norm_egtNGUE_le           -- Proc:596

#check @RBM.Univ.GUEPhase.gueDev_succ_le            -- Proc:771

#check @RBM.Univ.GUEPhase.gueKproc_detDom           -- ProcK:553

#check @RBM.Univ.GUEPhase.Hyp_Kt_detDom             -- HypA:690

#check @RBM.Univ.GUEPhase.Hyp_Kt_one                -- HypA:712

#check @RBM.Univ.GUEPhase.Hyp_Kt_disc               -- HypA:864

#check @RBM.Univ.GUEPhase.Hyp_grid                  -- HypA:981

#check @RBM.Univ.GUEPhase.map_gueH_eq_mixMat        -- EntryGrid:118

#check @RBM.Univ.GUEPhase.gueGrid_entry_bound       -- EntryGrid:518 (UN-43; owner of the BA twin: C5, T2515 Decision (5))

#check @RBM.Univ.GUEPhase.Duhamel_drift_remainder_ae  -- DuhamelA2:1008 (reads `condExp_loop_drift_gue`)

#check @RBM.Univ.GUEPhase.Duhamel_step_decomp       -- DuhamelB:739

#check @RBM.Univ.GUEPhase.gueGrid_loop_duhamel      -- DuhamelC:1485

#check @RBM.Univ.GUEPhase.HypB_entry_le             -- HypB:131 (`‖G - m‖_max`: BA `‖G - M‖_max`)

#check @RBM.Univ.GUEPhase.HypB_fixed                -- HypB:783

#check @RBM.Univ.GUEPhase.Bounds_path               -- BoundsA:503

#check @RBM.Univ.GUEPhase.BoundsACheck.pathBounds_of_forall_highProbAt  -- BoundsA:751

#check @RBM.Univ.GUEPhase.gueBds_h745E              -- PathBounds:330

#check @RBM.Univ.GUEPhase.gueBds_h746               -- PathBounds:433

#check @RBM.Univ.GUEPhase.gueGrid_pathBounds        -- PathBounds:550

#check @RBM.Univ.GUEPhase.oull_of_pathBounds        -- LLTransfer:443

#check @RBM.Univ.GUEPhase.gueGrid_eq729             -- Eq729B:622 (`h1` from `hP.lk 1` :663-690; Lemma 5.15 :676)

#check @RBM.Univ.GUEPhase.Eq729B_eq747_of_eq729     -- Eq729B:1077

#check @RBM.Univ.GUEPhase.Eq729B_derived            -- Eq729B:1125

#check @RBM.Univ.GUEPhase.Eq729B_eq747_of_inputs    -- Eq729B:1221

#check @RBM.Univ.GUEPhase.Eq729B_Concl              -- Eq729B:104

#check @RBM.Univ.GUEPhase.eq729_Kdisc               -- Eq729A:562 (target 8 instantiates it)

#check @RBM.Univ.GUEPhase.gue_highProb_incr_le      -- Markov:863 (read at `sz.withLam 0`)

#check @RBM.Univ.GUEPhase.gueK_exists               -- KPrim:749 (band twin of `gueK_existsBA`)

#check @RBM.Univ.GUEPhase.primRhsGUE                -- Bootstrap:178

-- the generic `Of` layer and the BA flow data (all merged; none is a V output)
#check @RBM.Gauss.ztOf                              -- Loop/GLoopFlow:55

#check @RBM.Gauss.etaOf                             -- GLoopFlow:58

#check @RBM.Gauss.Mres                              -- GLoopFlow:81 (`M = M^{(B)} ⊗ 1` of the local law)

#check @RBM.Univ.GUEPhase.mSigOf                    -- Universality/GUEPhase/Generator:62

#check @RBM.Univ.GUEPhase.genMatGUEOf               -- Generator:68

#check @RBM.Univ.GUEPhase.egtNGUEOf                 -- Generator:79

#check @RBM.Univ.GUEPhase.loopGenGUEOf              -- Generator:1168

#check @RBM.Gauss.PsiI                              -- Gauss/BlockAnderson:52

#check @RBM.Gauss.Sizes.withLam                     -- Defs/Sizes:182

#check @RBM.BA.BAm                                  -- BA/MFixedPoint:379

#check @RBM.BA.BAm_spec                             -- MFixedPoint:441

#check @RBM.BA.BAReal                               -- MFixedPoint:432

#check @RBM.BA.BAMB                                 -- MFixedPoint:190

#check @RBM.BA.BAMss                                -- MFixedPoint:511

#check @RBM.BA.BAMsigma                             -- MFixedPoint:507

#check @RBM.BA.BAzztE_data                          -- MFixedPoint:297 (`etaOf` identity of the flow point)

#check @RBM.BA.BAdom_real                           -- MFixedPoint:479

#check @RBM.BA.BAmF                                 -- BA/FlowPins:252

#check @RBM.BA.BAflowLam0                           -- FlowPins:386

#check @RBM.BA.BAFlow                               -- FlowPins:389

#check @RBM.BA.baFMz                                -- FlowPins:393

#check @RBM.BA.BAKsol                               -- FlowPins:283

#check @RBM.BA.baKsol_two                           -- BA/KInduct:88

#check @RBM.BA.BAKbound                             -- BA/KBound:196 (under `BAFlow`: coverage row 12)

#check @RBM.BA.baKbound_holds                       -- KBound:245

#check @RBM.BA.BAGamma                              -- BA/KCactus:488

#check @RBM.BA.STKboundgL                           -- Chain/Carrier:147 (registry `Test/Axioms:134`)

#check @RBM.BA.STLKgL                               -- Carrier:80

#check @RBM.BA.STLocalEntrygL                       -- Carrier:121

#check @RBM.BA.STExp2gL                             -- Carrier:127

#check @RBM.BA.baTheta_weighted_l1                  -- BA/GreenStab:251 (`‖K̃₂‖ ≤ 1`, target 8)

#check @RBM.BA.baM_row_l1                           -- GreenStab:116 (row `ℓ¹` of `M`, D1 (i))

#check @RBM.BA.BAm_norm_le_one                      -- BA/Ward:136

#check @RBM.Univ.ouP_ba_eq_band                     -- BA/UNPins:467

#check @RBM.Univ.ouMatC_ba_eq_band_add              -- UNPins:445

#check @RBM.Univ.UNMLOutBA                          -- UNPins:110 (instances: a hypothesis, no V name)

-- registry Props C5 contributes to (owner comments only)
#check @RBM.Univ.UNOULLk                            -- Universality/OUInterfaceK:69 (registry `Test/Axioms:168`)

#check @RBM.Univ.UNG1Rowk                           -- OUInterfaceK:101 (registry `Test/Axioms:169`)

#check @RBM.Univ.UNOUQUEk                           -- Universality/PinsK:326 (registry `Test/Axioms:387`)

#check @RBM.Univ.UNOUProfRowk                       -- OUInterfaceK:56 (registry `Test/Axioms:386`, untouched)

/-! ## Part 2: proposals over merged names (prefix `T2519_`; NOT binding until the 1a-audit) -/

namespace RBM.BA.T2519Check

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase RBM.BA

/-- **Target 16a, `ba_prodG`**: `RBG_Prod` at the BA vocabulary of C5g for a primitive family `KF` and path bounds `PB`
(C5 instantiates `KF := T2519_KFamBA`, `PB := T2519_PBBA`, Part 3); text of `RandomLayerBGBA:204`. -/
def T2519_ProdBA (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RBG_Prod (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d)

/-- **Target 16b, `ba_LLG`**: the unprimed T3 at BA (`RandomLayerBGBA:205`). -/
def T2519_LLBA (PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RandomLayerB_LL (UNKind.ba d) (BAfE d) (BAfT d) (PB d)

/-- **Target 16c, `ba_QueG`**: `RBG_Que` at BA with the BA profile `UNOUProfile.ba` (`RandomLayerBGBA:206`). -/
def T2519_QueBA (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RBG_Que (UNKind.ba d) (UNOUProfile.ba d) (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d)

/-- **Target 1, `BAKFam`** (twin of `RandomLayerB_KFam`, `RandomLayerB:63`): at the flow point `g = √t₀ λ`,
`m = BAm d L g E'` (the real-axis solution), start `BAKsol` at `t₁`, the ODE `primRhsGUE` on `[t₁, t₀]` (`n₀ = 3`), 2-loops
`kTwoGUEBA`.  Every clause is guarded by `0 < g` (`gueK_existsBA` needs it; `Sizes.lam` has no sign: coverage row 14). -/
def T2519_KFamBA (d : ℕ) (sz : Sizes d) (E' t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I =
        BAKsol d (sz.L n) (sz.W n)
          (BAMsigma d (sz.L n) (BAMB d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)
            (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))))
          (PropSpin (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))) (t1 n) I) ∧
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * 3 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) ∧
  (∀ n, 0 < Real.sqrt (t0 n) * sz.lam n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ =
        kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt (t0 n) * sz.lam n) (E' n)
          (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (t1 n) s σ₁ σ₂ a b)

/-- `BAKFam` has the type of `KF` in the three RBG texts (exact-type check of D1 (ii)). -/
example : Prop :=
  ∀ PB : (∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    T2519_ProdBA T2519_KFamBA PB ∧ T2519_LLBA PB ∧ T2519_QueBA T2519_KFamBA PB

/-- The consumer (N2, `T2513_n2_three`; `RandomLayerBGBA:199-212`): the three C5 targets with the merged C5g/C3 pieces give
`UNG1Rowk` at `UNKind.ba` through `g1Rowk_of_inputsG` (a `Prop` here; N2 proves it in MN-D3's filtered form). -/
example : Prop :=
  ∀ KF PB : (∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    T2519_ProdBA KF PB → T2519_LLBA PB → T2519_QueBA KF PB →
      UNG1Rowk (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA

/-- **Coverage row 13, the margin datum gives the real-axis datum** (family premise of C4's texts): `BAEd κ'` at `z`
is `BAReal` at `(√t₀ λ, BAfE, BAm d L (√t₀ λ) BAfE)` (`BAm_spec`, `BASelf_unique`). -/
def T2519_EdRealBA : Prop :=
  ∀ (d : ℕ) (κ' : ℝ) (sz : Sizes d) (n : ℕ) (z : ℂ), BAEd d κ' sz n z →
    BAReal d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) κ' (BAfE d sz n z)
      (BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ))

/-- **Coverage row 13, the scale of the RBG texts is the flow scale**: `√fT Im z = etaOf m t₀` at the flow point
(`BAzztE_data`, `BAt0_mul`): the hypotheses `h730`, `hscale` of `RBG_Prod` are the `η_{t₀}` rows of the grid twins. -/
def T2519_FlowEtaBA : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im →
    etaOf (BAm d (sz.L n) (Real.sqrt (BAfT d sz n z) * sz.lam n) (BAfE d sz n z : ℂ)) (BAfT d sz n z) =
      Real.sqrt (BAfT d sz n z) * z.im

/-- **Target 15, `baEq729_Kdisc`** (T2517 target 8, moved to C5 by T2517 Decision (1)): `eq729_Kdisc` (`Eq729A:562`) at
`Kf = kTwoGUELoopBA … t₁` on real-axis data; `hKd` is `hasDerivAt_kTwoGUELoopBA` (`GUEKPrim:776`); `b₂ ≤ 1` stays a
premise (fed by `baTheta_weighted_l1` or by `Hyp_Kt_detDomBA`). -/
def T2519_KdiscBA : Prop :=
  ∀ (d L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ {t1 t0 u Δ b2 : ℝ}, 0 ≤ t1 → t0 < 1 → u ∈ Set.Icc t1 t0 → u + Δ ∈ Set.Icc t1 t0 → 0 ≤ Δ → b2 ≤ 1 →
      (((W * L) ^ d : ℕ) : ℝ) * Δ ≤ 1 →
      (∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, ‖kTwoGUELoopBA d L W g E m t1 s ⟨[s1, s2], [x, y]⟩‖ ≤ b2) →
      ∀ (s1 s2 : Bool) (a1 a2 : Zd d L),
        ‖kTwoGUELoopBA d L W g E m t1 u ⟨[s1, s2], [a1, a2]⟩ +
            (Δ : ℂ) * primRhsGUE d L W (kTwoGUELoopBA d L W g E m t1 u) ⟨[s1, s2], [a1, a2]⟩ -
          kTwoGUELoopBA d L W g E m t1 (u + Δ) ⟨[s1, s2], [a1, a2]⟩‖ ≤
          3 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2

/-! ## Part 3: proposals over unmerged names (block comments; activate with the import lines above) -/

/- ACTIVATE AFTER T2517 row a (C4 a, `t/T2517`) MERGES: `BA/GUEOneLoop` provides `gueHBA` (`:45`), `gueHBA_succ` (`:59`),
`ol_gueHBA_eq` (`:72`), `gueGrid_expect_oneLoopBA` (C4 target 4 = `T2517_OneLoopBA`, `T2517-1a-audit` §2).

#check @RBM.BA.gueHBA

#check @RBM.BA.gueHBA_succ

#check @RBM.BA.ol_gueHBA_eq

#check @RBM.BA.gueGrid_expect_oneLoopBA

/-- **Target 1, `GUEPathBoundsBA`** (twin of `GUEPathBounds`, `Grid:89`): the path `gueHBA`, the flow `ztOf (m n) (E n)`,
the scale `N etaOf (m n) u`; the local law is against `Mres (g Ψ_I) E m = M^{(B)} ⊗ 1` (not `m • 1`).  No twist field:
`hoff` is target 7, a consequence at each grid time (D1 (i)). -/
def T2519_PathBoundsBA {d : ℕ} (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n0 : ℕ)
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

/-- **Target 1, `BAPB`** (twin of `RandomLayerB_PBband`, `RandomLayerB:346`): `GUEPathBoundsBA` at the flow point of the
RBG texts, `g = √t₀ λ`, `m = BAm d L g E'`, grid `gueGridK sz 3`, `n₀ = 3`. -/
def T2519_PBBA (d : ℕ) (sz : Sizes d) (E' t1 t0 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) : Prop :=
  T2519_PathBoundsBA sz (fun n => Real.sqrt (t0 n) * sz.lam n) E' t1 t0
    (fun n => BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (gueGridK sz 3) 3 Kt

/-- **Target 16 at C5's vocabulary** (the statements of `ba_prodG`, `ba_LLG`, `ba_QueG`). -/
def T2519_ProducersBA : Prop :=
  T2519_ProdBA T2519_KFamBA T2519_PBBA ∧ T2519_LLBA T2519_PBBA ∧ T2519_QueBA T2519_KFamBA T2519_PBBA

/-- **Target 7, `gueGrid_twistBA` = D1 (i), the `hoff` producer**: from `GUEPathBoundsBA` (with `Kt = m` on 1-loops)
the `M`-weighted block traces `t_{aq} = W^{-d} Σ_{x∈[a], y∈[q]} M_{xy} G_{yx}` are within `‖M^{(B)}_{aq}‖ (N η_u)⁻¹` of
`M^{(++)}_{aq}`: the conclusion is the second `StochDomAt` premise of `T2517_OneLoopBA` verbatim (at `K = gueGridK sz n0`).
Route R1: `t_{aq} - Q_{aq} = M^{(B)}_{aq} twTr(q, a)` and a fixed-time Stein moment bound on `twTr` at the one-time
Gaussian law of `gueHBA … k` (`ol_gueHBA_eq`). `0 < g` only eventually (coverage row 14). -/
def T2519_HoffBA (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ Λ : ℝ), 0 < κ → 0 < Λ →
    ∀ (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (n0 : ℕ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ),
    Tendsto (fun n => sz.size n) atTop atTop → 1 ≤ n0 →
    (∀ᶠ n in atTop, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
    (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) →
    (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ) →
    T2519_PathBoundsBA sz g E t1 t0 m (gueGridK sz n0) n0 Kt →
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ω =>
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) p.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p.2.2,
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
              Gres (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω)
                (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) true y x -
          BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true p.2.1 p.2.2‖)
      (fun n p _ => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) p.2.1 p.2.2‖ *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹)
-/

/- ACTIVATE AFTER T2517 row b (C4 b, `t/T2517b`) MERGES: `BA/GUEEq729BA` provides `oneStepEnvelopeGUEOf`,
`condExp_loop_step_gueBA`, `condExp_loop_drift_gueBA` (C4 target 6 = `T2517_DriftBA`; reader: `Duhamel_drift_remainder_aeBA`,
row b), `eq729FBA`, `eq729eBA`, `eq729_one_stepBA` (C4 target 7 = `T2517_OneStepBA`; reader: `gueGrid_eq729BA`, row d).

#check @RBM.BA.oneStepEnvelopeGUEOf

#check @RBM.BA.condExp_loop_drift_gueBA

#check @RBM.BA.eq729FBA

#check @RBM.BA.eq729eBA

#check @RBM.BA.eq729_one_stepBA
-/

/- ACTIVATE AFTER T2515 row b (C3 b, `t/T2515b`) MERGES (and T2517 row a, for `gueHBA`): `BA/GUEEntry2` provides
`mixMatBA` (`:448`), `GUEEntry_llErr` (`:48`), `GUEEntry_maxLoop` (`:55`), `GUEEntryMixBA` (`:738`), `gueEntryMixBA` (`:785`);
`BA/GUEEntry` provides `stable_mixBA` (`:68`).

#check @RBM.BA.mixMatBA

#check @RBM.BA.GUEEntry_llErr

#check @RBM.BA.GUEEntryMixBA

#check @RBM.BA.gueEntryMixBA

#check @RBM.BA.stable_mixBA

/-- **Target 4a, `map_gueHBA_eq_mixMatBA`** (twin of `map_gueH_eq_mixMat`, `EntryGrid:118`): under `Pgue (sz.withLam 0)`
the BA grid path at step `k` has the law of C3 b's mixture `g Ψ_I + √t₁ X_block + √(u_k - t₁) X_GUE` under the BA carrier
law `ouP (UNModel.band (sz.withLam 0)) n`; consumer: `gueGrid_entry_boundBA` (from `gueEntryMixBA`). -/
def T2519_MapMixBA : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), 0 ≤ t1 n → t1 n ≤ t0 n →
    (Pgue (sz.withLam 0)).map (gueHBA sz g t1 t0 K n k) =
      (ouP (UNModel.band (sz.withLam 0)) n).map (mixMatBA sz n (g n) (t1 n) (gridTime t1 t0 K n k - t1 n))
-/

end RBM.BA.T2519Check
