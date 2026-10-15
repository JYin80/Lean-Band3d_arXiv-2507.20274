/-
Release check for T2515 (dispatcher V4, 2026-10-15; DECISIONS §337; supervisor
2026-10-15-0643 Q3 `:60-64`, Q4 (c) `:73-75`, MNO-C4 `:88`; 2049 GMN-C4 `:105-108`; 1102 O9 `:205-217`; DECISIONS `:580`).
BA stage M/N row C3 (T2449 §5 `:134`): the BA OU profile `UNOUProfile.ba`, `UNOUProfRowk (UNKind.ba d)` in the lossless
row-difference form (O9), the profile half `RBG_ProfComp` at BA, the BA `thetaDiff` at `ζ = 0` (Q4 (c)), the BA forms of
`KPrim` (row a, `BA/GUEKPrim`) and of `EntryDet`/`EntryTail`/`EntryTailMain` (row b, `BA/GUEEntry`).
Part 1: merged names (`main` a47cf1e1; `file:line` relative to `RBM3D/`).
Part 2: the D1 proposals as `Prop` values (prefix `T2515_`): binding after the 1a-audit.  The BA end profile of
`BAEnd_QDiffL` (T2449 probe `t/T2449` 921369b `:164`, `BAprof`; published by M1 row a in `BA/MAPins`) is written inline.
Statements only; no proofs; not compiled by the dispatcher.
Run: lake env lean docs/tickets/checks/T2515-check.lean
-/
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.Prop6Path
import RBM3D.BA.KBase
import RBM3D.BA.EKNonzero
import RBM3D.BA.EMn2BA
import RBM3D.BA.KTreeRep
import RBM3D.BA.CombesThomas
import RBM3D.BA.Prop5Short
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.GUEPhase.EntryTailMain
import RBM3D.Main.QUEFromQDiff

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 1: merged names -/

-- the generic interface C3 instantiates at `UNKind.ba` (T2282, C5g)
#check @RBM.Univ.UNOUProfile                       -- Universality/OUInterfaceK:43
#check @RBM.Univ.UNOUProfile.band                  -- OUInterfaceK:48
#check @RBM.Univ.UNOUProfRowk                      -- OUInterfaceK:56 (registry `Test/Axioms:171`, owner BA-C3)
#check @RBM.Univ.ouRowk_of_pins                    -- OUInterfaceK:292 (premise `hprof`; N2 instantiates)
#check @RBM.Univ.unOUProfRowk_band                 -- OUInterfaceK:329
#check @RBM.Univ.GUEPhase.RBG_ProfComp             -- Universality/GUEPhase/RandomLayerBG:123
#check @RBM.Univ.GUEPhase.RBG_Comp                 -- RandomLayerBG:115
#check @RBM.Univ.GUEPhase.RBG_Que                  -- RandomLayerBG:87 (reads `P`; C5's producer at BA)
#check @RBM.Univ.GUEPhase.g1Rowk_of_inputsG        -- RandomLayerBG:399
#check @RBM.Univ.GUEPhase.RandomLayerBG_profComp_band  -- RandomLayerBG:465 (`rfl`)
#check @RBM.BA.RandomLayerBGBA_comp                -- BA/RandomLayerBGBA:126 (takes `RBG_ProfComp` at BA)
#check @RBM.Univ.UNKind.ba                         -- BA/UNPins:84 (bulk `BAbulk`, `lamV = 0`)
-- band twins (class T; row a: KPrim, ZeroModeProfile §2; row b: EntryDet, EntryTail, EntryTailMain)
#check @RBM.Univ.SBtilde                           -- Universality/ZeroModeProfile:65
#check @RBM.Univ.Jmat                              -- ZeroModeProfile:62
#check @RBM.Univ.ThetaTilde                        -- ZeroModeProfile:69
#check @RBM.Univ.ThetaTilde_eq                     -- ZeroModeProfile:281
#check @RBM.Univ.norm_ThetaTilde_sub_le            -- ZeroModeProfile:367
#check @RBM.Univ.profTilde_rowDiff                 -- ZeroModeProfile:469
#check @RBM.Univ.profPMTilde_zero                  -- ZeroModeProfile:522
#check @RBM.Univ.GUEPhase.kTwoGUE                  -- Universality/GUEPhase/KPrim:68
#check @RBM.Univ.GUEPhase.kTwoGUE_eq_ThetaTilde    -- KPrim:91
#check @RBM.Univ.GUEPhase.hasDerivAt_kTwoGUELoop   -- KPrim:209
#check @RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pm_eq_profPMTilde  -- KPrim:275
#check @RBM.Univ.GUEPhase.gueK_exists              -- KPrim:749
#check @RBM.Univ.GUEPhase.primRhsGUE               -- GUEPhase/Bootstrap:178 (model-free)
#check @RBM.Univ.GUEPhase.RandomLayerB_KFam        -- GUEPhase/RandomLayerB:63 (band `KF`)
#check @RBM.Univ.stable_mix                        -- GUEPhase/EntryDet:91
#check @RBM.Univ.mix_det                           -- EntryDet:719
#check @RBM.Univ.GUEEntryMix                       -- GUEPhase/EntryTail:94
#check @RBM.Univ.mixEntry_det                      -- EntryTail:859
#check @RBM.Univ.gueEntryMix                       -- GUEPhase/EntryTailMain:545
#check @RBM.Endpoints.MAThetaDiff                  -- Main/QUECore:76 (band `thetaDiff` pin)
#check @RBM.Endpoints.thetaDiff                    -- Main/QUECore:105
#check @RBM.Endpoints.queRowDiff                   -- Main/QUEFromQDiff:244 (consumer form; M3's twin reads the BA one)
-- BA inputs (all merged; none is a V output)
#check @RBM.BA.BAm                                 -- BA/MFixedPoint:379
#check @RBM.BA.BAm_self                            -- MFixedPoint:809
#check @RBM.BA.BAt0                                -- MFixedPoint:279
#check @RBM.BA.BAflowE                             -- MFixedPoint:280
#check @RBM.BA.BAt0_lt_one                         -- MFixedPoint:285
#check @RBM.BA.BAzztE_data                         -- MFixedPoint:297 (conj. 5: `√t₀ M(λ₀, E, m₀) = M(λ, z, m)`)
#check @RBM.BA.BAbulk                              -- MFixedPoint:429
#check @RBM.BA.BAReal                              -- MFixedPoint:432
#check @RBM.BA.BAdom_real                          -- MFixedPoint:479
#check @RBM.BA.BAMB                                -- MFixedPoint:190
#check @RBM.BA.BAMss                               -- MFixedPoint:511
#check @RBM.BA.BATheta                             -- MFixedPoint:515
#check @RBM.BA.BATheta0                            -- MFixedPoint:519
#check @RBM.BA.BAPropM                             -- MFixedPoint:567
#check @RBM.BA.BAoffDiag                           -- MFixedPoint:583
#check @RBM.PropThetaQ                             -- Propagator/Pins:214
#check @RBM.BA.BAProp8                             -- BA/FlowPins:217 (lossless: no `W^τ`, no `≺`)
#check @RBM.BA.baProp8_holds                       -- BA/Prop6Path:1009 (O9 (a) on `main`)
#check @RBM.BA.baProp5to8_holds                    -- Prop6Path:1049
#check @RBM.BA.baP8_BATheta_shift                  -- Prop6Path:497 (translation invariance of `BATheta`)
#check @RBM.BA.EKNonzero_Mss_shift                 -- BA/EKNonzero:110
#check @RBM.BA.BATheta_isUnit                      -- BA/KBase:324
#check @RBM.BA.BATheta_resolvent                   -- KBase:330
#check @RBM.BA.BATheta_row_sum_pm                  -- KBase:381
#check @RBM.BA.BAMB_row_sq_real                    -- BA/Ward:125 (`Σ_b |M_ab|² = 1` at real `E`)
#check @RBM.BA.BAK_row_sum                         -- BA/KKernel:124
#check @RBM.BA.BAMss_ss_diag                       -- BA/Prop5Short:110
#check @RBM.BA.EMn2BA_SB_zero                      -- BA/EMn2BA:77 (`SB d L 0 = 1`)
#check @RBM.BA.BAKsolve                            -- BA/KSolve:58 (`(Kn2sol)`: 2-loop `W^{-d} (Θ_t M)`)
#check @RBM.BA.baKsolve                            -- BA/KTreeRep:1699
#check @RBM.BA.baPropM_holds                       -- BA/CombesThomas:562
#check @RBM.BA.baOffDiag_holds                     -- BA/Ward:303
#check @RBM.BA.BAm_im_lower_window                 -- BA/MReg:227
#check @RBM.BA.ba_dom_of_bulk                      -- BA/RandomLayerBGBA:69 (`Im m ≥ κ' = (πκ)^5/2048`)
#check @RBM.BA.ba_Ed_of_im                         -- RandomLayerBGBA:87
#check @RBM.BA.ba_flowG                            -- RandomLayerBGBA:92 (`cT ≤ t₀ < 1`)
#check @RBM.Univ.ouMatC_ba_eq_band_add             -- BA/UNPins:445 (row b: BA OU carrier = band + `λΨ`)
#check @RBM.Univ.ouP_ba_eq_band                    -- BA/UNPins:467

/-! ## Part 2: D1 proposals (prefix `T2515_`; NOT binding until the 1a-audit) -/

namespace RBM.BA.T2515Check

open RBM RBM.Gauss RBM.Univ RBM.Univ.GUEPhase RBM.BA

/-- **D1 (iii), the BA OU profile** (`UNOUProfile.ba d` satisfies this by `rfl`): `pm`, `pp` are
`W^{-d} (Θ̃_ζ M^{(+,σ)})_{ab}` with `Θ̃_ζ = (1 - M^{(+,σ)}(z) S̃_ζ)⁻¹`, `S̃_ζ = SBtilde d L 0 ζ = (1 - ζ) 1 + (ζ/L^d) J`
(`SB d L 0 = 1`), `M = BAMB d L λ z (BAm d L λ z)`, `λ = sz.lam n`; it reads `sz` at the index only. -/
def T2515_ProfSpec (d : ℕ) (P : UNOUProfile (UNKind.ba d)) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)),
    (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false;
      P.pm sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) ∧
    (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true;
      P.pp sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)

/-- **D1 (iii) → target 4**: `UNOUProfRowk` (`OUInterfaceK:56`, merged text, read by name) at the BA profile:
lossless (O9), `C = C(d, 𝔡, κ)` before `sz`.  Consumer: N2 (`ouRowk_of_pins`, premise `hprof`). -/
def T2515_ProfRowBA (d : ℕ) : Prop :=
  3 ≤ d → ∀ P : UNOUProfile (UNKind.ba d), T2515_ProfSpec d P → UNOUProfRowk (UNKind.ba d) P

/-- **Target 5**: the profile half of `RBG_Comp` at BA (expected `rfl`, as `RandomLayerBG_profComp_band`).
Consumer: N2 (`RandomLayerBGBA_comp` → `g1Rowk_of_inputsG`). -/
def T2515_ProfCompBA (d : ℕ) : Prop :=
  ∀ P : UNOUProfile (UNKind.ba d), T2515_ProfSpec d P → RBG_ProfComp (UNKind.ba d) P

/-- **D1 (ii), the `ζ = 0` bridge**: at `ζ = 0` the profile is the end profile of `BAEnd_QDiffL`
(`BAprof sz n z true σ`, T2449 probe `:164`: `(PropThetaQ Q 1 * Q)_{ab} / W^d`). -/
def T2515_ProfZero (d : ℕ) : Prop :=
  ∀ P : UNOUProfile (UNKind.ba d), T2515_ProfSpec d P →
    ∀ (sz : Sizes d) (n : ℕ) (z : ℂ) (σ : Bool) (a b : Zd d (sz.L n)),
      (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ;
        (if σ then P.pp sz n 0 z a b else P.pm sz n 0 z a b) = (PropThetaQ Q 1 * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)

/-- **D1 (i), the transfer (O9 core)**: at `Im z > 0`, `Θ_s` at `z` is `BATheta` at the flow point
`(λ₀, E, m₀) = (√t₀ λ, BAflowE z m, m/√t₀)` at time `s t₀` (`BAzztE_data` conj. 5; `BAMss` of a real multiple). -/
def T2515_ThetaTransfer : Prop :=
  ∀ (d L : ℕ) [NeZero L] (lam : ℝ) (z : ℂ), 0 < z.im → ∀ (s : ℝ) (σ₁ σ₂ : Bool),
    let m := BAm d L lam z; let t0 := BAt0 z m;
    PropThetaQ (BAMss d L (BAMB d L lam z m) σ₁ σ₂) s =
      BATheta d L (Real.sqrt t0 * lam) (BAflowE z m) (m / (Real.sqrt t0 : ℂ)) (s * t0) σ₁ σ₂

/-- **UBA-C1 comparison** (one, from `ba_flowG`): `cT ≤ t₀`, i.e. `cT λ² ≤ λ₀² ≤ λ²`, `cT = κ'/(κ'+1)`. -/
def T2515_CmpBA : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ cT : ℝ, 0 < cT ∧ ∀ (d L : ℕ) [NeZero L] (lam : ℝ) (z : ℂ),
    BAbulk d L lam κ z.re → 0 < z.im → z.im ≤ 1 → cT ≤ BAt0 z (BAm d L lam z)

/-- **D1 (i), O9: lossless oscillation of `Θ̃^{BA}_ζ`** (twin of `norm_ThetaTilde_sub_le`): from `baProp8_holds` at
`(Λ, κ') = (𝔡⁻¹, (πκ)^5/2048)`, time `(1 - ζ) t₀ ∈ [0, 1)`, `(λ₀² + |1 - t|)⁻¹ ≤ (cT λ²)⁻¹`; the `α J` part cancels. -/
def T2515_ThetaTildeOscBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d L lam κ z.re → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
        ∀ (σ : Bool) (u v : Zd d L),
          let Q := BAMss d L (BAMB d L lam z (BAm d L lam z)) true σ;
          ‖Ring.inverse (1 - Q * SBtilde d L 0 ζ) u v - Ring.inverse (1 - Q * SBtilde d L 0 ζ) 0 0‖ ≤
            C * (lam ^ 2)⁻¹

/-- **D1 (ii), Q4 (c): the BA `thetaDiff` at `ζ = 0`**, in the consumer form of `queRowDiff` (`QUEFromQDiff:244`) on
the end profile `(Θ M)^{(+,σ)}/W^d` (= `BAprof sz n z true σ`).  Consumer: M3 (BA twin of `QUE_of_QDiff`). -/
def T2515_ThetaDiffBA : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re →
        ∀ (σ : Bool) (a b b' : Zd d (sz.L n)),
          let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ;
          ‖(PropThetaQ Q 1 * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d - (PropThetaQ Q 1 * Q) a b' / ((sz.W n : ℕ) : ℂ) ^ d‖ ≤
            C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d

end RBM.BA.T2515Check
