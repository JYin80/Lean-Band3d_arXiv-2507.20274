/-
Release check for T2468 (dispatcher V3, Mon Oct 12 17:34 UTC 2026; DECISIONS §272).  BA-G G7: the primed Step-1 rewire (supervisor 1155 C3;
2254 Q2: the diagonal pin stays the unprimed `BAGbEXPii`, only `BAGbEXPij` is superseded; 2254 Q3: the consumer change).
Additive: the new file `BA/Step1Prime.lean` (reserve `BA/Step1PrimeB.lean`); the merged Step-1 and Green files are not
edited (their names in Part 1 keep their statements, G1).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2468_`; content binding up to the name).
Part 3: shapes (not binding).
Merged names only.  No proofs, no placeholders.
Run: lake env lean docs/tickets/checks/T2468-check.lean
-/
import RBM3D.BA.GbEXPav
import RBM3D.BA.KBound
import RBM3D.BA.Prop5Short
import RBM3D.Defs.RadialSum
import RBM3D.Induction.LocalAvg1
import RBM3D.Induction.LocalAvg2

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the Green pins of stage G (C3; 2254 Q2) and their proofs
#check @RBM.BA.BAGbEXPij'
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.baGbEXPii_holds
#check @RBM.BA.BAGbEXPav
#check @RBM.BA.baGbEXPav_holds
#check @RBM.BA.GreenCore_loopPrem
#check @RBM.BA.GreenCore_decayRHS
#check @RBM.BA.GreenCore_decayConcl
#check @RBM.BA.GreenStab_clam
#check @RBM.BA.GreenOff_T_le_decayRHS

-- the unprimed band-window pin (superseded at this merge) and its vocabulary
#check @RBM.BA.BAGbEXPij
#check @RBM.BA.BAGijGEX
#check @RBM.BA.BAGiiGEX
#check @RBM.BA.BAGavLGEX
#check @RBM.BA.FlowFM.indMax
#check @RBM.BA.FlowFM.gexRHS
#check @RBM.BA.FlowFM.omegaC
#check @RBM.BA.FlowFM.gmMax

-- the merged Step 1 at BA (T2262, T2269, T2277): the consumers whose primed successors this row writes
#check @RBM.BA.flowFM_wl_det
#check @RBM.BA.baS1Std
#check @RBM.BA.baNetLift
#check @RBM.BA.baS1_wl_seq
#check @RBM.BA.baS1_forb
#check @RBM.BA.baS1_boot
#check @RBM.BA.baS1_weakPT
#check @RBM.BA.baS1_loopPT
#check @RBM.BA.baBootstrap'_holds
#check @RBM.BA.baGii_member
#check @RBM.BA.baGij_member
#check @RBM.BA.baM_entry_le
#check @RBM.BA.baBoot_LI
#check @RBM.BA.BABootstrap'
#check @RBM.BA.BAStep1
#check @RBM.BA.BAStep1_of_parts'
#check @RBM.BA.baStep1_holds
#check @RBM.BA.BAFlowMember
#check @RBM.BA.BAFlowMember_holds
#check @RBM.BA.BALmaxFromLK_holds
#check @RBM.BA.BATrivialLmax_holds
#check @RBM.BA.baConArg''_holds
#check @RBM.BA.BAFamZ
#check @RBM.BA.BAFamZ_main
#check @RBM.BA.BAWinBulk
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baFMz
#check @RBM.Ind.s1_F5
#check @RBM.Ind.s1_F8
#check @RBM.Ind.s1_ratio_ev

-- the merged instances (patterns; the primed ones drop `hii`, `hij`, `hmem`, `hwin` and, for the bootstrap, `hK`)
#check @RBM.BA.Step1Inst.inst_baBootstrap'
#check @RBM.BA.Step1Inst.inst_hGij
#check @RBM.BA.Step1FamInst.inst_baBootstrap'_full
#check @RBM.BA.Step1FamInst.inst_baStep1
#check @RBM.BA.Step1FamInst.inst_baStep1_low
#check @RBM.BA.Step1FamInst.inst_BALmaxFromLK
#check @RBM.BA.Step1FamInst.sz0_win_third
#check @RBM.BA.Step1BootInst.inst_baGij_member
#check @RBM.BA.Step1SetupInst.inst_baS1Std
#check @RBM.BA.Step1SetupInst.sI
#check @RBM.BA.Step1SetupInst.tI
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
#check @RBM.Gauss.SizesInst.sz0

-- K12 (supervisor 0150 O2: `hK` of `inst_baBootstrap'` has the type of `inst_BAKbound`)
#check @RBM.BA.inst_BAKbound
#check @RBM.BA.baKbound_holds
#check @RBM.BA.BAKbound
#check @RBM.BA.STKboundgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STLocalMaxgL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.STInitialGT2gL
#check @RBM.BA.STmaxLoop2g
#check @RBM.BA.PrecL

-- the generic Green pins whose BA owner text names stage G (registry `:148-150`) and their readers
#check @RBM.BA.STGiiGEXgL
#check @RBM.BA.STGijGEXgL
#check @RBM.BA.STGavLGEXgL
#check @RBM.BA.STindMaxg
#check @RBM.Gauss.Sizes.stStep2LocalPT_of_L2decayG
#check @RBM.Gauss.Sizes.stStep2AvgPT_of_L2decayG

-- the exponential sums for the window constant (2254 Q3: `3S⁴ + 4`, inside proofs only)
#check @RBM.expC
#check @RBM.sum_radial_exp_decay_le
#check @RBM.BA.BAsum_exp_decay_le
#check @RBM.Gauss.zdistD_le_mul_zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD

/-! ## Part 2: the target statements (binding up to the name) -/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- Target 1 (`baGij'_member`): the primed pin at every member `z'` of `Fam(t)` and every `0 ≤ u ≤ t`, the rate `c` fixed
after `(κ, ε, 𝔡)` (successor of `baGij_member`, `BA/Step1Boot.lean:283`). -/
def T2468_GijMember' : Prop :=
  ∀ d : ℕ, BAGbEXPij' d → BAFlowMember d →
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
          ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
            ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
              ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) →
                ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
                  ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
                    (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
                    (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
                    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
                    GreenCore_loopPrem sz z' u ε₀ Φ → GreenCore_decayConcl sz z' u ε₀ D c Φ Ψ

/-- Target 4a (`baBootstrap'_of_ij'`): the primed successor of `baBootstrap'_holds` (`BA/Step1.lean:576`), guard `2 ≤ d`. -/
def T2468_BootstrapIj' : Prop :=
  ∀ d : ℕ, 2 ≤ d → BAFlowMember d → BAGbEXPii d → BAGbEXPij' d → BABootstrap' d

/-- Target 4b (`baStep1_of_ij'`): the primed successor of `baStep1_holds` (`BA/Step1Fam.lean:695`), guard `2 ≤ d`. -/
def T2468_Step1Ij' : Prop :=
  ∀ d : ℕ, 2 ≤ d → BAGbEXPii d → BAGbEXPij' d → BAStep1 d

/-- Target 5a (`baBootstrap'_holds'`): the bootstrap at BA, unconditional for `2 ≤ d`. -/
def T2468_BootstrapHolds : Prop :=
  ∀ d : ℕ, 2 ≤ d → BABootstrap' d

/-- Target 5b (`baStep1_holds'`): Step 1 of `lem:main_ind_BA` at BA, unconditional for `2 ≤ d` (the producer read from
U3-BA (b), U5 and V2; REQ UBA `:30`). -/
def T2468_Step1Holds : Prop :=
  ∀ d : ℕ, 2 ≤ d → BAStep1 d

/-- Target 6a (`baSTGiiGEXgL_holds`): the generic `(GiiGEX)` at the BA carrier and law, from `baGbEXPii_holds`. -/
def T2468_STGiiBA : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEXgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀

/-- Target 6b (`baSTGavLGEXgL_holds`): the generic `(GavLGEX)` at the BA carrier and law, from `baGbEXPav_holds`. -/
def T2468_STGavBA : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGavLGEXgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀

/-- Target 7a (`inst_baBootstrap'_ij'`): `d = 3`, `sz0`, `zSeq`, `(s, t) = (1/2, 2/3)`; `hK` discharged from
`inst_BAKbound` (0150 O2); only `hLK`, `hLoc` stay (BA-V). -/
def T2468_InstBootstrap : Prop :=
  STLKgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
      (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) RBM.BA.Step1SetupInst.sI →
    STLocalMaxgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
        (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) RBM.BA.Step1SetupInst.sI →
      STStep1LoopgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
          (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) RBM.BA.Step1SetupInst.sI RBM.BA.Step1SetupInst.tI ∧
        STStep1WeakgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
          (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) RBM.BA.Step1SetupInst.sI RBM.BA.Step1SetupInst.tI

/-- Target 7b (`inst_baStep1'`): the family form at `sz0`, `zSeq`, `c₁ = 1/3`, `(s, t) = (1/2, 2/3)`; the family premise
stays (0150 K2); no Green pin is a hypothesis. -/
def T2468_InstStep1 : Prop :=
  (∀ z' : ℕ → ℂ, BAFamZ RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (1 / 3) RBM.BA.Step1SetupInst.sI z' →
      STKboundgL (baFMz RBM.Gauss.SizesInst.sz0 z') (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) ∧
        STLKgL (baFMz RBM.Gauss.SizesInst.sz0 z') (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))
          RBM.BA.Step1SetupInst.sI ∧
        STLocalMaxgL (baFMz RBM.Gauss.SizesInst.sz0 z') (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))
          RBM.BA.Step1SetupInst.sI) →
    STStep1LoopgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
        (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) RBM.BA.Step1SetupInst.sI RBM.BA.Step1SetupInst.tI ∧
      STStep1WeakgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
        (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0)) RBM.BA.Step1SetupInst.sI RBM.BA.Step1SetupInst.tI

/-! ## Part 3: shapes (not binding) -/

/-- Stage G's closing conditions (2254 Q2 `:72-78`) as statements: the three proved Green pins. -/
example : Prop := ∀ d : ℕ, 2 ≤ d → BAGbEXPij' d ∧ BAGbEXPii d ∧ BAGbEXPav d

/-- What U3-BA (b), U5 and V2 read (UBA-C3: `BAStep1 d` is their hypothesis of exact type until this row merges). -/
example : Prop := T2468_Step1Holds ∧ T2468_BootstrapHolds

/-- The conditional successors and the member transfer together. -/
example : Prop := T2468_GijMember' ∧ T2468_BootstrapIj' ∧ T2468_Step1Ij'

/-- The BA readings of the generic Green pins (registry `:148`, `:150`); `STGijGEXgL` at BA is not a target. -/
example : Prop := T2468_STGiiBA ∧ T2468_STGavBA

/-- The instances. -/
example : Prop := T2468_InstBootstrap ∧ T2468_InstStep1

/-- The type of `hK` in `inst_baBootstrap'`, which `inst_BAKbound` inhabits (0150 O2). -/
example : Prop :=
  STKboundgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) (Sizes.seqP (RBM.Gauss.SizesInst.sz0.withLam 0))

/-- The loop premise of the primed pin at the main flow, with a constant control (the shape target 2 (a) produces at a
member, with `Φ_n = Bctl_n(s_n)^{7/15}`). -/
example : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (u : ℕ → ℝ) (ε₀ : ℝ) (φ : ℕ → ℝ),
    GreenCore_loopPrem sz z u ε₀ (fun n _ _ => φ n)

end RBM.BA
