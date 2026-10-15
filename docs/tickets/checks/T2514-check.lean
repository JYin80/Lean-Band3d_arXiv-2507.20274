/-
Release check for T2514 (dispatcher V4, 2026-10-15; DECISIONS §337; supervisor 2026-10-15-0643 Q3, Q4 (a), MNO-C3;
design `docs/reports/T2449-design.md` §2, §3.3, §5; probe `t/T2449` 921369b `RBM3D/Probe/T2449Pins.lean:157-257`;
not compiled by the dispatcher).  M/N M1.  Row a (`t/T2514`): `BA/MAPins` publishes every MN1 pin text once (X1-C4,
0643 Q4 (a)) and the three per-`d` readings of MNO-C3; `BA/MALocal` proves locSC at BA from `UNMLOutBA d` per `d` and the
`UNLocAvgBA` bridge through a per-`d` core.  Row b (`t/T2514b`): `BA/MATrLocalBA`, the TrLocal rows through per-`d` cores.
Unmerged names (T2511 row b `unMLOutBA_three`; T2513's filtered forms) in prose only.  Part 1: merged names (`main` a47cf1e1).
Part 2: pins `T2514_*`, binding: the probe texts with the non-`Prop` defs `BAGz`, `BAMz`, `BAprof` (probe 157-168, published
verbatim) unfolded; `T2514_QDExp` is check-local.  Statements only.  Run: lake env lean docs/tickets/checks/T2514-check.lean
-/
import RBM3D.Main.BandTerminal
import RBM3D.Main.FixedZ
import RBM3D.Main.ZTransfer
import RBM3D.Main.ZNet
import RBM3D.Main.BUnivHolds
import RBM3D.BA.MainIndOutBA
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.CouplingWindow
import RBM3D.BA.Ward

set_option linter.style.longLine false

/-! ## Part 1: merged names -/
-- UN-side BA readings and rows (the registry lines are at `main` a47cf1e1; T2511 row b deletes `:140` first)
#check @RBM.Univ.UNMLOutBA                        -- BA/UNPins:110 (V3's output, per `d`)
#check @RBM.Univ.UNLocAvgBA                       -- UNPins:103 (registry :178; row a)
#check @RBM.Univ.UNLocAvgk                        -- Universality/PinsK:406 (structural :391)
#check @RBM.Univ.UNKind.ba                        -- UNPins:84
#check @RBM.Univ.UNTrLocalBARow                   -- UNPins:169 (registry :182; row b)
#check @RBM.Univ.UNTrLocalInitBARow'              -- UNPins:181 (registry :183; row b)
#check @RBM.Univ.UNTrLocal                        -- Universality/Pins:447 (structural :384)
#check @RBM.Univ.UNTrLocalInit'                   -- Universality/PinsC2:72 (structural :388)
#check @RBM.BA.BAEnd_QUEL                         -- UNPins:333 (conjunct of `BAThm27L`; M3)
#check @RBM.BA.BAEnd_BUnivL                       -- UNPins:343 (conjunct of `BAThm27L`; N2)
#check @RBM.Univ.baBUniv_of_rows                  -- UNPins:367 (reads rows a, b in `∀ d` form)
-- V (per `d`) and the row-a inputs
#check @RBM.BA.BAMLOutTL                          -- BA/TwistPins:178
#check @RBM.BA.unMLOutBA_of_BAMLOutTL             -- BA/MainIndOutBA:320 (probe 259, merged)
#check @RBM.BA.BAFlow                             -- BA/FlowPins:389 (carrier `baFMz` :393)
#check @RBM.Gauss.Sizes.Gt_BA                     -- Gauss/BlockAnderson:112 (`G(z) = √t₀ G_{t₀}`, pathwise)
#check @RBM.BA.BAzztE_data                        -- BA/MFixedPoint:297 (with `BAt0_mul` :290, `BAm_norm_le_one` Ward:136)
#check @RBM.BA.ba_dom_of_bulk                     -- BA/RandomLayerBGBA:69 (end domain → chain domain at κ')
#check @RBM.BA.BAm_sub_le_of_im                   -- BA/MReg:84
#check @RBM.BA.BAbulk_window                      -- MReg:122
#check @RBM.Endpoints.calB_zero_eq_Bctl           -- Endpoints:231 (the bridge, probe 227)
#check @RBM.Endpoints.explicit_of_stochDomAt      -- Endpoints:376 (law-generic; `eventually_forall_of_sections` :423)
-- band twins (MA-01..04; N1)
#check @RBM.Endpoints.locSCFixed_of_ML            -- Main/FixedZ:100
#check @RBM.Endpoints.zAve                        -- Main/ZTransfer:368
#check @RBM.Endpoints.btBt                        -- ZTransfer:214 (`STWB_compare` :174, public)
#check @RBM.Endpoints.netLoc                      -- Main/ZNet:999 (public `zNet_exists` :265, `net_union_le` :91, `net_count` :101)
#check @RBM.Endpoints.locBad1_net                 -- ZNet:781 (`locBad2_net` :831)
#check @RBM.Endpoints.locSC_to_UNLocAvgBand       -- Endpoints:519
#check @RBM.Endpoints.unTrLocalBandRow            -- Main/BUnivHolds:205 (`BUniv_trace_le` :172 is private)
-- row b: dilation and coupling
#check @RBM.Univ.ouInit_ba                        -- UNPins:472
#check @RBM.Univ.admissible_lamHat                -- UNPins:503
#check @RBM.BA.BAmWindow_holds                    -- BA/CouplingWindow:688 (`g' ≤ g` only, as `BAwindow_step` :448; F5)
-- instance data at `d = 3`
#check @RBM.Univ.BAInst.S0_adm                    -- UNPins:887 (`S0` :884)
#check @RBM.Univ.BAInst.inst_locAvg_domain        -- UNPins:990
#check @RBM.BA.FlowPinsInst.flow_sz0              -- FlowPins:1214

/-! ## Part 2: pins -/

open MeasureTheory Filter Topology

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

/-! ### Row a, file 1 `BA/MAPins` (probe 157-257 verbatim; M2, M3, N2 read these by name) -/

section Vocab

variable {d : ℕ} (sz : Sizes d)

/-- **P1 `BAendDom`** (probe 169). -/
def T2514_EndDom (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  BAbulk d (sz.L n) (sz.lam n) κ z.re ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
/-- **P1 `BAlocBad1z`** (probe 172; `BAGz`, `BAMz` unfolded). -/
def T2514_LocBad1z (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
    ‖Gres (sz.seqHBA n ω) z true x y -
        Mres ((sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n)) z (BAm d (sz.L n) (sz.lam n) z) x y‖ ^ 2
/-- **P1 `BAlocBad2z`** (probe 176). -/
def T2514_LocBad2z (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, Gres (sz.seqHBA n ω) z true x x -
      BAm d (sz.L n) (sz.lam n) z‖
/-- **P1 `BAqdBadz`** (probe 180; `BAprof sz n z true σ a b` unfolded). -/
def T2514_QdBadz (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) (σ : Bool) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => if σ then Gres (sz.seqHBA n ω) z true x y * Gres (sz.seqHBA n ω) z true y x
          else ((‖Gres (sz.seqHBA n ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b -
      (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) 1 *
          BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) a b /
        ((sz.W n : ℕ) : ℂ) ^ d‖
/-- **P1 `BAdecolBad`** (probe 185; ρ-bulk for the eigenvalue). -/
def T2514_DecolBad (κ τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqHBA n ω) μ ψ → ∀ k, BAbulk d (sz.L n) (sz.lam n) κ (μ k) → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)
/-- Check-local: the expectation half of QDiff at one `z` (probe 207-211 = 243-247; `BAprof … true false/true a b` unfolded). -/
def T2514_QDExp (τ : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  ∀ a b : Zd d (sz.L n),
    ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (sz.seqHBA n ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) -
        (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false) 1 *
            BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false) a b /
          ((sz.W n : ℕ) : ℂ) ^ d‖ ≤ qdBoundExp sz n τ z.im ∧
    ‖(∫ ω, avg2 sz n (fun x y => Gres (sz.seqHBA n ω) z true x y * Gres (sz.seqHBA n ω) z true y x) a b
          ∂(Sizes.seqP (sz.withLam 0))) -
        (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true) 1 *
            BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true) a b /
          ((sz.W n : ℕ) : ℂ) ^ d‖ ≤ qdBoundExp sz n τ z.im

end Vocab

/-- **P2 `BAEnd_locSCL`** (probe 192; owner M1, this ticket). -/
def T2514_EndLocSC (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, T2514_EndDom sz κ ε n z ∧ T2514_LocBad1z sz τ n z ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, T2514_EndDom sz κ ε n z ∧ T2514_LocBad2z sz τ n z ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))
/-- **P2 `BAEnd_QDiffL`** (probe 200; owner M2). -/
def T2514_EndQDiff (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      (Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, T2514_EndDom sz κ ε n z ∧ T2514_QdBadz sz τ n z ω false} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, T2514_EndDom sz κ ε n z ∧ T2514_QdBadz sz τ n z ω true} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, T2514_EndDom sz κ ε n z → T2514_QDExp sz τ n z
/-- **P2 `BAEnd_decolL`** (probe 213; owner M3). -/
def T2514_EndDecol (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, Sizes.seqP (sz.withLam 0) {ω | T2514_DecolBad sz κ τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
/-- **P2 `BAThm27L`** (probe 217; order of `band_terminal`; assembled at `d = 3` by N2, 0643 Q4 (b)). -/
def T2514_Thm27 (d : ℕ) : Prop :=
  T2514_EndDecol d ∧ T2514_EndLocSC d ∧ BAEnd_QUEL d ∧ BAEnd_BUnivL d ∧ T2514_EndQDiff d
/-- **P3 `BAlocSCFixed`** (probe 232; `N₀` uniform over the end domain). -/
def T2514_LocSCFixed (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, ∀ z : ℂ, T2514_EndDom sz κ ε n z →
      Sizes.seqP (sz.withLam 0) {ω | T2514_LocBad1z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP (sz.withLam 0) {ω | T2514_LocBad2z sz τ n z ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
/-- **P3 `BAQDiffFixed`** (probe 238; owner M2). -/
def T2514_QDiffFixed (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, ∀ z : ℂ, T2514_EndDom sz κ ε n z →
      (Sizes.seqP (sz.withLam 0) {ω | T2514_QdBadz sz τ n z ω false} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | T2514_QdBadz sz τ n z ω true} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      T2514_QDExp sz τ n z
/-- **P3 `BAMAFixed`, `BAMANetLoc`, `BAMANetQD`, `BAMADecol`, `BAMAQUE`** (probe 249-257). -/
def T2514_MAFixed (d : ℕ) : Prop := UNMLOutBA d → T2514_LocSCFixed d ∧ T2514_QDiffFixed d
def T2514_NetLoc (d : ℕ) : Prop := T2514_LocSCFixed d → T2514_EndLocSC d
def T2514_NetQD (d : ℕ) : Prop := T2514_QDiffFixed d → T2514_EndQDiff d
def T2514_MADecol (d : ℕ) : Prop := T2514_EndLocSC d → T2514_EndDecol d
def T2514_MAQUE (d : ℕ) : Prop := T2514_EndQDiff d → BAEnd_QUEL d

/-- **P4 `UNLocAvgBAAt`** (new, MNO-C3): `UNLocAvgk` (`PinsK:406-414`) at `UNKind.ba d`, after `∀ d, 3 ≤ d →`. -/
def T2514_LocAvgAt (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      ((UNKind.ba d).M sz).μ {ω | ∃ z : ℂ, ((UNKind.ba d).bulk sz κ z.re n ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧
          z.im ≤ 1) ∧ ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
            ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
                Gres (((UNKind.ba d).M sz).H n ω) z true x x - (UNKind.ba d).mdet sz n z‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))
/-- **P5 `UNTrLocalBAAt`** (new, MNO-C3): `UNTrLocalBARow` (`UNPins:169-174`) after `UNLocAvgBA → ∀ d, 3 ≤ d →`. -/
def T2514_TrLocalAt (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocal sz (UNModelC.ba sz).toUNModel (fun n => BAm d (sz.L n) (sz.lam n)) E δ
/-- **P5 `UNTrLocalInitBAAt'`** (new, MNO-C3): `UNTrLocalInitBARow'` (`UNPins:181-186`), same cut. -/
def T2514_TrLocalInitAt (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocalInit' sz (UNModelC.ba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E δ
/-- **P6** (targets `UNLocAvgBA_iff_at`, `UNTrLocalBARow_iff_at`, `UNTrLocalInitBARow'_iff_at`, each `Iff.rfl`). -/
def T2514_ReadIff : Prop :=
  (UNLocAvgBA ↔ ∀ d : ℕ, 3 ≤ d → T2514_LocAvgAt d) ∧
    (UNTrLocalBARow ↔ (UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → T2514_TrLocalAt d)) ∧
    (UNTrLocalInitBARow' ↔ (UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → T2514_TrLocalInitAt d))

/-! ### Row a, file 2 `BA/MALocal`: locSC at BA per `d`; the bridge through its per-`d` core -/

/-- **A2 `baLocSCFixed_of_ML`** (twin `locSCFixed_of_ML`; reads conj. 1, 5 of `UNMLOutBA d`). -/
def T2514_FixedOfML : Prop := ∀ d : ℕ, UNMLOutBA d → T2514_LocSCFixed d
/-- **A3 `baMANetLoc`** (twin `netLoc`). -/
def T2514_NetLocAll : Prop := ∀ d : ℕ, T2514_NetLoc d
/-- **A4 `baEnd_locSCL`** (A3 ∘ A2). -/
def T2514_EndOfML : Prop := ∀ d : ℕ, UNMLOutBA d → T2514_EndLocSC d
/-- **A5 `baEnd_locSCL_three`** (A4 at T2511 row b's `unMLOutBA_three`; closing condition (i)). -/
def T2514_EndThree : Prop := T2514_EndLocSC 3
/-- **A6 `unLocAvgBAAt_of_locSCL`** (per-`d` core of the bridge; probe 220-228 at one `d`). -/
def T2514_BridgeAt : Prop := ∀ d : ℕ, 3 ≤ d → T2514_EndLocSC d → T2514_LocAvgAt d
/-- **A7 `UNLocAvgBA_of_BAEnd_locSCL`** (probe 220 statement; one line from A6 and P6). -/
def T2514_BridgeAll : Prop := (∀ d : ℕ, T2514_EndLocSC d) → UNLocAvgBA
/-- **A8 `unLocAvgBAAt_of_ML`** (A6 ∘ A4; N2's `d = 3` input with `unMLOutBA_three`). -/
def T2514_LocAvgOfML : Prop := ∀ d : ℕ, 3 ≤ d → UNMLOutBA d → T2514_LocAvgAt d

/-! ### Row b, `BA/MATrLocalBA`: the TrLocal rows through per-`d` cores (MNO-C3) -/

/-- **B2 `unTrLocalBAAt_of_locAvg`** (twin `unTrLocalBandRow` with B1's window uniformisation). -/
def T2514_TrLocalCore : Prop := ∀ d : ℕ, 3 ≤ d → T2514_LocAvgAt d → T2514_TrLocalAt d
/-- **B4 `unTrLocalInitBAAt'_of_locAvg`** (dilation `ouInit_ba`, `admissible_lamHat`; F5). -/
def T2514_TrLocalInitCore : Prop := ∀ d : ℕ, 3 ≤ d → T2514_LocAvgAt d → T2514_TrLocalInitAt d
/-- **B3, B5 `unTrLocalBARow_holds`, `unTrLocalInitBARow'_holds`**: the merged texts, one line each from B2, B4, P6. -/
def T2514_Rows : Prop := UNTrLocalBARow ∧ UNTrLocalInitBARow'

end RBM.BA

end
