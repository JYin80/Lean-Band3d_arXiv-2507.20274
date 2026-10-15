/-
Release check for T2516 (dispatcher V4, 2026-10-15; DECISIONS §339; DECISIONS §266 (1), §316, §336-§338; supervisor
2026-10-15-0643 Q4 (a), Q4 (c), MNO-C4, closing (vi)-(vii); design `docs/reports/T2449-design.md` §2, §3.1, §3.3, §5 `:138`;
probe `t/T2449` 921369b `RBM3D/Probe/T2449Pins.lean:157-257`; not compiled by the dispatcher).  M/N M2 (`BA/MAQDiff`):
QDiff at BA from `UNMLOutBA d` per `d`, the `z`-net with the Lipschitz bound of `BAprof` (new), `baEnd_QDiffL_three`.
Part 1: merged names (`main` b2326aac; `file:line` relative to `RBM3D/`).
Part 2: pins `T2516_*`.  The MN1 texts `BAendDom`, `BAqdBadz`, `BAEnd_QDiffL`, `BAQDiffFixed`, `BAMANetQD` are published by
T2514 row a in `BA/MAPins` (`t/T2514` 112ffba2 `:65, :80, :107, :139, :158`; NOT merged at drafting) and pinned in
`docs/tickets/checks/T2514-check.lean` (`T2514_EndDom` :81, `_QdBadz` :94, `_QDExp` :107, `_EndQDiff` :130,
`_QDiffFixed` :152, `_NetQD` :161).  They are inlined below verbatim from T2514-check (prefix renamed; `BAGz`, `BAMz`,
`BAprof` unfolded as there) only so that this file compiles on `main` today: the 1b reads the `BA/MAPins` names and
never restates them (X1-C4); the auditor compares targets with these pins by `Iff.rfl`.
Statements only; no proofs.  Run: lake env lean docs/tickets/checks/T2516-check.lean
-/
import RBM3D.Main.BandTerminal
import RBM3D.Main.FixedZ
import RBM3D.Main.ZTransfer
import RBM3D.Main.ZNet
import RBM3D.BA.MainIndTermBA
import RBM3D.BA.KInduct
import RBM3D.BA.KBase
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.MReg
import RBM3D.BA.Ward

set_option linter.style.longLine false

/-! ## Part 1: merged names -/
-- V (per `d`) and the conjuncts M2 reads (1 at k = 2, 3, 4; law `seqP (sz.withLam 0)`)
#check @RBM.Univ.UNMLOutBA                        -- BA/UNPins:110
#check @RBM.BA.unMLOutBA_three                    -- BA/MainIndTermBA:47 (T2511 b, unconditional)
#check @RBM.BA.baMainIndFamTL_any                 -- MainIndTermBA:53 (`d > 3` only under `STStep5IIIgL d`; closing (vii))
#check @RBM.BA.unMLOutBA_of_famStep               -- BA/MainIndOutBA:326 (concludes `UNMLOutBA`; registry scan)
#check @RBM.BA.STLKgL                             -- Chain/Carrier:80 (`PrecL` :51)
#check @RBM.BA.STDecaygL                          -- Carrier:94
#check @RBM.BA.STExp2gL                           -- Carrier:127
#check @RBM.BA.BAFlow                             -- BA/FlowPins:389 (`baFMz` :393, `BAflowT0` :380, `BAflowEs` :383, `BAflowLam0` :386)
#check @RBM.BA.BALloop                            -- FlowPins:264
#check @RBM.BA.BAKloop                            -- FlowPins:298 (`BAKsol … (KLloopOf σ a)`, `BAKsol` :283)
-- (Kn2sol), the flow point, the transfer and the symmetry (F2, F3)
#check @RBM.BA.baKsol_two                         -- BA/KInduct:88
#check @RBM.BA.BAzztE_data                        -- BA/MFixedPoint:297 (cl. 4 `ztOf … = √t₀ z`, cl. 5 `√t₀ M₀ = M`)
#check @RBM.BA.BASelf_unique                      -- MFixedPoint:715
#check @RBM.BA.BAdom_real                         -- MFixedPoint:479
#check @RBM.BA.BAt0_mul                           -- MFixedPoint:290
#check @RBM.BA.BATheta_isSymm                     -- BA/KBase:371 (`BATheta_isUnit` :324; private `BAKBase_*` §2a :144-294)
#check @RBM.BA.BAMB_symm                          -- BA/Ward:83
#check @RBM.BA.BAMB_ward_row                      -- Ward:108 (F5: `‖Q(z)‖_{∞→∞} ≤ t₀`, row `ℓ²` ≤ 1)
#check @RBM.BA.BAm_norm_le_one                    -- Ward:136
#check @RBM.BA.BAm_sub_le_of_im                   -- BA/MReg:84
#check @RBM.BA.ba_dom_of_bulk                     -- BA/RandomLayerBGBA:69 (`κ' = (πκ)^5/2048`)
#check @RBM.PropThetaQ                            -- Propagator/Pins:214
#check @RBM.Gauss.Sizes.Gt_BA                     -- Gauss/BlockAnderson:112 (pathwise `G(z) = √t₀ G_{t₀}`)
#check @RBM.Gauss.loopFine                        -- Loop/GLoopFlow:110
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP -- Gauss/FineModel:171 (F4: `det_of_precL`)
-- law-generic bridges and carrier-free public lemmas
#check @RBM.Endpoints.explicit_of_stochDomAt      -- Endpoints:376
#check @RBM.Endpoints.det_of_prec                 -- Endpoints:443 (band law `sz.Prec` only; F4)
#check @RBM.Endpoints.eventually_forall_of_sections -- Endpoints:423 (+ T2514's `Option` fallback)
#check @RBM.Endpoints.qdBound                     -- Endpoints:96 (`qdBoundExp` :101, `avg2` :75)
#check @RBM.Endpoints.floor_X                     -- Main/FixedZ:222 (`prob_union_le` :345, `two_rpow_le` :358)
#check @RBM.Endpoints.trace_two                   -- Main/ZTransfer:319 (`trace_four` :269)
#check @RBM.Endpoints.STWB_compare                -- ZTransfer:174
#check @RBM.Endpoints.avg2_lip                    -- Main/ZNet:351 (`calB_shift_le` :123, `net_union_le` :91)
-- band twins (MA-02..04)
#check @RBM.Endpoints.QDiffFixed_of_ML            -- Main/FixedZ:419 (`qd_core` :259, `qd_exp_core` :373)
#check @RBM.Endpoints.zTrace                      -- Main/ZTransfer:394
#check @RBM.Endpoints.zProfile                    -- ZTransfer:473 (`KLK_two`)
#check @RBM.Endpoints.profPM_lip                  -- Main/ZNet:482 (`profPP_lip` :519; scalar `ξ`)
#check @RBM.Endpoints.qd1Bad_net                  -- ZNet:888 (`qd2Bad_net` :935; private `znet_qd_core` :759)
#check @RBM.Endpoints.netQD                       -- ZNet:1024
#check @RBM.Endpoints.QDiff_holds                 -- Main/BandTerminal:55
-- consumer
#check @RBM.BA.BAEnd_QUEL                         -- BA/UNPins:333 (M3: `BAMAQUE d := BAEnd_QDiffL d → BAEnd_QUEL d`)

/-! ## Part 2: pins -/

open MeasureTheory Filter Topology

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

/-! ### MN1 texts (T2514 row a, `BA/MAPins`; inlined from T2514-check, read by name in the 1b) -/

section Vocab

variable {d : ℕ} (sz : Sizes d)

/-- = `T2514_EndDom` (`T2514-check:81`) = **`BAendDom`** (`t/T2514` `BA/MAPins:65`; probe 169). -/
def T2516_EndDom (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  BAbulk d (sz.L n) (sz.lam n) κ z.re ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
/-- = `T2514_QdBadz` (`:94`) = **`BAqdBadz`** (`MAPins:80`; probe 180; `BAGz`, `BAprof` unfolded). -/
def T2516_QdBadz (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) (σ : Bool) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => if σ then Gres (sz.seqHBA n ω) z true x y * Gres (sz.seqHBA n ω) z true y x
          else ((‖Gres (sz.seqHBA n ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b -
      (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) 1 *
          BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) a b /
        ((sz.W n : ℕ) : ℂ) ^ d‖
/-- = `T2514_QDExp` (`:107`, check-local there too): the expectation half of `BAEnd_QDiffL` at one `z` (probe 207-211). -/
def T2516_QDExp (τ : ℝ) (n : ℕ) (z : ℂ) : Prop :=
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

/-- = `T2514_EndQDiff` (`:130`) = **`BAEnd_QDiffL`** (`MAPins:107`; probe 200).  Concluded by target 9 (owner M2). -/
def T2516_EndQDiff (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      (Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, T2516_EndDom sz κ ε n z ∧ T2516_QdBadz sz τ n z ω false} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, T2516_EndDom sz κ ε n z ∧ T2516_QdBadz sz τ n z ω true} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, T2516_EndDom sz κ ε n z → T2516_QDExp sz τ n z
/-- = `T2514_QDiffFixed` (`:152`) = **`BAQDiffFixed`** (`MAPins:139`; probe 238).  Concluded by target 5. -/
def T2516_QDiffFixed (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, ∀ z : ℂ, T2516_EndDom sz κ ε n z →
      (Sizes.seqP (sz.withLam 0) {ω | T2516_QdBadz sz τ n z ω false} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | T2516_QdBadz sz τ n z ω true} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      T2516_QDExp sz τ n z
/-- = `T2514_NetQD` (`:161`) = **`BAMANetQD`** (`MAPins:158`; probe 253).  Concluded by target 8. -/
def T2516_NetQD (d : ℕ) : Prop := T2516_QDiffFixed d → T2516_EndQDiff d

/-! ### Targets of `BA/MAQDiff` (binding; per `d`, closing (vii)) -/

/-- **5 `baQDiffFixed_of_ML`** (twin `QDiffFixed_of_ML`, `FixedZ:419`; conj. 1 (k = 2), 3, 4 of `UNMLOutBA d` at `BAflowT0`). -/
def T2516_FixedOfML : Prop := ∀ d : ℕ, UNMLOutBA d → T2516_QDiffFixed d
/-- **8 `baMANetQD`** (twin `netQD`, `ZNet:1024`; T2514's BA grid, count `C_R N^{14}`, target 6). -/
def T2516_NetQDAll : Prop := ∀ d : ℕ, T2516_NetQD d
/-- **9 `baEnd_QDiffL`** (8 ∘ 5). -/
def T2516_EndOfML : Prop := ∀ d : ℕ, UNMLOutBA d → T2516_EndQDiff d
/-- **9 `baEnd_QDiffL_three`** (9 at `unMLOutBA_three`; closing condition (i); N2 reads it for `BAThm27L 3`, M3 for `BAMAQUE 3`). -/
def T2516_EndThree : Prop := T2516_EndQDiff 3

/-! ### Intermediate statements (binding in shape; target 6's constant is fixed at the 1a) -/

/-- **1 `baTrace2`** (twin `zTrace`, `ZTransfer:394`; loop indices `(b, a)`): pathwise, `t₀ = BAflowT0`, carrier `baFMz`
(`Gt_BA`, `BAzztE_data` cl. 4, `BASelf_unique`). -/
def T2516_Trace : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), 0 < (z n).im → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
    avg2 sz n (fun x y => Gres (sz.seqHBA n ω) (z n) true x y * Gres (sz.seqHBA n ω) (z n) true y x) a b =
        (BAflowT0 sz z n : ℂ) *
          BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, true] ![b, a] ω ∧
      avg2 sz n (fun x y => ((‖Gres (sz.seqHBA n ω) (z n) true x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (BAflowT0 sz z n : ℂ) *
          BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, false] ![b, a] ω

/-- **2 `baProfile_eq`** (twin `zProfile`, `ZTransfer:473`): the end profile `BAprof sz n (z n) true σ a b` (unfolded) is
`t₀ 𝒦^{(2)}_{t₀,(+,σ),(b,a)}` of `baFMz` (F2 `baKsol_two` at the `BAReal` datum of `BAdom_real` with `κ := Im m`; F3 transfer
`PropThetaQ (Q z) 1 = BATheta λ₀ E m₀ t₀`; `BATheta_isSymm`, `BAMB_symm`).  `0 < sz.lam n` is eventual from `WO`. -/
def T2516_Profile : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), 0 < (z n).im → 0 < sz.lam n → ∀ (σ : Bool) (a b : Zd d (sz.L n)),
    (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (z n) (BAm d (sz.L n) (sz.lam n) (z n))) true σ) 1 *
        BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (z n) (BAm d (sz.L n) (sz.lam n) (z n))) true σ) a b /
        ((sz.W n : ℕ) : ℂ) ^ d =
      (BAflowT0 sz z n : ℂ) * BAKloop sz (BAflowLam0 sz z) (BAflowEs sz z) n (BAflowT0 sz z n) ![true, σ] ![b, a]

/-- **6 `baProf_lip`** (new, F5; the band `profPM_lip`/`profPP_lip`, `ZNet:482, 519`, have a scalar `ξ`): on the ρ-bulk,
`|ΔBAprof| ≤ C η⁻² |z - w| W^{-d}` with `C = C(κ)` before `sz` (U5S-C3).  Route: `‖Q(z)‖_{∞→∞} ≤ t₀ < 1` (Ward,
`BAMB_ward_row`), Neumann `‖Θ‖_{∞→∞} ≤ (1 - t₀)⁻¹ ≤ 2/η`, `Θ - Θ' = Θ (Q - Q') Θ'`, `‖Q - Q'‖_{∞→∞} ≤ 2 ‖M - M'‖_op`,
`‖M - M'‖_op ≤ κ'^{-2} (1 + κ'^{-2}) |z - w|` (`BAm_sub_le_of_im`, T2514 1a row 8): proposal `C = 12 κ'^{-2} (1 + κ'^{-2})`. -/
def T2516_ProfLip : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (η : ℝ) (z w : ℂ), 0 < η → η ≤ z.im →
    η ≤ w.im → z.im ≤ 1 → w.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re → BAbulk d (sz.L n) (sz.lam n) κ w.re →
      ∀ (σ : Bool) (a b : Zd d (sz.L n)),
        ‖(PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) 1 *
              BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) a b /
            ((sz.W n : ℕ) : ℂ) ^ d -
          (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) w (BAm d (sz.L n) (sz.lam n) w)) true σ) 1 *
              BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) w (BAm d (sz.L n) (sz.lam n) w)) true σ) a b /
            ((sz.W n : ℕ) : ℂ) ^ d‖ ≤ C * (η ^ 2)⁻¹ * ‖z - w‖ / ((sz.W n : ℕ) : ℝ) ^ d

end RBM.BA

end
