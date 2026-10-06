/-
Release check for T2238 (dispatcher V1, Tue Oct  6 00:45 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §72, §68, §52, §45 O2,
§29, §20, §17, §16).
BA-S2a (block Anderson, gate BA; T2205 portmap row BA-S2a, `docs/reports/T2205-portmap.md:66`): `RBM3D/BA/Step1Trivial.lean`,
the deterministic `(lRB1)` bound at `s₀ = 1 - c₁` for every member of `Fam(0)` (`BATrivialLmax`, probe
`git show 96e4087:RBM3D/Probe/T2205Pins.lean` `:1775-1784`), with the family predicate `BAFamZ` (probe `:1250-1254`) and the
two elementary facts `BAflow_T0_bounds` (`:1284-1291`), `BAFamZ_main` (`:1293-1295`) moved from the probe.
Section 1: the merged names the proof uses (exact namespaces; file:line, last commit on `main` e64e4f0).
Section 2: the vocabulary `BAFamZ` (probe `:1252-1254` verbatim; = T2205 check `:200-204` by `rfl`, probe `:3978`) and the pin
`BATrivialLmax` (probe `:1779-1784` verbatim), in the temporary namespace `RBM.BA.T2238Check`; T2238 defines both in `RBM.BA`
under the same names.
Section 3: the statements of the public theorems of T2238 as `*_pin : Prop`.
Section 4: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2238-check.lean`.
-/
import RBM3D.BA.CouplingWindow
import RBM3D.BA.FlowPins
import RBM3D.Induction.Step1Setup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Real.Sqrt

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

/-! ## 1. Merged names -/

-- T2189 (ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA`
#check @RBM.BA.BAt0            -- :279
#check @RBM.BA.BAflowE         -- :280
#check @RBM.BA.BAt0_pos        -- :282
#check @RBM.BA.BAt0_lt_one     -- :285
#check @RBM.BA.BAm             -- :379
#check @RBM.BA.BAdom           -- :435
-- T2197 (b750bf3): `RBM3D/BA/FlowPins.lean`, namespace `RBM.BA`
#check @RBM.BA.BAmF            -- :250
#check @RBM.BA.BAGt            -- :257
#check @RBM.BA.BALloop         -- :262
#check @RBM.BA.PrecL           -- :328
#check @RBM.BA.FlowFM          -- :332
#check @RBM.BA.STLmaxgL        -- :364
#check @RBM.BA.baFM            -- :479
#check @RBM.BA.BAflowT0        -- :537
#check @RBM.BA.BAflowEs        -- :540
#check @RBM.BA.BAflowLam0      -- :543
#check @RBM.BA.BAFlow          -- :546
#check @RBM.BA.baFMz           -- :550
-- T2197: `RBM3D/BA/FlowPins.lean`, namespace `RBM.BA.FlowPinsInst` (instance data)
#check @RBM.BA.FlowPinsInst.zSeq         -- :1333
#check @RBM.BA.FlowPinsInst.sz0_lam_pos  -- :1336
#check @RBM.BA.FlowPinsInst.flow_sz0     -- :1366
#check @RBM.BA.FlowPinsInst.t0_sz0       -- :1379
-- T2227 (e1fec21): `RBM3D/BA/CouplingWindow.lean`, namespace `RBM.BA`
#check @RBM.BA.BAWinBulk       -- :799
-- T2013 (868b3b4): `RBM3D/Loop/GLoopFlow.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.ztOf                 -- :55
#check @RBM.Gauss.etaOf                -- :58
#check @RBM.Gauss.ztOf_im              -- :64
#check @RBM.Gauss.Gres                 -- :74
#check @RBM.Gauss.loopM                -- :92
#check @RBM.Gauss.blockMat             -- :105
#check @RBM.Gauss.loopFine             -- :110
#check @RBM.Gauss.norm_loopM_le_sharp  -- :903 (`‖G‖ ≤ 1/η` is inside it; the resolvent bounds `:741`, `:773` are private)
-- T2013 (868b3b4): `RBM3D/Gauss/BlockAnderson.lean`
#check @RBM.Gauss.PsiI                 -- :52
#check @RBM.Gauss.PsiI_isHermitian     -- :65
#check @RBM.Gauss.Sizes.seqHflowBA     -- :83
-- 0a873f1: `RBM3D/Gauss/FineModel.lean`, namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.SeqΩ                 -- :160
#check @RBM.Gauss.Sizes.seqP                 -- :169
#check @RBM.Gauss.Sizes.seqHflow             -- :225
#check @RBM.Gauss.Sizes.seqHflow_isHermitian -- :531
-- 0a873f1: `RBM3D/Defs/Sizes.lean`
#check @RBM.Gauss.Sizes                -- :138
#check @RBM.Gauss.Sizes.WO             -- :164
#check @RBM.Gauss.Sizes.SizeTendsto    -- :173
#check @RBM.Gauss.Sizes.Admissible     -- :177
#check @RBM.Gauss.Sizes.withLam        -- :182
#check @RBM.Gauss.Sizes.Bctl           -- :214
#check @RBM.Gauss.SizesInst.sz0        -- :260
-- 5d1e6b1: `RBM3D/Induction/ScaleFacts.lean`, namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STBctl_pos     -- :64
#check @RBM.Gauss.Sizes.STBctl_mono    -- :74
#check @RBM.Gauss.Sizes.STBctl_ge      -- :126
-- 9e2b00f: `RBM3D/Defs/StochDomAt.lean`
#check @RBM.badSetAt                   -- :53
#check @RBM.StochDomAt                 -- :61
#check @RBM.Gauss.Sizes.one_le_size    -- :130
#check @RBM.StochDomAt.of_subset       -- :325
#check @RBM.StochDomAt.of_le_left      -- :347
#check @RBM.StochDomAt.refl            -- :400
#check @RBM.StochDomAt.trans           -- :411
#check @RBM.StochDomAt.const_mul_left  -- :462
-- T2079 (4f186cf): `RBM3D/Induction/Step1Setup.lean`, namespace `RBM.Ind` (the band model)
#check @RBM.Ind.s1_hsize               -- :199
#check @RBM.Ind.s1_Wd_le_Bctl          -- :621 (`W^{-d} ≤ (lam² + 1) Bctl n u`, `0 ≤ u < 1`)
#check @RBM.Ind.s1_loop_det            -- :653 (model of `baFM_loop_det`)
-- Mathlib
#check @Matrix.IsHermitian.submatrix   -- Mathlib/LinearAlgebra/Matrix/Hermitian.lean:101
#check @Real.sqrt_le_sqrt              -- Mathlib/Analysis/Real/Sqrt.lean:209
#check @Real.sqrt_mul                  -- Mathlib/Analysis/Real/Sqrt.lean:366

namespace RBM.BA.T2238Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 2. Vocabulary and the pin (verbatim probe text; merged names) -/

/-- Route (A) family at time `u` (probe `:1252-1254`). -/
def BAFamZ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (z' : ℕ → ℂ) : Prop :=
  ∀ n, BAflowEs sz z' n = BAflowEs sz z n ∧
    min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz z' n ∧ BAflowT0 sz z' n ≤ BAflowT0 sz z n

/-- **(lRB1) is deterministic below `1 - c₁`** (probe `:1779-1784`). -/
def BATrivialLmax (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' →
          STLmaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (fun _ => 1 - c₁)

/-! ## 3. The public theorems of T2238 -/

/-- `BAflow_T0_bounds` (probe `:1285-1286`, binders as `∀`). -/
def BAflow_T0_bounds_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ,
    0 < (z n).im ∧ 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im ∧ 0 < BAflowT0 sz z n ∧ BAflowT0 sz z n < 1

/-- `BAFamZ_main` (probe `:1294`). -/
def BAFamZ_main_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ), BAFamZ sz z c₁ u z

/-- New: the coupling of a member of `Fam(0)` lies in the window `[√(1 - c₁) g₀, g₀]` of the main flow. -/
def BAFamZ_lam0_window_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
    ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' → ∀ n : ℕ,
      Real.sqrt (1 - c₁) * BAflowLam0 sz z n ≤ BAflowLam0 sz z' n ∧ BAflowLam0 sz z' n ≤ BAflowLam0 sz z n

/-- New: hence `Im m(E, g₀') ≥ κ` for the member's own carrier (`BAWinBulk` at `g' = g₀'`). -/
def BAFamZ_im_m_ge_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
    ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
      ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' → ∀ n : ℕ,
        κ ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im

/-- New: the deterministic loop bound of any BA carrier, `|𝓛^{(k)}_u| ≤ η⁻ᵏ (W^{-d})^{k-1}` when `0 < η ≤ Im z_u`
(the BA form of `s1_loop_det`; `norm_loopM_le_sharp`). -/
def baFM_loop_det_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u η : ℝ), 0 < η →
    η ≤ (ztOf (BAmF sz lam0 E n) (E n) u).im →
    ∀ k : ℕ, 1 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ),
      ‖(baFM sz lam0 E).L n u σ a ω‖ ≤ η⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1)

/-- The target. -/
def BATrivialLmax_holds_pin : Prop := ∀ d : ℕ, BATrivialLmax d

/-! ## 4. Statement shapes at concrete data (no proof obligation) -/

example : Prop := BATrivialLmax 3
example : Prop :=
  BAFamZ RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (1 / 3) (fun _ => 0) RBM.BA.FlowPinsInst.zSeq
example : Prop :=
  BAWinBulk RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (1 / 3) (1 / 2) →
    STLmaxgL (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
      (Sizes.seqP (Sizes.withLam RBM.Gauss.SizesInst.sz0 0)) (fun _ => 1 - 1 / 3)

end RBM.BA.T2238Check
