/-
Release check for T2227 (dispatcher V1, Mon Oct  5 22:56 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §72, §68, §52, §51,
§45 O2, §29, §20, §17, §16).
BA-D8 (block Anderson, gate BA; T2205 portmap row BA-D8, `docs/reports/T2205-portmap.md:64`): `RBM3D/BA/CouplingWindow.lean`,
the coupling window of the BA flow, moved from the compiled T2205 probe (`git show 96e4087:RBM3D/Probe/T2205Pins.lean`,
branch `t/T2205`, sections 2, 2.1-2.3, 3.2 and the one-point instances 7.2) into the namespace `RBM.BA`
(instances: `RBM.BA.CouplingWindowInst`), on top of the merged T2189 file `RBM3D/BA/MFixedPoint.lean` (ae63e74).
Section 1: the merged names the moved text uses (exact namespaces; file:line and last commit on `main` cd6fcba).
Section 2: the three deterministic pins (`BAgapReal`, `BAmWindow`, `BAzztE_inv`; probe `:493-521` = T2205 check `:135-163`)
and the window vocabulary (`BAWinBulk` written out with merged names = T2205 check `:172-176`; `BAWinBulk_of_dom_stmt`
= probe `:1264-1268`), as `def … : Prop` in the temporary namespace `RBM.BA.T2227Check`; T2227 defines each in `RBM.BA`
under the same name.
Section 3: the statements of the public theorems of T2227 as `*_pin : Prop` (the probe's binders turned into `∀` binders,
otherwise verbatim).  Omitted: the private lemmas `T2205_inv_spectral`, `abs_eigenvalue_le`, `BASelf_iff_fixed`,
`inv_mul_inv_sub_le`, `norm_inv_le_of_abs_im` (the verbatim criterion of the ticket covers them) and the instances (probe
`example`s, compiled in the file).
Section 4: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Imports: `RBM3D.BA.MFixedPoint` (its import closure, 42 RBM3D modules, holds every merged name of section 1; unchanged
since the probe base cef761a: `git diff --stat cef761a cd6fcba -- <closure> lean-toolchain lake-manifest.json lakefile.toml`
is empty) and `Mathlib.Topology.MetricSpace.Contracting` (the one Mathlib module the probe imports for these blocks).
Run from the main worktree: `lake env lean docs/tickets/checks/T2227-check.lean`.
-/
import RBM3D.BA.MFixedPoint
import Mathlib.Topology.MetricSpace.Contracting

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA` (`:43-836`)
#check @RBM.BA.BAcard_Zd
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BAPsi_isHermitian
#check @RBM.BA.BAt0
#check @RBM.BA.BAflowE
#check @RBM.BA.BAt0_pos
#check @RBM.BA.BAzztE_data
#check @RBM.BA.BAspec
#check @RBM.BA.BAm
#check @RBM.BA.BAReal
#check @RBM.BA.BAdom
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAdom_real
#check @RBM.BA.BAg0_le
#check @RBM.BA.BAMB_trace_eq_sum
#check @RBM.BA.BASelf_iff_freeConv
#check @RBM.BA.BASelf_unique
#check @RBM.BA.BAm_self
#check @RBM.BA.BAm_real_eq_of_self
-- `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA.MFixedPointInst` (`:838-994`)
#check @RBM.BA.MFixedPointInst.mS
#check @RBM.BA.MFixedPointInst.zS
#check @RBM.BA.MFixedPointInst.selfS
#check @RBM.BA.MFixedPointInst.zS_im_pos
#check @RBM.BA.MFixedPointInst.FlowPt
#check @RBM.BA.MFixedPointInst.P
-- T2013 (868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, `RBM3D/Loop/GLoopFlow.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.Mres
-- T2006 (0a873f1): `RBM3D/Defs/Sizes.lean`; T2012 (9e2b00f): `RBM3D/Defs/StochDomAt.lean`
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.L
#check @RBM.Gauss.Sizes.lam
#check @RBM.Gauss.Sizes.three_le_L
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.one_le_size
#check @RBM.Gauss.SizesInst.sz0
-- `RBM3D/Defs/Lattice.lean` (51f1a17), `RBM3D/Defs/Neighbours.lean` (be709a6), `RBM3D/Analysis/Resolvent.lean` (6f9e0ba)
#check @RBM.Zd
#check @RBM.Adj
#check @RBM.card_adj
#check @RBM.isUnit_sub_smul_of_isHermitian
-- Mathlib (`Mathlib/Topology/MetricSpace/Contracting.lean`): the fixed point of `BAwindow_step`
#check @ContractingWith.exists_fixedPoint'

noncomputable section

namespace RBM.BA.T2227Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 2. The pins and the window vocabulary (T2227 defines each in `RBM.BA` with exactly this body) -/

section DetPins

variable (d : ℕ)

/-- The stability gap on the real axis (probe `:493`; proved by `BAgapReal_holds`). -/
def BAgapReal : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    BASelf d L g (E : ℂ) m →
      2 * m.im ^ 2 ≤
        (1 - (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g (E : ℂ) m * BAMB d L g (E : ℂ) m).trace).re

/-- `m(E, ·)` on the coupling window (probe `:504`; proved by `BAmWindow_holds`). -/
def BAmWindow (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ g' : ℝ, Real.sqrt (1 - c₁) * g ≤ g' → g' ≤ g →
          BAReal d L g' (κ / 2) E (BAm d L g' (E : ℂ)) ∧ ‖BAm d L g' (E : ℂ) - m‖ ≤ C * (g - g')

/-- The inverse of `zztE_BA` (probe `:514`; proved by `BAzztE_inv_holds`). -/
def BAzztE_inv : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (τ E : ℝ) (m₀ : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    0 < τ → τ < 1 → BASelf d L (Real.sqrt τ * g) (E : ℂ) m₀ →
      BAm d L g (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) = (Real.sqrt τ : ℂ) * m₀ ∧
        BAt0 (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = τ ∧
          BAflowE (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = E

end DetPins

/-- The window `[√(1 - c₁) g₀, g₀]` lies in the κ-bulk at the energy `E` (T2205 check `:172-176`: the probe's
`BAWinBulk` `:1242-1244` with T2197's `BAflowLam0`, `BAflowEs` written out; the two agree by `rfl`, probe `:3974`). -/
def BAWinBulk {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) : Prop :=
  ∀ (n : ℕ) (g' : ℝ),
    Real.sqrt (1 - c₁) * (Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n) ≤ g' →
    g' ≤ Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n →
    κ ≤ (BAm d (sz.L n) g' (BAflowE (z n) (BAm d (sz.L n) (sz.lam n) (z n)) : ℂ)).im

/-- From the chain domain: the window is in the `κ/2`-bulk (probe `:1264`; proved by `BAWinBulk_of_dom_holds`). -/
def BAWinBulk_of_dom_stmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ Λ : ℝ, 0 < κ → 0 < Λ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
      ∀ (ε : ℝ) (sz : Sizes d) (z : ℕ → ℂ), (∀ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ) →
        (∀ n, BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)) → BAWinBulk sz z c₁ (κ / 2)

/-! ## 3. The public theorems of T2227 (statements; consumers in the ticket) -/

/-- `BAMB_trace_sq_eq_sum` (probe `:568`): the public spectral form of `tr (M^{(B)})²`. -/
def BAMB_trace_sq_eq_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    (BAMB d L g z m * BAMB d L g z m).trace = ∑ i, (((BAspec d L g i : ℂ) - (z + m))⁻¹) ^ 2

/-- `BAgapReal_holds` (probe `:597`). -/
def BAgapReal_holds_pin : Prop := ∀ d : ℕ, BAgapReal d

/-- `BAzztE_inv_core` (probe `:676`; BA-S3 uses it, probe `:1461`). -/
def BAzztE_inv_core_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g τ E : ℝ) (m₀ : ℂ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hself : BASelf d L (Real.sqrt τ * g) (E : ℂ) m₀),
    BAm d L g (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) = (Real.sqrt τ : ℂ) * m₀ ∧
      BAt0 (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = τ ∧
        BAflowE (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = E

/-- `BAzztE_inv_holds` (probe `:740`). -/
def BAzztE_inv_holds_pin : Prop := ∀ d : ℕ, BAzztE_inv d

/-- `BAm_im_nonneg` (probe `:756`; BA-S3 uses it, probe `:1932`). -/
def BAm_im_nonneg_pin : Prop :=
  ∀ {d L : ℕ} [NeZero L] {g : ℝ} {z : ℂ}, 0 ≤ (BAm d L g z).im

/-- `BAself_im_le_one` (probe `:764`; BA-S3 uses it, probe `:1971`, `:1973`). -/
def BAself_im_le_one_pin : Prop :=
  ∀ {d L : ℕ} [NeZero L] {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m), m.im ≤ 1

/-- `BAwindow_step` (probe `:884`): the one Newton-Kantorovich step of the window. -/
def BAwindow_step_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {g g' E κ : ℝ} (hκ : 0 < κ) (hg : 0 < g)
    {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (hκm : κ ≤ m.im) (hg' : g' ≤ g) (hδ : g - g' ≤ κ ^ 9 / (64 * d)),
    ∃ m' : ℂ, BASelf d L g' (E : ℂ) m' ∧ ‖m' - m‖ ≤ 2 * d * (g - g') / κ ^ 4 ∧ κ / 2 ≤ m'.im

/-- `BAmWindow_holds` (probe `:1124`). -/
def BAmWindow_holds_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), BAmWindow d Λ κ

/-- `BAwindow_iter` (probe `:1159`): the step iterated at a floor `κf`. -/
def BAwindow_iter_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {E κf : ℝ} (hκf : 0 < κf),
    ∀ (N : ℕ) {g g' : ℝ}, 0 < g' → g' ≤ g → g - g' ≤ N * (κf ^ 9 / (64 * d)) →
      ∀ {m : ℂ}, BASelf d L g (E : ℂ) m → κf + 2 * d * (g - g') / κf ^ 4 ≤ m.im →
        ∃ m' : ℂ, BASelf d L g' (E : ℂ) m' ∧ ‖m' - m‖ ≤ 2 * d * (g - g') / κf ^ 4 ∧ κf ≤ m'.im

/-- `BAwindow_floor` (probe `:1214`; BA-S3 uses it in `sz0_win`, probe `:3490`). -/
def BAwindow_floor_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {g g' E κ κf : ℝ} (hκf : 0 < κf)
    (hg' : 0 < g') (hle : g' ≤ g) {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (hκm : κ ≤ m.im)
    (hbudget : κf + 2 * d * (g - g') / κf ^ 4 ≤ κ),
    κf ≤ (BAm d L g' (E : ℂ)).im ∧ ‖BAm d L g' (E : ℂ) - m‖ ≤ 2 * d * (g - g') / κf ^ 4

/-- `BAWinBulk_of_dom` (probe `:1359`). -/
def BAWinBulk_of_dom_pin : Prop :=
  ∀ (d : ℕ) (hw : ∀ Λ κ : ℝ, BAmWindow d Λ κ), BAWinBulk_of_dom_stmt d

/-- `BAWinBulk_of_dom_holds` (probe `:1378`; BA-V3, BA-M1 apply it on a tail, T2205d = D538; BA-S3 at `sz0`, probe `:3598`). -/
def BAWinBulk_of_dom_holds_pin : Prop := ∀ d : ℕ, BAWinBulk_of_dom_stmt d

/-! ## 4. Statement shapes at concrete merged data (no proof obligation) -/

-- the deterministic pins at `d = 3`, `Λ = 10` and the `κ` of the merged flow point `P` (`FlowPt 4 10`)
example : Prop := BAgapReal 3
example : Prop := BAmWindow 3 10 (RBM.BA.MFixedPointInst.P).m0.im
example : Prop := BAzztE_inv 3
-- the window vocabulary along the merged sequence `sz0`
example : Prop := BAWinBulk RBM.Gauss.SizesInst.sz0 (fun _ => Complex.I) (1 / 10) (1 / 10)
example : Prop := BAWinBulk_of_dom_stmt 3
-- the public theorems, as propositions
example : Prop := BAMB_trace_sq_eq_sum_pin ∧ BAzztE_inv_core_pin ∧ BAm_im_nonneg_pin ∧ BAself_im_le_one_pin
example : Prop := BAwindow_step_pin ∧ BAwindow_iter_pin ∧ BAwindow_floor_pin ∧ BAWinBulk_of_dom_pin
example : Prop := BAgapReal_holds_pin ∧ BAzztE_inv_holds_pin ∧ BAmWindow_holds_pin ∧ BAWinBulk_of_dom_holds_pin

end RBM.BA.T2227Check

end
