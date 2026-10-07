/-
Release check for T2300 (dispatcher V1, Tue Oct  6 13:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1), §98 (2),
§96 (2), §94 (3), §102, §90, §66, §65, §57 (1), §51, §45 O2, §29, §20, §18, §17, §16).
BA-C2 (block Anderson, gate BA; T2173 portmap P.3 row BA-C2, `docs/reports/T2173-portmap.md:274`): `RBM3D/BA/MReg.lean`,
the regularity of `m(·, λ)` and `ρ_N` on the bulk window, uniform in `L`, `λ`; proves the merged owed pin
`RBM.Univ.UNDensBARow'` (`RBM3D/BA/UNPins.lean:159`, not restated here: it is merged and unchanged).
Section 1: the merged names the proofs and the instances use (exact namespaces from the enclosing `namespace … end`
blocks; file:line and last commit on `main` f9e070b), and the Mathlib names of the route.
Section 2: the statements of the seven public theorems of T2300 as `*_pin : Prop` in the temporary namespace
`RBM.BA.T2300Check`; T2300 proves targets 1-5 in `RBM.BA`, targets 6-7 in `RBM.Univ`, under the name without `_pin`,
binders in this order.  Omitted: the private lemmas (prefix `MReg_`) and the instances (compiled in the file, namespace
`RBM.BA.MRegInst`).
Section 3: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Imports: `RBM3D.BA.ImmLower` (brings `Ward`, `CouplingWindow`, `MFixedPoint`), `RBM3D.BA.Boundary` (`BASelf_of_tendsto`),
`RBM3D.BA.UNPins` (`UNDensBARow'`; brings `PinsC2`, `PinsDens`, `Pins`, `Defs/Sizes`), and the Mathlib modules of the
Mathlib names checked in section 1.
Run from the main worktree: `lake env lean docs/tickets/checks/T2300-check.lean`.
-/
import RBM3D.BA.ImmLower
import RBM3D.BA.Boundary
import RBM3D.BA.UNPins
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Complex.Norm

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA` (`:43-836`)
#check @RBM.BA.BASelf
#check @RBM.BA.BAm
#check @RBM.BA.BArho
#check @RBM.BA.BAbulk
#check @RBM.BA.BAReal
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAm_self
#check @RBM.BA.BAm_eq_freeConvST
#check @RBM.BA.BAm_real_eq_of_self
#check @RBM.BA.BAbulk_iff_exists
-- `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA.MFixedPointInst` (`:838-994`)
#check @RBM.BA.MFixedPointInst.mS
#check @RBM.BA.MFixedPointInst.selfS
-- T2283 (P.9 row BA-D3 (Ward), b4fb28b): `RBM3D/BA/Ward.lean`, namespace `RBM.BA` (`:29-425`)
#check @RBM.BA.BAm_norm_le_one
-- T2227 (BA-D8, e1fec21): `RBM3D/BA/CouplingWindow.lean`, namespace `RBM.BA` (`:37-919`)
#check @RBM.BA.BAm_im_nonneg
#check @RBM.BA.BAself_im_le_one
-- `RBM3D/BA/CouplingWindow.lean`, namespace `RBM.BA.CouplingWindowInst` (`:840-917`)
#check @RBM.BA.CouplingWindowInst.EP
#check @RBM.BA.CouplingWindowInst.m0P
#check @RBM.BA.CouplingWindowInst.g0P
#check @RBM.BA.CouplingWindowInst.flowP_data
#check @RBM.BA.CouplingWindowInst.flowP_real
-- T2291 (BA-D7, 30f7ef8): `RBM3D/BA/ImmLower.lean`, namespace `RBM.BA` (`:46-432`)
#check @RBM.BA.BASelf_sub_le
#check @RBM.BA.BAm_im_ge_half
#check @RBM.BA.BAm_im_ge_mul
#check @RBM.BA.BAm_im_lower
#check @RBM.BA.BAm_im_lower_of_bulk
-- T2285 (BA-D6, f3e7c74): `RBM3D/BA/Boundary.lean`, namespace `RBM.BA` (`:47-349`)
#check @RBM.BA.BASelf_of_tendsto
#check @RBM.BA.BAm_im_tendsto_zero
#check @RBM.BA.BArho_tendsto
-- T2006 (MD-1, 0a873f1): `RBM3D/Defs/Sizes.lean`, namespace `RBM.Gauss` (`:36-248`), `Sizes` (`:148-246`)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.three_le_L
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.Sizes.Admissible
-- T2174 (UN-01, f8ad4b4): `RBM3D/Universality/Pins.lean`, namespace `RBM.Univ` (`:46-1900`)
#check @RBM.Univ.UNDens
-- T2201 (UN-01c, 3fc9d03): `RBM3D/Universality/PinsDens.lean`, namespace `RBM.Univ` (`:50-700`)
#check @RBM.Univ.UNDens'
#check @RBM.Univ.UNDens'.toUNDens
#check @RBM.Univ.unDens'_freeConvST
-- T2213 (UN-12b, 122f299): `RBM3D/Universality/PinsC2.lean`, namespace `RBM.Univ` (`:60-1709`)
#check @RBM.Univ.UNDens'.mono
-- T2241 (BA-C1b, 88d7676): `RBM3D/BA/UNPins.lean`, namespace `RBM.Univ` (`:55-308`), `RBM.BA.UNPinsInst` (`:765-871`),
-- `RBM.Univ.BAInst` (`:873-1312`)
#check @RBM.Univ.UNDensBARow'
#check @RBM.BA.UNPinsInst.fp
#check @RBM.BA.UNPinsInst.clsS
#check @RBM.BA.UNPinsInst.clsκ
#check @RBM.BA.UNPinsInst.clsκ_pos
#check @RBM.BA.UNPinsInst.cls_bulk
#check @RBM.Univ.BAInst.S0
#check @RBM.Univ.BAInst.S0_adm
#check @RBM.Univ.BAInst.S0_bulk
#check @RBM.Univ.BAInst.inst_univ_ba
#check @RBM.Univ.BAInst.inst_step1GoodC''_ba
-- Mathlib: Bolzano-Weierstrass in a proper space (`Mathlib/Topology/MetricSpace/Sequences.lean:38`, root namespace)
#check @tendsto_subseq_of_bounded
-- Mathlib: closed balls are bounded (`Mathlib/Topology/MetricSpace/Bounded.lean:73`, namespace `Metric`)
#check @Metric.isBounded_closedBall
-- Mathlib: `|Im w| ≤ ‖w‖`, `Im w ≤ ‖w‖` (`Mathlib/Analysis/Complex/Norm.lean:187,192`, namespace `Complex`)
#check @Complex.abs_im_le_norm
#check @Complex.im_le_norm

noncomputable section

namespace RBM.BA.T2300Check

open Filter Topology
open RBM RBM.Gauss RBM.BA RBM.Univ

/-! ## 2. The public theorems of T2300, as propositions -/

/-- `BAm_sub_le_of_im` (target 1, the modulus off the real axis): two points of the upper half plane where
`Im m ≥ c > 0` give `‖m(z) - m(z')‖ ≤ ‖z - z'‖ / c²` (from `BASelf_sub_le`; no `L`, `g`, `d` condition). -/
def BAm_sub_le_of_im_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g c : ℝ) (z z' : ℂ), 0 < c → 0 < z.im → 0 < z'.im →
    c ≤ (BAm d L g z).im → c ≤ (BAm d L g z').im →
      ‖BAm d L g z - BAm d L g z'‖ ≤ ‖z - z'‖ / c ^ 2

/-- `BAbulk_window` (target 2, the bulk window; "the bulk set is open", quantitatively): `ρ_N(E) ≥ κ` and
`|x - E| ≤ (πκ)³/8` give `ρ_N(x) ≥ κ/2`. -/
def BAbulk_window_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E x : ℝ), 0 < κ → BAbulk d L g κ E →
    |x - E| ≤ (Real.pi * κ) ^ 3 / 8 → BAbulk d L g (κ / 2) x

/-- `BArho_lip_of_bulk` (target 3, "`ρ_N` continuous", on the bulk): `|ρ_N(x) - ρ_N(y)| ≤ |x - y| / (π³κ²)`
for `x`, `y` in the `κ`-bulk. -/
def BArho_lip_of_bulk_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ x y : ℝ), 0 < κ → BAbulk d L g κ x → BAbulk d L g κ y →
    |BArho d L g x - BArho d L g y| ≤ |x - y| / (Real.pi ^ 3 * κ ^ 2)

/-- `BArho_rate_of_bulk` (target 4, the boundary value with a rate, no `3 ≤ L`, no `0 < g`):
`|π⁻¹ Im m(E + iη) - ρ_N(E)| ≤ 2η / (π³κ²)` in the `κ`-bulk. -/
def BArho_rate_of_bulk_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ), 0 < κ → BAbulk d L g κ E →
    ∀ η : ℝ, 0 < η →
      |(BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi - BArho d L g E| ≤
        2 * η / (Real.pi ^ 3 * κ ^ 2)

/-- `BAm_im_lower_window` (target 5): on the window `|x - E| ≤ (πκ)³/8`, `0 < η ≤ 10`,
`Im m(x + iη) ≥ (πκ)⁵/2048`. -/
def BAm_im_lower_window_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E x η : ℝ), 0 < κ → BAbulk d L g κ E →
    |x - E| ≤ (Real.pi * κ) ^ 3 / 8 → 0 < η → η ≤ 10 →
      (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g ((x : ℂ) + (η : ℂ) * Complex.I)).im

/-- `unDens'_ba` (target 6, in `RBM.Univ`): the density hypothesis `UNDens'` of the block Anderson datum
`m n = m(·, λ_n)`, `ρ n = ρ_N(E)` on every window `0 < δ ≤ (πκ)³/8`, from the eventual bulk at `E` alone
(no admissibility). -/
def unDens'_ba_pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ E : ℝ), 0 < κ →
    (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) →
    ∀ δ : ℝ, 0 < δ → δ ≤ (Real.pi * κ) ^ 3 / 8 →
      UNDens' (fun n => BAm d (sz.L n) (sz.lam n)) E (fun n => BArho d (sz.L n) (sz.lam n) E) δ

/-- `unDensBARow'_holds` (target 7, in `RBM.Univ`): the merged owed pin `UNDensBARow'` (`UNPins.lean:159`). -/
def unDensBARow'_holds_pin : Prop := UNDensBARow'

/-! ## 3. Statement shapes at concrete merged data (no proof obligation) -/

open RBM.BA.MFixedPointInst RBM.BA.CouplingWindowInst

-- (I1) the pin
example : Prop := UNDensBARow'
-- the `ρ`-bulk datum of the merged flow point (proved as in `RBM.BA.ImmLowerInst` (I4), `ImmLower.lean:456-468`)
example : Prop := BAbulk 3 4 g0P ((mS 4 10).im / Real.pi) EP
-- (I2) the window at the flow point
example : Prop :=
  ∀ x : ℝ, |x - EP| ≤ (Real.pi * ((mS 4 10).im / Real.pi)) ^ 3 / 8 →
    BAbulk 3 4 g0P ((mS 4 10).im / Real.pi / 2) x
-- (I3) the lower bound on the window at the flow point
example : Prop :=
  ∀ x η : ℝ, |x - EP| ≤ (Real.pi * ((mS 4 10).im / Real.pi)) ^ 3 / 8 → 0 < η → η ≤ 10 →
    (Real.pi * ((mS 4 10).im / Real.pi)) ^ 5 / 2048 ≤ (BAm 3 4 g0P ((x : ℂ) + (η : ℂ) * Complex.I)).im
-- (I4) `UNDens'` at the merged class sequence `S0` (`UNPins.lean:884`)
example : Prop :=
  ∃ E κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (Real.pi * κ) ^ 3 / 8 →
    UNDens' (fun n => BAm 3 ((RBM.Univ.BAInst.S0 : Sizes 3).L n) ((RBM.Univ.BAInst.S0 : Sizes 3).lam n)) E
      (fun n => BArho 3 ((RBM.Univ.BAInst.S0 : Sizes 3).L n) ((RBM.Univ.BAInst.S0 : Sizes 3).lam n) E) δ
-- the public theorems, as propositions
example : Prop := BAm_sub_le_of_im_pin ∧ BAbulk_window_pin ∧ BArho_lip_of_bulk_pin ∧ BArho_rate_of_bulk_pin
example : Prop := BAm_im_lower_window_pin ∧ unDens'_ba_pin ∧ unDensBARow'_holds_pin

end RBM.BA.T2300Check

end
