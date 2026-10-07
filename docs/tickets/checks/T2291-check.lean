/-
Release check for T2291 (dispatcher V1, Tue Oct  6 11:30 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1), §95 (4),
§94 (3), §93 (2), §90, §72, §58 (3), §57 (1), §51, §45 O2, §29, §20, §18, §17, §16).
BA-D7 (block Anderson, gate BA; T2161 split P.9, `docs/reports/T2161-portmap.md:1001`, `:1059`): `RBM3D/BA/ImmLower.lean`,
the lower bound on `Im m(E + iη)`, `η ∈ (0, 1]`, in the bulk; proves the merged pin `RBM.BA.BAImmLower`
(`MFixedPoint.lean:594`, not restated here: it is merged and unchanged).
Section 1: the merged names the proofs and the instances use (exact namespaces from the enclosing `namespace … end`
blocks; file:line and last commit on `main` e7d495b), and the Mathlib names of the route.
Section 2: the statements of the six public theorems of T2291 as `*_pin : Prop` in the temporary namespace
`RBM.BA.T2291Check`; T2291 proves each in `RBM.BA` under the name without `_pin`, binders in this order.
Omitted: the private lemmas (prefix `ImmLower_`) and the instances (compiled in the file, namespace `RBM.BA.ImmLowerInst`).
Section 3: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Imports: `RBM3D.BA.Ward` (`BAm_norm_le_one`; imports `RBM3D.BA.MFixedPoint`), `RBM3D.BA.CouplingWindow` (the instance
data `CouplingWindowInst`), and the Mathlib modules of the Mathlib names checked in section 1.
Run from the main worktree: `lake env lean docs/tickets/checks/T2291-check.lean`.
-/
import RBM3D.BA.Ward
import RBM3D.BA.CouplingWindow
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Norm

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA` (`:43-836`)
#check @RBM.BA.BAcard_Zd
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BAspec
#check @RBM.BA.BAm
#check @RBM.BA.BArho
#check @RBM.BA.BAward_avg
#check @RBM.BA.BAbulk
#check @RBM.BA.BAReal
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAImmLower
#check @RBM.BA.BAMB_trace_eq_sum
#check @RBM.BA.BASelf_iff_freeConv
#check @RBM.BA.BASelf_exists
#check @RBM.BA.BASelf_unique
#check @RBM.BA.baMExists_holds
#check @RBM.BA.BAm_self
#check @RBM.BA.BAm_real_eq_of_self
#check @RBM.BA.BAbulk_iff_exists
-- `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA.MFixedPointInst` (`:838-994`)
#check @RBM.BA.MFixedPointInst.wI
#check @RBM.BA.MFixedPointInst.mS
#check @RBM.BA.MFixedPointInst.zS
#check @RBM.BA.MFixedPointInst.selfS
#check @RBM.BA.MFixedPointInst.zS_im_pos
-- T2283 (P.9 row BA-D3 (Ward), b4fb28b): `RBM3D/BA/Ward.lean`, namespace `RBM.BA` (`:29-425`)
#check @RBM.BA.BAMB_diag_eq
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAm_norm_le_one
-- T2227 (BA-D8, e1fec21): `RBM3D/BA/CouplingWindow.lean`, namespace `RBM.BA` (`:37-919`)
#check @RBM.BA.BAgapReal
#check @RBM.BA.BAMB_trace_sq_eq_sum
#check @RBM.BA.BAgapReal_holds
#check @RBM.BA.BAm_im_nonneg
#check @RBM.BA.BAself_im_le_one
-- `RBM3D/BA/CouplingWindow.lean`, namespace `RBM.BA.CouplingWindowInst` (`:840-917`)
#check @RBM.BA.CouplingWindowInst.t0P
#check @RBM.BA.CouplingWindowInst.EP
#check @RBM.BA.CouplingWindowInst.m0P
#check @RBM.BA.CouplingWindowInst.g0P
#check @RBM.BA.CouplingWindowInst.flowP_data
#check @RBM.BA.CouplingWindowInst.g0P_pos
#check @RBM.BA.CouplingWindowInst.g0P_le
#check @RBM.BA.CouplingWindowInst.flowP_real
-- T2013 (868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, namespace `RBM.Gauss`; `RBM3D/Defs/Lattice.lean` (51f1a17), `RBM`
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Zd
-- Mathlib: Jensen for a finite average (`Mathlib/Algebra/Order/Chebyshev.lean:144`, root namespace)
#check @sq_sum_le_card_mul_sum_sq
-- Mathlib: `|Im w| ≤ ‖w‖`, `Im w ≤ ‖w‖` (`Mathlib/Analysis/Complex/Norm.lean:187,192`, namespace `Complex`)
#check @Complex.abs_im_le_norm
#check @Complex.im_le_norm

noncomputable section

namespace RBM.BA.T2291Check

open RBM RBM.Gauss RBM.BA

/-! ## 2. The public theorems of T2291, as propositions -/

/-- `BASelf_sub_le` (M2): the two-point stability estimate.  For solutions `m`, `m'` of `(self_m)` at `z`, `z'` with
`Im z, Im z' ≥ 0`: `(Im m² + Im m'²) ‖m − m'‖ ≤ 2 ‖z − z'‖` (no dimension, no `L`, no `g` condition). -/
def BASelf_sub_le_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z z' m m' : ℂ), 0 ≤ z.im → 0 ≤ z'.im →
    BASelf d L g z m → BASelf d L g z' m' →
      (m.im ^ 2 + m'.im ^ 2) * ‖m - m'‖ ≤ 2 * ‖z - z'‖

/-- `BAm_im_ge_half` (M3): near the real axis, `0 < η ≤ κ³/4`, the bulk value halves at most. -/
def BAm_im_ge_half_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m →
    ∀ η : ℝ, 0 < η → η ≤ κ ^ 3 / 4 →
      κ / 2 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im

/-- `BAm_im_ge_mul` (M4): every `η > 0`, `Im m(E + iη) ≥ η κ² / (η + 3)²` (from `⟨|v − E − m|⁻²⟩ = 1`). -/
def BAm_im_ge_mul_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m →
    ∀ η : ℝ, 0 < η →
      η * κ ^ 2 / (η + 3) ^ 2 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im

/-- `BAm_im_lower` (M5): the pin's conclusion at fixed `(L, g, E, m)` with `c = κ⁵/64`. -/
def BAm_im_lower_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m →
    ∀ η : ℝ, 0 < η → η ≤ 1 →
      κ ^ 5 / 64 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im

/-- `baImmLower_holds`: the merged pin `BAImmLower` (`MFixedPoint.lean:594`), proved at every `d`, `Λ`, `κ`. -/
def baImmLower_holds_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), BAImmLower d Λ κ

/-- `BAm_im_lower_of_bulk` (M6): the `ρ`-form (`BAbulk`, DECISIONS §51): `ρ_N(E) ≥ κ` gives `Im m(E + iη) ≥ (πκ)⁵/64`. -/
def BAm_im_lower_of_bulk_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ), 0 < κ → BAbulk d L g κ E →
    ∀ η : ℝ, 0 < η → η ≤ 1 →
      (Real.pi * κ) ^ 5 / 64 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im

/-! ## 3. Statement shapes at concrete merged data (no proof obligation) -/

open RBM.BA.MFixedPointInst RBM.BA.CouplingWindowInst

-- the pin at `d = 3`, `Λ = 10`, `κ = Im m_S` (the merged flow point has `g0P ≤ 10`, `g0P_le`)
example : Prop := BAImmLower 3 10 (mS 4 10).im
-- the bulk datum of the merged flow point (`flowP_real`, `CouplingWindow.lean:878`)
example : Prop := BAReal 3 4 g0P (mS 4 10).im EP m0P
-- (I2) the pin's conclusion there, `c = κ⁵/64`
example : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 → (mS 4 10).im ^ 5 / 64 ≤ (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im
-- (I3) the two-point estimate between the real point and `EP + iη`
example : Prop :=
  ∀ η : ℝ, 0 < η →
    (m0P.im ^ 2 + (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im ^ 2) *
        ‖m0P - BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)‖
      ≤ 2 * ‖(EP : ℂ) - ((EP : ℂ) + (η : ℂ) * Complex.I)‖
-- (I4) the `ρ`-form at the flow point
example : Prop := BAbulk 3 4 g0P ((mS 4 10).im / Real.pi) EP
-- the public theorems, as propositions
example : Prop := BASelf_sub_le_pin ∧ BAm_im_ge_half_pin ∧ BAm_im_ge_mul_pin
example : Prop := BAm_im_lower_pin ∧ baImmLower_holds_pin ∧ BAm_im_lower_of_bulk_pin

end RBM.BA.T2291Check

end
