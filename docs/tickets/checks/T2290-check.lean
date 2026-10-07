/-
Release check for T2290 (dispatcher V1, Tue Oct  6 11:30 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1), §93 (2),
§95, §90, §72 (1), §66 (5), §58 (3), §57 (1)(3), §51, §29, §20, §18, §17, §16).
P.9 row BA-D4 (block Anderson, gate BA; `docs/reports/T2161-portmap.md:999`, `:1057`): `RBM3D/BA/CombesThomas.lean`,
proving the merged pin `BAPropM` (`MFixedPoint.lean:567`, all items) from `baPropM12_holds` (T2283, `Ward.lean:183`)
and the Combes–Thomas item (3) (`(Mbound_AO)`, `(Mbound_AO2)`, `7_8:1888-1904`), unconditionally.
Section 1: the merged names the proofs use (exact namespaces from the enclosing `namespace … end` blocks; file:line and
last commit on `main` e7d495b in the ticket header), and the Mathlib lemmas of the suggested route (modules imported).
Section 2: the two constants, as `def`s in the temporary namespace `RBM.BA.T2290Check`; T2290 defines them in `RBM.BA`
under the same names with the same bodies (`rfl`-compared).
Section 3: the statements of the public theorems of T2290 as `*_pin : Prop` (explicit argument order = binder order).
Section 4: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2290-check.lean`.
-/
import RBM3D.BA.Ward
import RBM3D.Defs.Neighbours
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA` (`:43-836`)
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BAPsi_isHermitian
#check @RBM.BA.BAReal
#check @RBM.BA.BAPropM
-- `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA.MFixedPointInst` (`:838-994`)
#check @RBM.BA.MFixedPointInst.wI
#check @RBM.BA.MFixedPointInst.mS
#check @RBM.BA.MFixedPointInst.zS
#check @RBM.BA.MFixedPointInst.selfS
#check @RBM.BA.MFixedPointInst.zS_im_pos
#check @RBM.BA.MFixedPointInst.FlowPt
#check @RBM.BA.MFixedPointInst.FlowPt.real
#check @RBM.BA.MFixedPointInst.FlowPt.g0_pos
#check @RBM.BA.MFixedPointInst.FlowPt.g0_le
#check @RBM.BA.MFixedPointInst.P
-- T2283 (P.9 row BA-D3 (Ward), b4fb28b): `RBM3D/BA/Ward.lean`, namespace `RBM.BA` (`:29-425`)
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAMB_diag_eq
#check @RBM.BA.BAMB_row_sq_real
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.BAPropM12
#check @RBM.BA.baPropM12_holds
-- T2013 (868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, `RBM3D/Loop/GLoopFlow.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Gauss.Mres
-- `RBM3D/Defs/Lattice.lean` (51f1a17), `RBM3D/Defs/Neighbours.lean` (be709a6), namespace `RBM`
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.zdistD_eq_zero_iff
#check @RBM.zdistD_add_le
#check @RBM.zdistD_neg
#check @RBM.Adj
#check @RBM.card_adj
-- `RBM3D/Analysis/Resolvent.lean` (6f9e0ba), namespace `RBM`: the `ℓ²` lower bound (no `Matrix` norm instance)
#check @RBM.norm_sub_smul_ge_of_isHermitian
#check @RBM.isUnit_sub_smul_of_isHermitian
#check @RBM.norm_inverse_entry_le
-- Mathlib: the `ℓ²` norm of `EuclideanSpace` and its coordinates, Cauchy–Schwarz for finsets, `exp`/`log`
#check @EuclideanSpace.norm_eq
#check @EuclideanSpace.norm_sq_eq
#check @EuclideanSpace.single
#check @EuclideanSpace.norm_single
#check @PiLp.norm_apply_le
#check @Finset.sum_mul_sq_le_sq_mul_sq
#check @Real.add_one_le_exp
#check @Real.exp_log
#check @Real.log_pos

noncomputable section

namespace RBM.BA.T2290Check

open RBM RBM.Gauss RBM.BA

/-! ## 2. The constants (T2290 defines them in `RBM.BA` with exactly these bodies) -/

/-- The constant `C` of `(Mbound_AO)` (`7_8:1888-1891`; "depending only on `d` and `κ`"): `C = 16 d² / κ³`. -/
def BAct_C (d : ℕ) (κ : ℝ) : ℝ := 16 * (d : ℝ) ^ 2 / κ ^ 3

/-- The rate `c` of `(Mbound_AO2)` (`7_8:1902`): `c = min (log (1 + κ/(4dΛ))) (κ/2)` (depends on `d, Λ, κ`, §18). -/
def BAct_rate (d : ℕ) (Λ κ : ℝ) : ℝ := min (Real.log (1 + κ / (4 * (d : ℝ) * Λ))) (κ / 2)

/-! ## 3. The public theorems of T2290 (statements) -/

/-- `BAzdist_adj_lip`: `x ↦ |x - b|` is 1-Lipschitz along edges (any `L`). -/
def BAzdist_adj_lip_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (x y b : Zd d L), Adj d L x y → zdistD d L (x - b) ≤ zdistD d L (y - b) + 1

/-- `BAMB_resolvent_row`: the entries of `(gΨ - w) M = 1`, `w = z + m`, `Im w ≠ 0`. -/
def BAMB_resolvent_row_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 → ∀ a b : Zd d L,
    (g : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), BAMB d L g z m c b
        - (z + m) * BAMB d L g z m a b = if a = b then 1 else 0

/-- `BAMB_ct_core`: **the Combes–Thomas estimate** for `M = (gΨ - w)⁻¹`, `Im w ≥ κ`, weight `e^{ν|x - b|}`. -/
def BAMB_ct_core_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → ∀ (g κ ν : ℝ) (z m : ℂ), 0 ≤ g → 0 < κ → κ ≤ (z + m).im → 0 ≤ ν →
    2 * (d : ℝ) * g * (Real.exp ν - 1) ≤ κ / 2 → ∀ a b : Zd d L,
      ‖BAMB d L g z m a b‖ ≤ 2 / κ * Real.exp (-(ν * (zdistD d L (a - b) : ℝ)))

/-- `BAct_C_pos`. -/
def BAct_C_pos_pin : Prop := ∀ (d : ℕ) (κ : ℝ), 0 < d → 0 < κ → 0 < BAct_C d κ

/-- `BAct_rate_pos`. -/
def BAct_rate_pos_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), 0 < d → 0 < Λ → 0 < κ → 0 < BAct_rate d Λ κ

/-- `BAMB_upper_small`: the upper half of `(Mbound_AO)` at a real-axis datum, `g < (2C)⁻¹`. -/
def BAMB_upper_small_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ →
    BAReal d L g κ E m → g < (2 * BAct_C d κ)⁻¹ → ∀ a b : Zd d L,
      ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_C d κ * g) ^ zdistD d L (a - b)

/-- `BAMB_lower_small`: the lower half of `(Mbound_AO)` (nearest neighbours), `g < (2C)⁻¹`. -/
def BAMB_lower_small_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ →
    BAReal d L g κ E m → g < (2 * BAct_C d κ)⁻¹ → ∀ a b : Zd d L, Adj d L a b →
      (BAct_C d κ)⁻¹ * g ≤ ‖BAMB d L g (E : ℂ) m a b‖

/-- `BAMB_decay_large`: `(Mbound_AO2)` at a real-axis datum, for every `0 < g ≤ Λ`. -/
def BAMB_decay_large_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m → ∀ a b : Zd d L,
      ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))

/-- `BAPropM3_of_real`: item (3) of `BAPropM` (its last two conjuncts, verbatim with `C := BAct_C d κ`,
`c := BAct_rate d Λ κ`) at one datum. -/
def BAPropM3_of_real_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m →
      (g < (2 * BAct_C d κ)⁻¹ → ∀ a b : Zd d L,
        (BAct_C d κ)⁻¹ * g * (if Adj d L a b then 1 else 0) ≤ ‖BAMB d L g (E : ℂ) m a b‖ ∧
          ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_C d κ * g) ^ zdistD d L (a - b)) ∧
      ((2 * BAct_C d κ)⁻¹ ≤ g → ∀ a b : Zd d L,
        ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)))

/-- `baPropM_holds`: the merged pin, all items. -/
def baPropM_holds_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), BAPropM d Λ κ

/-! ## 4. Statement shapes at concrete merged data (no proof obligation) -/

-- the pin at `d = 3`, `Λ = 10` and the `κ` of the merged flow point `P` (`FlowPt 4 10`)
example : Prop := BAPropM 3 10 (RBM.BA.MFixedPointInst.P).m0.im
-- `(Mbound_AO2)` at the real-axis point `P` (`L = 4`, `g = P.g0 ≤ 10`, `E = P.E`, `m = P.m0`, `κ = Im m₀`)
example : Prop :=
  ∀ a b : Zd 3 4,
    ‖BAMB 3 4 (RBM.BA.MFixedPointInst.P).g0 ((RBM.BA.MFixedPointInst.P).E : ℂ) (RBM.BA.MFixedPointInst.P).m0 a b‖
      ≤ (BAct_rate 3 10 (RBM.BA.MFixedPointInst.P).m0.im)⁻¹ *
        Real.exp (-BAct_rate 3 10 (RBM.BA.MFixedPointInst.P).m0.im * (zdistD 3 4 (a - b) : ℝ))
-- the Combes–Thomas core at the complex point `(z_S, m_S)` (`z_S + m_S = w_I = 6i/5`, `g = 10`, `ν = log (1 + 1/100)`)
example : Prop :=
  ∀ a b : Zd 3 4,
    ‖BAMB 3 4 10 (RBM.BA.MFixedPointInst.zS 4 10) (RBM.BA.MFixedPointInst.mS 4 10) a b‖
      ≤ 2 / (6 / 5) * Real.exp (-(Real.log (1 + 1 / 100) * (zdistD 3 4 (a - b) : ℝ)))
example : Prop := (6 / 5 : ℝ) ≤ (RBM.BA.MFixedPointInst.zS 4 10 + RBM.BA.MFixedPointInst.mS 4 10).im
example : Prop := 2 * ((3 : ℕ) : ℝ) * 10 * (Real.exp (Real.log (1 + 1 / 100)) - 1) ≤ (6 / 5 : ℝ) / 2
-- the constants at `d = 3`, `κ = 1/2`, `Λ = 10`
example : Prop := 0 < BAct_C 3 (1 / 2) ∧ 0 < BAct_rate 3 10 (1 / 2)
-- the public theorems, as propositions
example : Prop := BAzdist_adj_lip_pin ∧ BAMB_resolvent_row_pin ∧ BAMB_ct_core_pin ∧ BAct_C_pos_pin ∧ BAct_rate_pos_pin
example : Prop :=
  BAMB_upper_small_pin ∧ BAMB_lower_small_pin ∧ BAMB_decay_large_pin ∧ BAPropM3_of_real_pin ∧ baPropM_holds_pin

end RBM.BA.T2290Check

end
