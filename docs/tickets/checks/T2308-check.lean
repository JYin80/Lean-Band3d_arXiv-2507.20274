/-
Release check for T2308 (dispatcher V1, Tue Oct  6 14:45 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1), §98 (2),
§104 (1), §106 (2), §90, §66 (5), §58 (3), §57 (1)(3), §51, §29, §20, §18, §17, §16).
P.9 row BA-P1 (block Anderson, gate BA; `docs/reports/T2161-portmap.md:1002`, `:1060`): `RBM3D/BA/Prop5Short.lean`,
proving the merged pin `BAProp5s` (`FlowPins.lean:182`, `(prop:ThfadC_short)` for `Θ^{(σ,σ)}_t` of the block Anderson
model) unconditionally, from `BAoffDiag_scalar` (T2283, `Ward.lean:202`) and the Combes–Thomas bounds of T2290
(`BAMB_upper_small` `CombesThomas.lean:375`, `BAMB_decay_large` `:509`).
Section 1: the merged names the proofs use (exact namespaces from the enclosing `namespace … end` blocks; file:line and
last commit on `main` 4686e08 in the ticket header), and the Mathlib lemmas of the suggested route (modules imported).
Section 2: the four constants, as `def`s in the temporary namespace `RBM.BA.T2308Check`; T2308 defines them in `RBM.BA`
under the same names with the same bodies (`rfl`-compared).
Section 3: the statements of the public theorems of T2308 as `*_pin : Prop` (explicit argument order = binder order).
Section 4: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2308-check.lean`.
-/
import RBM3D.BA.FlowPins
import RBM3D.BA.CombesThomas
import RBM3D.Defs.RadialSum
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! ## 1. Merged names -/

-- T2197 (BA-C1a, b750bf3): `RBM3D/BA/FlowPins.lean`, namespace `RBM.BA` (`:902-962`, `:965-1133`) and
-- `RBM.BA.FlowPinsInst` (`:1136-1580`)
#check @RBM.BA.BAProp5s
#check @RBM.BA.BAProp5to8
#check @RBM.BA.FlowPinsInst.inst_BAProp5s
-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA` (`:43-836`)
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BAReal
#check @RBM.BA.BAMsigma
#check @RBM.BA.BAMss
#check @RBM.BA.BATheta
-- `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA.MFixedPointInst` (`:838-994`)
#check @RBM.BA.MFixedPointInst.FlowPt
#check @RBM.BA.MFixedPointInst.FlowPt.real
#check @RBM.BA.MFixedPointInst.FlowPt.g0_pos
#check @RBM.BA.MFixedPointInst.FlowPt.g0_le
#check @RBM.BA.MFixedPointInst.P
-- T2127 (b06ff9b): `RBM3D/Propagator/Pins.lean`, namespace `RBM` (`:27-285`)
#check @RBM.PropThetaQ
-- T2283 (P.9 row BA-D3 (Ward), b4fb28b): `RBM3D/BA/Ward.lean`, namespace `RBM.BA` (`:29-425`)
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAMB_diag_eq
#check @RBM.BA.BAMB_row_sq_real
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.BAnorm_one_sub_tm2_sq
#check @RBM.BA.BAoffDiag_scalar
#check @RBM.BA.BAMss_pp_apply
#check @RBM.BA.BAoffDiag_row_sum
-- T2290 (BA-D4, 1ba63a2): `RBM3D/BA/CombesThomas.lean`, namespace `RBM.BA` (`:35-672`)
#check @RBM.BA.BAct_C
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAct_C_pos
#check @RBM.BA.BAct_rate_pos
#check @RBM.BA.BAMB_upper_small
#check @RBM.BA.BAMB_decay_large
-- `RBM3D/Defs/RadialSum.lean` (320f7b0), namespace `RBM` (`:33-563`): the torus sum of `e^{-c|x|}`, uniformly in `L`
#check @RBM.expC
#check @RBM.sum_radial_exp_decay_le
#check @RBM.sum_shift
-- `RBM3D/Defs/Lattice.lean` (51f1a17), namespace `RBM`
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.zdistD_add_le
#check @RBM.zdistD_neg
#check @RBM.zdistD_eq_zero_iff
-- Mathlib: `Ring.inverse`, a maximiser on a finite type, convexity of `exp`, `Finset.erase`, `exp` monotone, `conj`
#check @Ring.inverse_non_unit
#check @Ring.mul_inverse_cancel
#check @Finite.exists_max
#check @convexOn_exp
#check @Finset.add_sum_erase
#check @Real.exp_le_exp
#check @Real.add_one_le_exp
#check @Complex.norm_conj
#check @Matrix.conjTranspose_apply

noncomputable section

namespace RBM.BA.T2308Check

open RBM RBM.Gauss RBM.BA

/-! ## 2. The constants (T2308 defines them in `RBM.BA` with exactly these bodies) -/

/-- `A = 4 (C/c)²` (`C = BAct_C d κ`, `c = BAct_rate d Λ κ`): `|M_xy|² ≤ A g² e^{-2c|x-y|}` for `x ≠ y`. -/
noncomputable def BAp5s_A (d : ℕ) (Λ κ : ℝ) : ℝ := 4 * (BAct_C d κ / BAct_rate d Λ κ) ^ 2

/-- `S = expC (d-2) c`: `Σ_x e^{-c|y-x|} ≤ S` on `Z_L^d`, uniformly in `L` (`RadialSum.lean:275`, `d = (d-2)+2`). -/
noncomputable def BAp5s_S (d : ℕ) (Λ κ : ℝ) : ℝ := RBM.expC (d - 2) (BAct_rate d Λ κ)

/-- The rate `μ = min c (ε² c / (2 A Λ² S))`, `ε = κ²/4` (the `ε` of `BAoffDiag_scalar`). -/
noncomputable def BAp5s_rate (d : ℕ) (Λ κ : ℝ) : ℝ :=
  min (BAct_rate d Λ κ) ((κ ^ 2 / 4) ^ 2 * BAct_rate d Λ κ / (2 * BAp5s_A d Λ κ * Λ ^ 2 * BAp5s_S d Λ κ))

/-- The constant `C₅ = 2/ε² + 2 A S/ε³`, `ε = κ²/4`. -/
noncomputable def BAp5s_C (d : ℕ) (Λ κ : ℝ) : ℝ :=
  2 / (κ ^ 2 / 4) ^ 2 + 2 * BAp5s_A d Λ κ * BAp5s_S d Λ κ / (κ ^ 2 / 4) ^ 3

/-! ## 3. The public theorems of T2308 (statements) -/

/-- `BAMss_ss_norm`: `|M^{(σ,σ)}_{xy}| = |M_xy|²` for both `σ` (any `z, m`; `BAMB_symm`, `‖star w‖ = ‖w‖`). -/
def BAMss_ss_norm_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y : Zd d L),
    ‖BAMss d L (BAMB d L g z m) σ σ x y‖ = ‖BAMB d L g z m x y‖ ^ 2

/-- `BAMss_ss_diag`: the diagonal of `M^{(σ,σ)}` is `m(σ)²` at a solution of `(self_m)`. -/
def BAMss_ss_diag_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), BASelf d L g z m → ∀ (σ : Bool) (y : Zd d L),
    BAMss d L (BAMB d L g z m) σ σ y y = (if σ then m else star m) ^ 2

/-- `BAnorm_one_sub_tq_sigma`: `|1 - t m(σ)²| = |1 - t m²|` (`t` real). -/
def BAnorm_one_sub_tq_sigma_pin : Prop :=
  ∀ (t : ℝ) (m : ℂ) (σ : Bool), ‖1 - (t : ℂ) * (if σ then m else star m) ^ 2‖ = ‖1 - (t : ℂ) * m ^ 2‖

/-- `BAMss_row_offdiag_sum`: every row of `M'^{(σ,σ)}` (diagonal removed) sums to `1 - |m|²` (Ward, row `y`). -/
def BAMss_row_offdiag_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → ∀ (σ : Bool) (y : Zd d L),
    ∑ x ∈ Finset.univ.erase y, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖ = 1 - ‖m‖ ^ 2

/-- `BAMB_sq_off_le`: off the diagonal, `|M_xy|² ≤ A g² e^{-2c|x-y|}` for every `0 < g ≤ Λ` (both branches of T2290). -/
def BAMB_sq_off_le_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m → ∀ x y : Zd d L, x ≠ y →
      ‖BAMB d L g (E : ℂ) m x y‖ ^ 2
        ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (x - y) : ℝ)))

/-- `BAsum_exp_decay_le`: `Σ_x e^{-c|y-x|} ≤ expC (d-2) c` on `Z_L^d`, `d ≥ 2`, uniformly in `L` and `y`. -/
def BAsum_exp_decay_le_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 2 ≤ d → ∀ c : ℝ, 0 < c → ∀ y : Zd d L,
    ∑ x : Zd d L, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) ≤ RBM.expC (d - 2) c

/-- `BApropQ_decay`: **the weighted `ℓ^∞` estimate** for `Θ = (1 - tQ)⁻¹` (`PropThetaQ`), `Q` with constant diagonal
`q`, gap `ε ≤ |1 - tq|` and weighted off-diagonal row sums `t Σ_{x≠y} e^{μ|y-x|}|Q_yx| ≤ (1 - ε/2)|1 - tq|`. -/
def BApropQ_decay_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (Q : Matrix (Zd d L) (Zd d L) ℂ) (q : ℂ) (t ε μ : ℝ),
    (∀ y, Q y y = q) → 0 < ε → ε ≤ ‖1 - (t : ℂ) * q‖ → 0 ≤ μ → 0 ≤ t →
    (∀ y, t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖
        ≤ (1 - ε / 2) * ‖1 - (t : ℂ) * q‖) →
    ∀ y a : Zd d L, ‖PropThetaQ Q t y a‖ ≤ 2 / ε ^ 2 * Real.exp (-(μ * (zdistD d L (y - a) : ℝ)))

/-- `BApropQ_offdiag`: off the diagonal the entry bound `|Q_yx| ≤ B e^{-2c|y-x|}` (`μ ≤ c`) gives the factor `B`. -/
def BApropQ_offdiag_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (Q : Matrix (Zd d L) (Zd d L) ℂ) (q : ℂ) (t ε μ B c S : ℝ),
    (∀ y, Q y y = q) → 0 < ε → ε ≤ ‖1 - (t : ℂ) * q‖ → 0 ≤ μ → 0 ≤ t → t ≤ 1 →
    (∀ y, t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖
        ≤ (1 - ε / 2) * ‖1 - (t : ℂ) * q‖) →
    0 ≤ B → μ ≤ c →
    (∀ y x : Zd d L, x ≠ y → ‖Q y x‖ ≤ B * Real.exp (-(2 * c * (zdistD d L (y - x) : ℝ)))) →
    (∀ y : Zd d L, ∑ x : Zd d L, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) ≤ S) →
    ∀ y a : Zd d L, y ≠ a →
      ‖PropThetaQ Q t y a‖ ≤ 2 * B * S / ε ^ 3 * Real.exp (-(μ * (zdistD d L (y - a) : ℝ)))

/-- `BAp5s_row_weighted`: the row hypothesis of `BApropQ_decay` for `Q = M^{(σ,σ)}` at a real-axis datum,
`μ = BAp5s_rate d Λ κ`, `ε = κ²/4`, every `t ∈ [0, 1]`. -/
def BAp5s_row_weighted_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 2 ≤ d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (σ : Bool) (y : Zd d L),
      t * ∑ x ∈ Finset.univ.erase y,
          Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ)) * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖
        ≤ (1 - κ ^ 2 / 4 / 2) * ‖1 - (t : ℂ) * (if σ then m else star m) ^ 2‖

/-- `BAp5s_C_pos`. -/
def BAp5s_C_pos_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), 0 < d → 0 < Λ → 0 < κ → 0 < BAp5s_C d Λ κ

/-- `BAp5s_rate_pos`. -/
def BAp5s_rate_pos_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), 0 < d → 0 < Λ → 0 < κ → 0 < BAp5s_rate d Λ κ

/-- `baProp5s_of_real`: the body of `BAProp5s` at one datum with `C := BAp5s_C d Λ κ`, `c := BAp5s_rate d Λ κ`,
for every `t ∈ [0, 1]` (the pin asks `t < 1`). -/
def baProp5s_of_real_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 2 ≤ d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ (σ : Bool) (a : Zd d L),
      ‖BATheta d L g E m t σ σ 0 a‖
        ≤ BAp5s_C d Λ κ * ((if a = 0 then (1 : ℝ) else 0)
            + g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * (zdistD d L a : ℝ)))

/-- `baProp5s_holds`: the merged pin. -/
def baProp5s_holds_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), BAProp5s d Λ κ

/-! ## 4. Statement shapes at concrete merged data (no proof obligation) -/

-- the pin at `d = 3`, `Λ = 10` and the `κ` of the merged flow point `P` (`FlowPt 4 10`)
example : Prop := BAProp5s 3 10 (RBM.BA.MFixedPointInst.P).m0.im
-- the hypothesis of the merged instance `inst_BAProp5s` (`FlowPins.lean:1222`) is that same proposition
example : Prop :=
  BAProp5s 3 10 (RBM.BA.MFixedPointInst.P).m0.im →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ‖BATheta 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0
          (1 / 2) true true 0 ![1, 0, 0]‖ ≤
        C * ((if (![1, 0, 0] : Zd 3 4) = 0 then (1 : ℝ) else 0) +
          (RBM.BA.MFixedPointInst.P).g0 ^ 2 * Real.exp (-c * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ)))
-- the explicit-constant bound at the real-axis point `P` (`L = 4`, `g = P.g0 ≤ 10`, `E = P.E`, `m = P.m0`,
-- `κ = Im m₀`), `t = 1/2`, `σ = -` (`false`)
example : Prop :=
  ∀ a : Zd 3 4,
    ‖BATheta 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0
        (1 / 2) false false 0 a‖
      ≤ BAp5s_C 3 10 (RBM.BA.MFixedPointInst.P).m0.im * ((if a = 0 then (1 : ℝ) else 0) +
          (RBM.BA.MFixedPointInst.P).g0 ^ 2 *
            Real.exp (-BAp5s_rate 3 10 (RBM.BA.MFixedPointInst.P).m0.im * (zdistD 3 4 a : ℝ)))
-- the torus sum at `d = 3`, `L = 4`, `c = 1/2`
example : Prop :=
  ∑ x : Zd 3 4, Real.exp (-((1 / 2 : ℝ) * (zdistD 3 4 (0 - x) : ℝ))) ≤ RBM.expC (3 - 2) (1 / 2)
-- the constants at `d = 3`, `Λ = 10`, `κ = 1/2`
example : Prop := 0 < BAp5s_C 3 10 (1 / 2) ∧ 0 < BAp5s_rate 3 10 (1 / 2)
-- the public theorems, as propositions
example : Prop :=
  BAMss_ss_norm_pin ∧ BAMss_ss_diag_pin ∧ BAnorm_one_sub_tq_sigma_pin ∧ BAMss_row_offdiag_sum_pin ∧
    BAMB_sq_off_le_pin ∧ BAsum_exp_decay_le_pin ∧ BApropQ_decay_pin
example : Prop :=
  BApropQ_offdiag_pin ∧ BAp5s_row_weighted_pin ∧ BAp5s_C_pos_pin ∧ BAp5s_rate_pos_pin ∧
    baProp5s_of_real_pin ∧ baProp5s_holds_pin

end RBM.BA.T2308Check

end
