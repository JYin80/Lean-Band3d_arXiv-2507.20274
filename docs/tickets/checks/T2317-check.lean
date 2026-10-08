/-
Release check for T2317 (dispatcher V1, Thu Oct  8 01:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §128, §108 (2),
§98 (2), §92 (1)(7), §72, §66 (5), §57 (1)(3), §52, §51, §29, §20, §18, §17, §16).
P.9 row BA-P2 (block Anderson, gate BA; `docs/reports/T2161-portmap.md:1003`, `:1061`): `RBM3D/BA/KKernel.lean`,
the kernel `K = M^{(+,-)}` of the block Anderson model (`K_ab = |M^{(B)}_ab|²`, `(eq:Msig)` `1_2:1070-1071`,
`A:18-19`, `A:59`) as a real matrix `BAK`, with: symmetry and translation invariance, double stochasticity (Ward,
`(eq:WardM)` `7_8:1869`), laziness `K_aa = |m|²` with `κ² ≤ |m|² ≤ 1`, exponential tails (the squares of
`(Mbound_AO)`/`(Mbound_AO2)`, `7_8:1891, 1902`; `BAMB_sq_off_le` of T2308) and the exponential moment
`Σ_b K_ab e^{μ|a-b|}`, the neighbour lower bound (small `g`, `BAMB_lower_small` of T2290) and, for every `g`, the
neighbour-sum identity `Σ_{b∼a} M_ab = (1 + (E+m)m)/g` with the lower bound `Σ_{b∼a} K_ab ≥ κ²(1-|m|²)²/(8dg²)`;
the bridge `M^{(+,-)} = BAK.map ofReal` to the merged `BAMss`/`BATheta`, and the Markov facts for the powers `K^n`.
No merged pin is discharged (plan row: "proves (pins): -"); the statements are new (`BAK…`).
Section 1: the merged names the proofs use (exact namespaces from the enclosing `namespace … end` blocks; file:line and
last commit on `main` e5f819c in the ticket header), and the Mathlib lemmas of the suggested route (modules imported).
Section 2: the definition `BAK`, in the temporary namespace `RBM.BA.T2317Check`; T2317 defines it in `RBM.BA` under the
same name with the same body (`rfl`-compared).
Section 3: the statements of the public theorems of T2317 as `*_pin : Prop` (explicit argument order = binder order).
Section 4: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2317-check.lean`.
-/
import RBM3D.BA.Prop5Short
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! ## 1. Merged names -/

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
#check @RBM.BA.BAMB_shift
#check @RBM.BA.BAMB_transpose
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAMB_diag_eq
#check @RBM.BA.BAMB_row_sq_real
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.BAMss_pp_apply
#check @RBM.BA.BAoffDiag_row_sum
-- `RBM3D/BA/Ward.lean`, namespace `RBM.BA.WardInst` (`:314-423`): the scalar instance `m = (3/5) i`, `κ = 1/2`
#check @RBM.BA.WardInst.ward_scalar_inst_norm
#check @RBM.BA.WardInst.ward_scalar_inst_im
-- T2290 (BA-D4, 1ba63a2): `RBM3D/BA/CombesThomas.lean`, namespace `RBM.BA` (`:35-672`)
#check @RBM.BA.BAct_C
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAct_C_pos
#check @RBM.BA.BAct_rate_pos
#check @RBM.BA.BAMB_resolvent_row
#check @RBM.BA.BAMB_upper_small
#check @RBM.BA.BAMB_lower_small
#check @RBM.BA.BAMB_decay_large
-- T2308 (BA-P1, 1d19466): `RBM3D/BA/Prop5Short.lean`, namespace `RBM.BA` (`:42-812`)
#check @RBM.BA.BAp5s_A
#check @RBM.BA.BAp5s_S
#check @RBM.BA.BAMss_ss_norm
#check @RBM.BA.BAMss_ss_diag
#check @RBM.BA.BAMss_row_offdiag_sum
#check @RBM.BA.BAMB_sq_off_le
#check @RBM.BA.BAsum_exp_decay_le
-- `RBM3D/Defs/RadialSum.lean` (320f7b0), namespace `RBM` (`:33-563`)
#check @RBM.expC
-- `RBM3D/Defs/Lattice.lean` (51f1a17), `RBM3D/Defs/Neighbours.lean`, namespace `RBM`
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.zdistD_neg
#check @RBM.zdistD_eq_zero_iff
#check @RBM.Adj
#check @RBM.card_adj
-- `RBM3D/Gauss/BlockAnderson.lean` (868b3b4), namespace `RBM.Gauss`
#check @RBM.Gauss.PsiB
-- Mathlib: `z * conj z = ‖z‖²`, `Im z ≤ ‖z‖`, transposes and powers, reindexing, Cauchy–Schwarz on a finset
#check @Complex.mul_conj'
#check @Complex.conj_mul'
#check @Complex.normSq_eq_norm_sq
#check @Complex.im_le_norm
#check @Complex.norm_real
#check @Matrix.conjTranspose_apply
#check @Matrix.transpose_apply
#check @Matrix.transpose_pow
#check @Matrix.mul_apply
#check @Matrix.map_apply
#check @Fintype.sum_equiv
#check @sq_sum_le_card_mul_sum_sq
#check @norm_sum_le
#check @Finset.add_sum_erase
#check @Finset.sum_comm
#check @Finset.mul_sum
#check @Real.exp_le_exp

noncomputable section

namespace RBM.BA.T2317Check

open RBM RBM.Gauss RBM.BA

/-! ## 2. The kernel (T2317 defines it in `RBM.BA` with exactly this body) -/

/-- The kernel `K = M^{(+,-)}` of the block Anderson model as a real matrix: `K_ab = |M^{(B)}_ab|²`
(`M^{(+,-)}_{ab} = M_{ba} conj(M_{ab})`, `(eq:Msig)` `1_2:1070-1071`; `M` symmetric), at the real-axis data
`(g, E, m)` of `BATheta`. -/
noncomputable def BAK (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) : Matrix (Zd d L) (Zd d L) ℝ :=
  Matrix.of fun a b => ‖BAMB d L g (E : ℂ) m a b‖ ^ 2

/-! ## 3. The public theorems of T2317 (statements) -/

/-- `BAK_apply` (definitional). -/
def BAK_apply_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (a b : Zd d L),
    BAK d L g E m a b = ‖BAMB d L g (E : ℂ) m a b‖ ^ 2

/-- `BAK_nonneg`: `0 ≤ K_ab` (any data). -/
def BAK_nonneg_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (a b : Zd d L), 0 ≤ BAK d L g E m a b

/-- `BAK_symm`: `K_ab = K_ba` (`BAMB_symm`; any data). -/
def BAK_symm_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (a b : Zd d L), BAK d L g E m a b = BAK d L g E m b a

/-- `BAK_transpose`: `Kᵀ = K`. -/
def BAK_transpose_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), Matrix.transpose (BAK d L g E m) = BAK d L g E m

/-- `BAK_shift`: translation invariance `K_{a+r,b+r} = K_ab` (`BAMB_shift`, `7_8:1857`). -/
def BAK_shift_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (a b r : Zd d L),
    BAK d L g E m (a + r) (b + r) = BAK d L g E m a b

/-- `BAK_zero_neg`: `K_{0,-a} = K_{0,a}` (shift + symmetry): the row `K_{0·}` is even. -/
def BAK_zero_neg_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (a : Zd d L), BAK d L g E m 0 (-a) = BAK d L g E m 0 a

/-- `BAMss_pm_eq`: the merged `M^{(+,-)}` is `K` read in `ℂ` (`M_{ba} conj(M_{ba}) = |M_{ba}|² = |M_{ab}|²`). -/
def BAMss_pm_eq_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ),
    BAMss d L (BAMB d L g (E : ℂ) m) true false = Matrix.map (BAK d L g E m) Complex.ofReal

/-- `BAMss_mp_eq`: the same for `M^{(-,+)}` (`conj(M_{ab}) M_{ab}`; no symmetry needed). -/
def BAMss_mp_eq_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ),
    BAMss d L (BAMB d L g (E : ℂ) m) false true = Matrix.map (BAK d L g E m) Complex.ofReal

/-- `BAMss_norm_eq_BAK`: `|M^{(σ₁,σ₂)}_{ab}| = K_ab` for all four charge pairs (`A:18`, with equality). -/
def BAMss_norm_eq_BAK_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d L),
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b‖ = BAK d L g E m a b

/-- `BATheta_pm_eq`: `Θ_t^{(+,-)} = (1 - tK)⁻¹` (`PropThetaQ` of the complexified `K`). -/
def BATheta_pm_eq_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ),
    BATheta d L g E m t true false = PropThetaQ (Matrix.map (BAK d L g E m) Complex.ofReal) t

/-- `BAK_diag`: laziness `K_aa = |m|²` (`BAMB_diag_eq`). -/
def BAK_diag_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → ∀ a : Zd d L,
    BAK d L g E m a a = ‖m‖ ^ 2

/-- `BAK_row_sum`: Ward, `Σ_b K_ab = 1` (`(eq:WardM)`, `BAMB_row_sq_real`). -/
def BAK_row_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → ∀ a : Zd d L,
    ∑ b, BAK d L g E m a b = 1

/-- `BAK_col_sum`: `Σ_a K_ab = 1` (symmetry): `K` is doubly stochastic. -/
def BAK_col_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → ∀ b : Zd d L,
    ∑ a, BAK d L g E m a b = 1

/-- `BAK_offdiag_sum`: `Σ_{b≠a} K_ab = 1 - |m|²` (row `a`; `BAoffDiag_row_sum` is the row `0` in `BAMss` form). -/
def BAK_offdiag_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → ∀ a : Zd d L,
    ∑ b ∈ Finset.univ.erase a, BAK d L g E m a b = 1 - ‖m‖ ^ 2

/-- `BAK_diag_bounds`: `κ² ≤ K_aa ≤ 1` in the bulk (`κ ≤ Im m ≤ |m| ≤ 1`). -/
def BAK_diag_bounds_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m → ∀ a : Zd d L,
    κ ^ 2 ≤ BAK d L g E m a a ∧ BAK d L g E m a a ≤ 1

/-- `BAK_pow_nonneg`: `0 ≤ (K^n)_ab`. -/
def BAK_pow_nonneg_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (n : ℕ) (a b : Zd d L), 0 ≤ (BAK d L g E m ^ n) a b

/-- `BAK_pow_row_sum`: `Σ_b (K^n)_ab = 1` (the walk of `A:59` has `n`-step transition matrix `K^n`). -/
def BAK_pow_row_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → ∀ (n : ℕ) (a : Zd d L),
    ∑ b, (BAK d L g E m ^ n) a b = 1

/-- `BAK_pow_transpose`: `(K^n)ᵀ = K^n`. -/
def BAK_pow_transpose_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (n : ℕ),
    Matrix.transpose (BAK d L g E m ^ n) = BAK d L g E m ^ n

/-- `BAK_pow_shift`: `(K^n)_{a+r,b+r} = (K^n)_ab`. -/
def BAK_pow_shift_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (n : ℕ) (a b r : Zd d L),
    (BAK d L g E m ^ n) (a + r) (b + r) = (BAK d L g E m ^ n) a b

/-- `BAK_off_le`: exponential tails for every `0 < g ≤ Λ`: `K_ab ≤ A g² e^{-2c|a-b|}` off the diagonal
(`A = BAp5s_A d Λ κ`, `c = BAct_rate d Λ κ`; this is `BAMB_sq_off_le` of T2308 in `K` form). -/
def BAK_off_le_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m → ∀ a b : Zd d L, a ≠ b →
      BAK d L g E m a b
        ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)))

/-- `BAK_le_small`: the square of the upper half of `(Mbound_AO)`, `g < (2C)⁻¹`: `K_ab ≤ (Cg)^{2|a-b|}`. -/
def BAK_le_small_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ →
    BAReal d L g κ E m → g < (2 * BAct_C d κ)⁻¹ → ∀ a b : Zd d L,
      BAK d L g E m a b ≤ (BAct_C d κ * g) ^ (2 * zdistD d L (a - b))

/-- `BAK_le_decay`: the square of `(Mbound_AO2)`, every `0 < g ≤ Λ`, all entries: `K_ab ≤ c⁻² e^{-2c|a-b|}`. -/
def BAK_le_decay_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m → ∀ a b : Zd d L,
      BAK d L g E m a b
        ≤ (BAct_rate d Λ κ)⁻¹ ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)))

/-- `BAK_exp_moment_le`: the exponential moment of the kernel, uniformly in `L` (`2 ≤ d`): for `0 ≤ μ ≤ c`,
`Σ_b K_ab e^{μ|a-b|} ≤ |m|² + A g² S`, `S = BAp5s_S d Λ κ = expC (d-2) c` (the input of the Esscher tilt, BA-P3/P4). -/
def BAK_exp_moment_le_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 2 ≤ d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal d L g κ E m → ∀ μ : ℝ, 0 ≤ μ → μ ≤ BAct_rate d Λ κ → ∀ a : Zd d L,
      ∑ b, BAK d L g E m a b * Real.exp (μ * (zdistD d L (a - b) : ℝ))
        ≤ ‖m‖ ^ 2 + BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ

/-- `BAK_adj_ge_small`: the neighbour lower bound of `(Mbound_AO)` squared, `g < (2C)⁻¹`: `(C⁻¹g)² ≤ K_ab`, `a ∼ b`. -/
def BAK_adj_ge_small_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ →
    BAReal d L g κ E m → g < (2 * BAct_C d κ)⁻¹ → ∀ a b : Zd d L, Adj d L a b →
      ((BAct_C d κ)⁻¹ * g) ^ 2 ≤ BAK d L g E m a b

/-- `BAMB_adj_sum`: the neighbour-sum identity, every `g > 0`: `Σ_{b∼a} M_ab = (1 + (E+m)m)/g`
(the diagonal entry of `(gΨ - E - m) M = 1`: `BAMB_resolvent_row` at `(a, a)`, with `M_aa = m` and `M_ca = M_ac`). -/
def BAMB_adj_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), 0 < g → BASelf d L g (E : ℂ) m → ∀ a : Zd d L,
    ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L a b), BAMB d L g (E : ℂ) m a b
      = (1 + ((E : ℂ) + m) * m) / (g : ℂ)

/-- `BAone_add_wm_ge`: the scalar lower bound `(κ/2)(1 - |m|²) ≤ |1 + (E+m)m|` for `κ ≤ Im m`, `|m| ≤ 1`
(`1 + (E+m)m = (1 - |m|²) + u Re m + i u Im m`, `u = E + 2 Re m`; split on `|u| ≤ (1-|m|²)/2`). -/
def BAone_add_wm_ge_pin : Prop :=
  ∀ (κ E : ℝ) (m : ℂ), 0 < κ → κ ≤ m.im → ‖m‖ ≤ 1 →
    κ / 2 * (1 - ‖m‖ ^ 2) ≤ ‖1 + ((E : ℂ) + m) * m‖

/-- `BAK_adj_sum_ge`: the neighbour-sum lower bound for every `g > 0` (no small-`g` restriction):
`Σ_{b∼a} K_ab ≥ (κ(1-|m|²))²/(8dg²)` (identity + scalar bound + Cauchy–Schwarz over the `2d` neighbours). -/
def BAK_adj_sum_ge_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ →
    BAReal d L g κ E m → ∀ a : Zd d L,
      (κ * (1 - ‖m‖ ^ 2)) ^ 2 / (8 * (d : ℝ) * g ^ 2)
        ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L a b), BAK d L g E m a b

/-! ## 4. Statement shapes at concrete merged data (no proof obligation) -/

-- Ward at the real-axis flow point `P` (`L = 4`, `g = P.g0 ≤ 10`, `E = P.E`, `m = P.m0`, `κ = Im m₀`): row `0`
example : Prop :=
  ∑ b, BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 0 b = 1
-- laziness at `P`
example : Prop :=
  BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 0 0
    = ‖(RBM.BA.MFixedPointInst.P).m0‖ ^ 2 ∧
  (RBM.BA.MFixedPointInst.P).m0.im ^ 2
    ≤ BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 0 0
-- the bridge to the merged propagator `Θ_{1/2}^{(+,-)}` at `P`
example : Prop :=
  BATheta 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0
      (1 / 2) true false
    = PropThetaQ (Matrix.map (BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E
        (RBM.BA.MFixedPointInst.P).m0) Complex.ofReal) (1 / 2)
-- the three-step kernel at `P` is stochastic
example : Prop :=
  ∑ b, (BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 ^ 3) 0 b
    = 1
-- the tail at `P`, entry `(0, (1,0,0))`, `Λ = 10`
example : Prop :=
  BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 0 ![1, 0, 0]
    ≤ BAp5s_A 3 10 (RBM.BA.MFixedPointInst.P).m0.im * (RBM.BA.MFixedPointInst.P).g0 ^ 2
        * Real.exp (-(2 * BAct_rate 3 10 (RBM.BA.MFixedPointInst.P).m0.im
            * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ)))
-- the exponential moment at `P`, `μ = c`, row `0`
example : Prop :=
  ∑ b, BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 0 b
      * Real.exp (BAct_rate 3 10 (RBM.BA.MFixedPointInst.P).m0.im * (zdistD 3 4 ((0 : Zd 3 4) - b) : ℝ))
    ≤ ‖(RBM.BA.MFixedPointInst.P).m0‖ ^ 2
      + BAp5s_A 3 10 (RBM.BA.MFixedPointInst.P).m0.im * (RBM.BA.MFixedPointInst.P).g0 ^ 2
        * BAp5s_S 3 10 (RBM.BA.MFixedPointInst.P).m0.im
-- the neighbour-sum identity and lower bound at `P`, row `0`
example : Prop :=
  ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b),
      BAMB 3 4 (RBM.BA.MFixedPointInst.P).g0 ((RBM.BA.MFixedPointInst.P).E : ℂ) (RBM.BA.MFixedPointInst.P).m0 0 b
    = (1 + (((RBM.BA.MFixedPointInst.P).E : ℂ) + (RBM.BA.MFixedPointInst.P).m0) * (RBM.BA.MFixedPointInst.P).m0)
        / ((RBM.BA.MFixedPointInst.P).g0 : ℂ)
example : Prop :=
  ((RBM.BA.MFixedPointInst.P).m0.im * (1 - ‖(RBM.BA.MFixedPointInst.P).m0‖ ^ 2)) ^ 2
      / (8 * (3 : ℝ) * (RBM.BA.MFixedPointInst.P).g0 ^ 2)
    ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b),
        BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 0 b
-- the small-`g` neighbour lower bound at `P` is an implication (no merged datum has a provable `g₀ < (2C)⁻¹`, T2290)
example : Prop :=
  (RBM.BA.MFixedPointInst.P).g0 < (2 * BAct_C 3 (RBM.BA.MFixedPointInst.P).m0.im)⁻¹ →
    ((BAct_C 3 (RBM.BA.MFixedPointInst.P).m0.im)⁻¹ * (RBM.BA.MFixedPointInst.P).g0) ^ 2
      ≤ BAK 3 4 (RBM.BA.MFixedPointInst.P).g0 (RBM.BA.MFixedPointInst.P).E (RBM.BA.MFixedPointInst.P).m0 0 ![1, 0, 0]
-- the scalar bound at the Ward scalar instance `κ = 1/2`, `m = (3/5) i`, `E = 0`
example : Prop :=
  (1 / 2 : ℝ) / 2 * (1 - ‖(3 / 5 : ℂ) * Complex.I‖ ^ 2)
    ≤ ‖1 + (((0 : ℝ) : ℂ) + (3 / 5 : ℂ) * Complex.I) * ((3 / 5 : ℂ) * Complex.I)‖
-- the public theorems, as propositions
example : Prop :=
  BAK_apply_pin ∧ BAK_nonneg_pin ∧ BAK_symm_pin ∧ BAK_transpose_pin ∧ BAK_shift_pin ∧ BAK_zero_neg_pin ∧
    BAMss_pm_eq_pin ∧ BAMss_mp_eq_pin ∧ BAMss_norm_eq_BAK_pin ∧ BATheta_pm_eq_pin
example : Prop :=
  BAK_diag_pin ∧ BAK_row_sum_pin ∧ BAK_col_sum_pin ∧ BAK_offdiag_sum_pin ∧ BAK_diag_bounds_pin ∧
    BAK_pow_nonneg_pin ∧ BAK_pow_row_sum_pin ∧ BAK_pow_transpose_pin ∧ BAK_pow_shift_pin
example : Prop :=
  BAK_off_le_pin ∧ BAK_le_small_pin ∧ BAK_le_decay_pin ∧ BAK_exp_moment_le_pin ∧ BAK_adj_ge_small_pin ∧
    BAMB_adj_sum_pin ∧ BAone_add_wm_ge_pin ∧ BAK_adj_sum_ge_pin

end RBM.BA.T2317Check

end
