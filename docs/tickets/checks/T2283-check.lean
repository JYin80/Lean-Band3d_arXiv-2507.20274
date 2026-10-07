/-
Release check for T2283 (dispatcher V1, Tue Oct  6 10:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1), §90, §72,
§68, §66 (5), §58 (3), §57 (1)(3), §51, §29, §20, §18, §17, §16).
P.9 row BA-D3 (Ward) (block Anderson, gate BA; `docs/reports/T2161-portmap.md:998`, `:1056`): `RBM3D/BA/Ward.lean`,
proving the merged pins `BAWard` (`MFixedPoint.lean:558`), `BAoffDiag` (`:583`) and items (1)(2) of `BAPropM` (`:567`)
as the new pin `BAPropM12`, on top of T2189 (`RBM3D/BA/MFixedPoint.lean`, ae63e74).
Section 1: the merged names the proofs use (exact namespaces from the enclosing `namespace … end` blocks; file:line and
last commit on `main` 66cddb4 in the ticket header), and the Mathlib lemmas of the suggested route (modules imported).
Section 2: the new pin `BAPropM12`, as `def … : Prop` in the temporary namespace `RBM.BA.T2283Check`; T2283 defines it
in `RBM.BA` under the same name (same body; the `NeZero` proof may be the merged pins' tactic term: `rfl`-equal (proof irrelevance)).
Section 3: the statements of the public theorems of T2283 as `*_pin : Prop`.
Section 4: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2283-check.lean`.
-/
import RBM3D.BA.MFixedPoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA` (`:43-836`)
#check @RBM.BA.BAimInv_diag
#check @RBM.BA.BAcard_Zd
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BAPsi_isHermitian
#check @RBM.BA.BAward_avg
#check @RBM.BA.BAReal
#check @RBM.BA.BAMsigma
#check @RBM.BA.BAMss
#check @RBM.BA.BAWard
#check @RBM.BA.BAPropM
#check @RBM.BA.BAoffDiag
#check @RBM.BA.BASelf_unique
-- `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA.MFixedPointInst` (`:838-994`)
#check @RBM.BA.MFixedPointInst.mS
#check @RBM.BA.MFixedPointInst.zS
#check @RBM.BA.MFixedPointInst.selfS
#check @RBM.BA.MFixedPointInst.zS_im_pos
#check @RBM.BA.MFixedPointInst.FlowPt
#check @RBM.BA.MFixedPointInst.FlowPt.real
#check @RBM.BA.MFixedPointInst.FlowPt.g0_pos
#check @RBM.BA.MFixedPointInst.P
-- T2013 (868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, `RBM3D/Loop/GLoopFlow.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Gauss.Mres
-- `RBM3D/Defs/Lattice.lean` (51f1a17), `RBM3D/Analysis/Resolvent.lean` (6f9e0ba), namespace `RBM`
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.zdistD_neg
#check @RBM.Adj
#check @RBM.isUnit_sub_smul_of_isHermitian
-- Mathlib: the reindexing / transpose of a nonsingular inverse (`Ring.inverse` = `⁻¹` on matrices), the shift equiv,
-- the diagonal term of a row sum, `‖z‖² = normSq z`
#check @Matrix.inv_submatrix_equiv
#check @Matrix.transpose_nonsing_inv
#check @Matrix.nonsing_inv_eq_ringInverse
#check @Equiv.addRight
#check @Finset.add_sum_erase
#check @Complex.sq_norm

noncomputable section

namespace RBM.BA.T2283Check

open RBM RBM.Gauss RBM.BA

/-! ## 2. The new pin (T2283 defines it in `RBM.BA` with exactly this body) -/

section Pins

variable (d : ℕ)

/-- **Items (1)(2) of `lem:propM`** (`7_8:1853-1869`) on the real axis: translation invariance, `M_aa = m`,
Ward's identity `Σ_b |M_ab|² = 1` (`(eq:WardM)`), `|m| ≤ 1` — the first four conjuncts of the merged `BAPropM`
(`MFixedPoint.lean:573-575`) verbatim, under `BASelf` at a real energy instead of `BAReal` (no `κ`, no `C, c`).
The paper's `Im m ≳ 1` is the bulk premise `κ ≤ Im m` of `BAReal` (and `BAImmLower`, BA-D7), not a conjunct. -/
def BAPropM12 : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    BASelf d L g (E : ℂ) m →
      (∀ a b r : Zd d L, BAMB d L g (E : ℂ) m (a + r) (b + r) = BAMB d L g (E : ℂ) m a b) ∧
      (∀ a : Zd d L, BAMB d L g (E : ℂ) m a a = m) ∧
      (∀ a : Zd d L, ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1) ∧ ‖m‖ ≤ 1

end Pins

/-! ## 3. The public theorems of T2283 (statements) -/

/-- `BAMB_shift`: translation invariance, unconditional (`Ring.inverse` commutes with the reindexing
`Equiv.addRight r`; a singular matrix stays singular). -/
def BAMB_shift_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (a b r : Zd d L),
    BAMB d L g z m (a + r) (b + r) = BAMB d L g z m a b

/-- `BAMB_transpose`: `M^{(B)}` is complex symmetric (`Ψ^{(B)}` is real symmetric), unconditional. -/
def BAMB_transpose_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), Matrix.transpose (BAMB d L g z m) = BAMB d L g z m

/-- `BAMB_symm`: the entrywise form. -/
def BAMB_symm_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (a b : Zd d L), BAMB d L g z m a b = BAMB d L g z m b a

/-- `BAMB_diag_eq`: `M_aa = m` for a solution of `(self_m)` (any `z`). -/
def BAMB_diag_eq_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), BASelf d L g z m → ∀ a : Zd d L, BAMB d L g z m a a = m

/-- `BAMB_ward_row`: Ward's identity for each row, `0 ≤ Im z`. -/
def BAMB_ward_row_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), 0 ≤ z.im → BASelf d L g z m →
    ∀ a : Zd d L, (m.im + z.im) * ∑ b, ‖BAMB d L g z m a b‖ ^ 2 = m.im

/-- `baWard_holds`: the merged pin. -/
def baWard_holds_pin : Prop := ∀ d : ℕ, BAWard d

/-- `BAMB_row_sq_real`: `(eq:WardM)` at a real energy. -/
def BAMB_row_sq_real_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m →
    ∀ a : Zd d L, ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1

/-- `BAm_norm_le_one`: `|m| ≤ 1` for every `0 ≤ Im z` (`|m|² = |M_aa|² ≤ Σ_b |M_ab|² = Im m/(Im m + Im z)`). -/
def BAm_norm_le_one_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), 0 ≤ z.im → BASelf d L g z m → ‖m‖ ≤ 1

/-- `baPropM12_holds`: the new pin. -/
def baPropM12_holds_pin : Prop := ∀ d : ℕ, BAPropM12 d

/-- `BAnorm_one_sub_tm2_sq`: `|1 - t m²|² = (1 - t|m|²)² + 4t (Im m)²` (`A:32-34`; every real `t`). -/
def BAnorm_one_sub_tm2_sq_pin : Prop :=
  ∀ (t : ℝ) (m : ℂ), ‖1 - (t : ℂ) * m ^ 2‖ ^ 2 = (1 - t * ‖m‖ ^ 2) ^ 2 + 4 * t * m.im ^ 2

/-- `BAoffDiag_scalar`: the scalar inequalities of `(eq:off_diagM)` with `ε = κ²/4`. -/
def BAoffDiag_scalar_pin : Prop :=
  ∀ (κ t : ℝ) (m : ℂ), 0 < κ → κ ≤ m.im → ‖m‖ ≤ 1 → 0 ≤ t → t ≤ 1 →
    κ ^ 2 / 4 ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧ 1 - ‖m‖ ^ 2 ≤ (1 - κ ^ 2 / 4) * ‖1 - (t : ℂ) * m ^ 2‖

/-- `BAMss_pp_apply`: `M^{(+,+)}_{ab} = M_{ba} M_{ab}` (definitional). -/
def BAMss_pp_apply_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (M : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L),
    BAMss d L M true true a b = M b a * M a b

/-- `BAoffDiag_row_sum`: the left side of `(eq:off_diagM)` is exactly `1 - |m|²` at a real energy. -/
def BAoffDiag_row_sum_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m →
    ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖ = 1 - ‖m‖ ^ 2

/-- `BAoffDiag_of_real`: `(eq:off_diagM)` with the explicit `ε = κ²/4` at one datum (no `Λ`, no `3 ≤ d`). -/
def BAoffDiag_of_real_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    κ ^ 2 / 4 ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
      ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
        ≤ (1 - κ ^ 2 / 4) * ‖1 - (t : ℂ) * m ^ 2‖

/-- `baOffDiag_holds`: the merged pin. -/
def baOffDiag_holds_pin : Prop := ∀ (d : ℕ) (Λ κ : ℝ), BAoffDiag d Λ κ

/-! ## 4. Statement shapes at concrete merged data (no proof obligation) -/

-- the pins at `d = 3`, `Λ = 10` and the `κ` of the merged flow point `P` (`FlowPt 4 10`)
example : Prop := BAWard 3
example : Prop := BAPropM12 3
example : Prop := BAoffDiag 3 10 (RBM.BA.MFixedPointInst.P).m0.im
example : Prop := BAPropM 3 10 (RBM.BA.MFixedPointInst.P).m0.im
-- the conclusions at the real-axis point `P` (`L = 4`, `g = P.g0`, `E = P.E`, `m = P.m0`)
example : Prop :=
  ∀ a : Zd 3 4, BAMB 3 4 (RBM.BA.MFixedPointInst.P).g0 ((RBM.BA.MFixedPointInst.P).E : ℂ)
    (RBM.BA.MFixedPointInst.P).m0 a a = (RBM.BA.MFixedPointInst.P).m0
example : Prop :=
  ∑ a ∈ Finset.univ.erase (0 : Zd 3 4),
      ‖BAMss 3 4 (BAMB 3 4 (RBM.BA.MFixedPointInst.P).g0 ((RBM.BA.MFixedPointInst.P).E : ℂ)
        (RBM.BA.MFixedPointInst.P).m0) true true 0 a‖
    = 1 - ‖(RBM.BA.MFixedPointInst.P).m0‖ ^ 2
-- Ward for each row at the complex point `(z_S, m_S)` of `w = 6i/5` (`Im z > 0`, `L = 4`, `g = 10`)
example : Prop :=
  ∀ a : Zd 3 4, ((RBM.BA.MFixedPointInst.mS 4 10).im + (RBM.BA.MFixedPointInst.zS 4 10).im) *
      ∑ b, ‖BAMB 3 4 10 (RBM.BA.MFixedPointInst.zS 4 10) (RBM.BA.MFixedPointInst.mS 4 10) a b‖ ^ 2
    = (RBM.BA.MFixedPointInst.mS 4 10).im
-- the public theorems, as propositions
example : Prop := BAMB_shift_pin ∧ BAMB_transpose_pin ∧ BAMB_symm_pin ∧ BAMB_diag_eq_pin ∧ BAMB_ward_row_pin
example : Prop := baWard_holds_pin ∧ BAMB_row_sq_real_pin ∧ BAm_norm_le_one_pin ∧ baPropM12_holds_pin
example : Prop := BAnorm_one_sub_tm2_sq_pin ∧ BAoffDiag_scalar_pin ∧ BAMss_pp_apply_pin ∧ BAoffDiag_row_sum_pin
example : Prop := BAoffDiag_of_real_pin ∧ baOffDiag_holds_pin

end RBM.BA.T2283Check

end
