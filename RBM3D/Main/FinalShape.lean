/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.BandTerminal
import RBM3D.BA.UNBUniv
import RBM3D.BA.MAPins

set_option linter.style.longLine false

/-!
# The final shape (MA-06b, ticket T2521)

The project's final theorem: the band Theorems 2.1-2.5 (`band_terminal`, `Main/BandTerminal.lean:104`) together with the
block Anderson Theorem 2.7 (`MR:decol_BA`) at `d = 3`, conditional only on the borrowed `UNL32` (LSY arXiv:1609.09011
Thm 2.2).  No new mathematics: every conjunct is a merged theorem.

* `Thm27 := BAThm27L 3`: the five BA bullets in the order of `band_terminal` (decol, locSC, QUE, BUniv, QDiff).  The
  `d = 3` scope is Jun's decision B (D723); the general-`d` form is `baThm27L_any` under `STStep5IIIgL d`
  (`BA/UNBUniv`);
* `Thm27_of_L32 := baThm27L_three` (`BA/UNBUniv`);
* `final_shape : UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27`.

The compiled instances at the end apply every conjunct at concrete data (`d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)`); only
`UNL32` stays a hypothesis.
-/

namespace RBM.Endpoints

open RBM.Univ

/-- **Theorem 2.7 (`MR:decol_BA`) at `d = 3`**: `BAThm27L 3` (`BA/MAPins.lean:126`), the five BA bullets in the order of
`band_terminal`: decol, locSC, QUE, BUniv, QDiff.  The `d = 3` scope is Jun's decision B (D723); the general-`d` form is
`RBM.BA.baThm27L_any` under `STStep5IIIgL d`. -/
def Thm27 : Prop := RBM.BA.BAThm27L 3

/-- Theorem 2.7 at `d = 3` from the borrowed `UNL32` only: N2's `baThm27L_three` (`BA/UNBUniv`). -/
theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27 := RBM.BA.baThm27L_three

/-- **The final shape**: the paper's main results (band Thms 2.1-2.5, block Anderson Thm 2.7 at `d = 3`) with the single
external hypothesis `UNL32` (LSY arXiv:1609.09011 Thm 2.2). -/
theorem final_shape : RBM.Univ.UNL32 →
    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27 := fun h32 =>
  ⟨band_terminal h32, Thm27_of_L32 h32⟩

/-! ## Compiled nonempty instances (`d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)`)

Band conjuncts at `Inst.inst_*` (`Main/BandTerminal.lean` §Instances) on `sz0`; the five BA conjuncts at `S0`,
`κ_* = clsκ 4`, `E_*` in the bulk (`BA/MAPins.lean:213-224`).  Only `UNL32` stays a hypothesis. -/

section Instances

open RBM.Gauss.SizesInst RBM.Univ.UNInst

private theorem FinalShape_hg : (0 : ℝ) < 3 / 10 := by norm_num

/-- `decol` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_decol (final_shape h32).1.1

/-- `locSC` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_locSC (final_shape h32).1.2.1

/-- `QUE` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_QUE (final_shape h32).1.2.2.1

/-- `BUniv` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_BUniv (final_shape h32).1.2.2.2.1

/-- `QDiff` of `final_shape` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_QDiff (final_shape h32).1.2.2.2.2

section BAInstances

open RBM.BA.UNPinsInst RBM.Univ.BAInst RBM.BA

/-- The five BA conjuncts of `(final_shape h32).2` applied at `S0`, `κ_* = clsκ 4`, `E_*` in the bulk (as
`BA/MAPins.lean:213-224`); the QUE conjunct at `τ = 1/300`. -/
example (h32 : UNL32) : True := by
  have h := (final_shape h32).2
  have _ := h.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 10) 1 (clsκ_pos 4 FinalShape_hg) (by norm_num) (by norm_num)
  have _ := h.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg) (by norm_num)
    (by norm_num) (by norm_num)
  have _ := h.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (1 / 30) (1 / 60) (1 / 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have _ := h.2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm 1 le_rfl (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (fp 4 FinalShape_hg).E S0_bulk 0
    (by norm_num) UNInst.bump UNInst.bump_testFun
  have _ := h.2.2.2.2 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

/-- The whole `final_shape` at the instance data: all ten conjuncts at once, `UNL32` the only hypothesis. -/
example (h32 : UNL32) : True := by
  have h := final_shape h32
  have _ := Inst.inst_decol h.1.1
  have _ := Inst.inst_locSC h.1.2.1
  have _ := Inst.inst_QUE h.1.2.2.1
  have _ := Inst.inst_BUniv h.1.2.2.2.1
  have _ := Inst.inst_QDiff h.1.2.2.2.2
  have _ := h.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 10) 1 (clsκ_pos 4 FinalShape_hg) (by norm_num) (by norm_num)
  have _ := h.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg) (by norm_num)
    (by norm_num) (by norm_num)
  have _ := h.2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (1 / 30) (1 / 60) (1 / 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have _ := h.2.2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm 1 le_rfl (clsκ 4 FinalShape_hg) (clsκ_pos 4 FinalShape_hg) (fp 4 FinalShape_hg).E S0_bulk 0
    (by norm_num) UNInst.bump UNInst.bump_testFun
  have _ := h.2.2.2.2.2 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 FinalShape_hg) (1 / 20) (1 / 10) 2 (clsκ_pos 4 FinalShape_hg)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

end BAInstances

end Instances

end RBM.Endpoints
