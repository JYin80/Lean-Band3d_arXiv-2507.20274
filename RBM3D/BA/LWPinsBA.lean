/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.LWGen
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.LWExpTerm6
import RBM3D.BA.FlowPins

/-!
# The band instances and the BA readings of the generic light-weight pins (BA-L0, ticket T2394)

Design `docs/reports/T2387-design.md` §2 (LD2), §6 (row L0); probe `t/T2387:RBM3D/Probe/T2387Pins.lean:205-244, 305-322`.
This file sits downstream of the band theorems (`lwterm_holds`, `lwtermExp_holds`, `lwTermEXP_holds`,
`STLWB_of_LWterm`, `STLWT_of_LWtermExp`), which the chain files do not import.

* `baPin P` is `P` at the block Anderson data (law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon
  `BAflowT0`); `BAStep2 d` (`BA/FlowPins.lean:432`) is `baPin STStep2G d`.
* The BA readings `BALWterm`, `BALWtermExp`, `BALWtermEXP` (owner: BA-L6) and `BASTLWB`, `BASTLWT` (owner: T1-BA / T7-BA) are
  `Prop`-valued pins with no proof here.
* The band instances at `d = 3` are theorems (the merged band results, transported by `Iff.rfl`).
* The nonempty instances at the end apply the BA pins at the concrete data of `sz0` (`n = 0`: `L = 4`, `W = 32`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- BA: law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon `BAflowT0` (as `BAStep2`, `BA/FlowPins.lean:432`). -/
def baPin (P : PinFam) (d : ℕ) : Prop := P d (fun sz => Sizes.seqP (sz.withLam 0))
  (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-! ## 1. The BA readings (pins; no proof) -/

/-- `lem:LWterm` at the block Anderson data (owed: BA-L6). -/
abbrev BALWterm : ℕ → Prop := baPin LWtermG
/-- `lem: EWGn2_N` at the block Anderson data (owed: BA-L6). -/
abbrev BALWtermExp : ℕ → Prop := baPin LWtermExpG
/-- `lem:LWterm_EXP` at the block Anderson data (owed: BA-L6). -/
abbrev BALWtermEXP : ℕ → Prop := baPin LWtermEXPG
/-- `STLWB` at the block Anderson data (owed: T1-BA / T7-BA, through L5). -/
abbrev BASTLWB : ℕ → Prop := baPin STLWBgL
/-- `STLWT` at the block Anderson data (owed: T1-BA / T7-BA, through L5). -/
abbrev BASTLWT : ℕ → Prop := baPin STLWTgL

/-! ## 2. The generic pins at the band carrier are the merged theorems -/

theorem band_LWtermG : bandPin LWtermG 3 := (LWterm_iff 3).1 (lwterm_holds 3)
theorem band_LWtermExpG : bandPin LWtermExpG 3 := (LWtermExp_iff 3).1 (lwtermExp_holds 3)
theorem band_LWtermEXPG : bandPin LWtermEXPG 3 := (LWtermEXP_iff 3).1 (lwTermEXP_holds 3)
theorem band_STLWBgL : bandPin STLWBgL 3 := (STLWB_bandPin 3).1 (STLWB_of_LWterm (by norm_num) (lwterm_holds 3))
theorem band_STLWTgL : bandPin STLWTgL 3 := (STLWT_bandPin 3).1 (STLWT_of_LWtermExp (by norm_num) (lwtermExp_holds 3))

/-! ## 3. Nonempty instances at `d = 3`

Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `λ = 1/64`), flow `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2 ≤ BAflowT0`,
`ε₀ = 1/10`, `Ψ_n = W_n^{-1/2}` (window `W^{-3/2} ≤ Ψ ≤ W^{-1/10}`), `ℓ ≡ 0`, `D = 1`. -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

/-- `Ψ_n = W_n^{-1/2}` for `sz0`. -/
private def Ψ0 (n : ℕ) : ℝ := ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
private theorem Ψ0_window : ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ Ψ0 n ∧
    Ψ0 n ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) :=
  Eventually.of_forall fun n => ⟨Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz0.W_pos n) (by norm_num),
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz0.W_pos n) (by norm_num)⟩
private theorem ell0 (n : ℕ) : (0 : ℝ) ≤ (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 * ellT (sz0.L n) (sz0.lam n) (1 / 2) :=
  mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast sz0.W_pos n)) 10)
    (zero_le_one.trans (one_le_ellT (by exact_mod_cast (sz0.three_le_L n).trans' (by norm_num))))

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- The BA reading `BALWterm 3` is a `Prop` (its proof is BA-L6). -/
example : Prop := BALWterm 3

/-- `BALWtermExp 3` at the data above: every deterministic hypothesis is discharged; `(initialGT2)` and `(LW_assm_exp)` stay
hypotheses (other gates' pins). -/
example (h : BALWtermExp 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 0)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) Ψ0 (fun _ => 0)
    ⟨by norm_num, Ψ0_window, hI, fun _ => le_rfl, ell0, hL⟩ 1 one_pos

/-- `BASTLWT 3` at the data above. -/
example (h : BASTLWT 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
    (hL : ∀ D : ℝ, 0 < D → STLWassmExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) D (fun _ => 0)) :=
  h (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num) Ψ0 Ψ0_window hI (fun _ => 0)
    (Eventually.of_forall fun n => ⟨le_rfl, ell0 n⟩) hL 1 one_pos

/-- `BALWtermEXP 3` at the data above: the Step 1/2 bounds stay hypotheses. -/
example (h : BALWtermEXP 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hM hK hD
end Inst

end RBM.BA

end
