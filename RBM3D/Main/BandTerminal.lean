/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.BUnivHolds
import RBM3D.Main.ZNet
import RBM3D.Main.FixedZ
import RBM3D.Main.QUEFromQDiff
import RBM3D.Induction.MainIndHolds
import RBM3D.Universality.NormBand
import RBM3D.Universality.GUELocalSchur
import RBM3D.Universality.UnivMain

/-!
# The band terminal (MA-06a, ticket T2377)

The band main theorems of the paper, assembled from merged theorems and conditional only on the
borrowed `UNL32` (LSY arXiv:1609.09011 Thm 2.2):

* Thm 2.1 `decol_holds`, Thm 2.2 `locSC_holds`, Thm 2.3 `QUE_holds`, Thm 2.5 `QDiff_holds`: no
  hypothesis at all (`unMLOut_holds`, `Induction/MainIndHolds.lean`, closes the ST-6 input);
* Thm 2.4 `unBUniv_of_L32`, `BUniv_of_L32`: `UNL32` is the only hypothesis;
* `band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff`.

The Lean statements of the endpoints are frozen in `RBM3D/Endpoints.lean:165-209` and not edited.
There is no cycle: `locSC` and `QUE` do not use `UNBUniv`.  The registry edits of supervisor 0853
C1 and O3 are in `RBM3D/Test/Axioms.lean`.

`unOUQUE_holds` projects the first `𝐇_t` claim `UNOUQUE sz 𝔡 τU` for `0 < τU ≤ ouTauMax 𝔠 𝔡`.  The
type of `unOURow` (`UNOUClaims`) hides `τ₀` under an `∃`; the value `ouTauMax 𝔠 𝔡` is the one of its
proof `ouRow_of_pins`, and `unOUQUE_holds` takes it from the same two rows `g1Row`, `g2bRow`
directly (not through `unOURow`).

The compiled instances at the end apply the endpoints at the merged data `sz0`, `d = 3`,
`(𝔠, 𝔡) = (1/6, 1/10)` of `Endpoints.lean` §`Inst`; only `UNL32` stays a hypothesis.
-/

set_option linter.style.longLine false

namespace RBM.Endpoints

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-! ## The four unconditional endpoints -/

/-- **Thm 2.2 `MR:locSC`** from `unMLOut_holds`: `netLoc` (`Main/ZNet.lean:999`) at the fixed-`z` form
`locSCFixed_of_ML` (`Main/FixedZ.lean:100`). -/
theorem locSC_holds : locSC := netLoc (locSCFixed_of_ML unMLOut_holds)

/-- **Thm 2.5 `MR:QuDiff`** from `unMLOut_holds`: `netQD` (`Main/ZNet.lean:1024`) at `QDiffFixed_of_ML`
(`Main/FixedZ.lean:419`). -/
theorem QDiff_holds : QDiff := netQD (QDiffFixed_of_ML unMLOut_holds)

/-- **Thm 2.3 `MR:QUE`**: `QUE_of_QDiff` (`Main/QUEFromQDiff.lean:502`) at `QDiff_holds`. -/
theorem QUE_holds : QUE := QUE_of_QDiff QDiff_holds

/-- **Thm 2.1 `MR:decol`**: `decol_of_locSC` (`Main/FixedZ.lean:789`) at `locSC_holds`. -/
theorem decol_holds : decol := decol_of_locSC locSC_holds

/-! ## The consumed UN inputs and the `𝐇_t` claims -/

/-- The consumed pin `UNLocAvgBand` (`(G_bound_ave)`): the bridge `locSC_to_UNLocAvgBand`
(`Endpoints.lean:519`) at `locSC_holds`. -/
theorem unLocAvgBand_holds : UNLocAvgBand := locSC_to_UNLocAvgBand locSC_holds

/-- The consumed pin `UNQueBand` (`(Meq:QUE)` at `t = 0`): the bridge `QUE_to_UNQueBand`
(`Endpoints.lean:530`) at `QUE_holds`. -/
theorem unQueBand_holds : UNQueBand := QUE_to_UNQueBand QUE_holds

/-- The two `𝐇_t` claims `UNOUClaims`: `unOURow` (`Main/BUniv.lean:41`) at the three proved inputs. -/
theorem unOUClaims_holds : UNOUClaims := unOURow unMLOut_holds unLocAvgBand_holds unQueBand_holds

/-- **The first `𝐇_t` claim `UNOUQUE`** (`Pins.lean:637`) for `0 < τU ≤ τ₀`, `τ₀ = ouTauMax 𝔠 𝔡 = min (min (𝔠/12)
(𝔠𝔡/12)) (1/100)` (`ZeroModeProfile.lean:78`): `g2bRow` (`QUEFlow.lean:953`) at the second conjunct of `g1Row`
(`GUEPhase/RandomLayerB.lean:468`), `τ₀` is the one of `ouRow_of_pins` (`ZeroModeProfile.lean:719`).  The type of
`unOURow` hides `τ₀` (it is under the `∃` of `UNOUClaims`), so this is not a projection of `unOURow`. -/
theorem unOUQUE_holds : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOUQUE sz 𝔡 τU :=
  fun d hd 𝔠 𝔡 sz hA τU hτ hle =>
    g2bRow d hd 𝔠 𝔡 sz hA τU hτ hle
      (GUEPhase.g1Row unMLOut_holds unLocAvgBand_holds unQueBand_holds d hd 𝔠 𝔡 sz hA τU hτ hle).2

/-- The arithmetic row `UNClaimRowBA` of the block Anderson kind: `unClaimRowk` (`Universality/UnivMain.lean:466`)
at `K = UNKind.ba` (supervisor 0853 O4). -/
theorem unClaimRowBA_holds : UNClaimRowBA := unClaimRowk _

/-! ## Bulk universality (Thm 2.4) and the terminal -/

/-- **Thm 2.4 `B_Univ`** from the borrowed `UNL32` only: `bUniv_holds` (`Main/BUnivHolds.lean:227`) at the proved
rows `unNormBandRow` (`Universality/NormBand.lean:173`), `gueSchurTail` (`Universality/GUELocalSchur.lean:540`),
`unMLOut_holds`, `unLocAvgBand_holds`, `unQueBand_holds`. -/
theorem unBUniv_of_L32 : UNL32 → UNBUniv := fun h32 =>
  bUniv_holds unNormBandRow h32 unMLOut_holds unLocAvgBand_holds unQueBand_holds gueSchurTail

/-- The same with the head `BUniv` (`Endpoints.lean:209`, an `abbrev` of `UNBUniv`), which the premise scan of
`RBM3D/Test/Axioms.lean` reads. -/
theorem BUniv_of_L32 : UNL32 → BUniv := unBUniv_of_L32

/-- **The band terminal** (MA-06a): Thms 2.1-2.5 of the paper for the band model, conditional only on the borrowed
`UNL32`; four conjuncts are unconditional. -/
theorem band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff := fun h32 =>
  ⟨decol_holds, locSC_holds, QUE_holds, BUniv_of_L32 h32, QDiff_holds⟩

/-! ## Compiled nonempty instances (`d = 3`, `sz0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`)

`Inst.inst_*` (`Endpoints.lean` §7) apply an endpoint at the instance data: `decol` at `(τ, D) = (1/10, 1)`; `locSC`,
`QDiff` at `(ε, τ, D) = (1/20, 1/10, 2)`; `QUE` at `(ε₀, c, τ) = (1/30, 1/60, 1/10)`; `BUniv` at `k = 1`, `E = 0`,
`𝒪 = bump`.  Every deterministic hypothesis is discharged there; only `UNL32` stays a hypothesis here. -/

section Instances

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `decol` of `band_terminal` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_decol (band_terminal h32).1

/-- `locSC` of `band_terminal` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_locSC (band_terminal h32).2.1

/-- `QUE` of `band_terminal` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_QUE (band_terminal h32).2.2.1

/-- `BUniv` of `band_terminal` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_BUniv (band_terminal h32).2.2.2.1

/-- `QDiff` of `band_terminal` at the instance data. -/
example (h32 : UNL32) :=
  Inst.inst_QDiff (band_terminal h32).2.2.2.2

/-- The four unconditional endpoints at the instance data: no hypothesis. -/
example := And.intro (Inst.inst_decol decol_holds) (And.intro (Inst.inst_locSC locSC_holds)
  (And.intro (Inst.inst_QUE QUE_holds) (Inst.inst_QDiff QDiff_holds)))

/-- `unBUniv_of_L32` at the instance data (`k = 1`, `E = 0`, `𝒪 = bump`). -/
example (h32 : UNL32) :=
  Inst.inst_BUniv (unBUniv_of_L32 h32)

/-- The two bridges at the instance data, at the proved endpoints (no hypothesis). -/
example := And.intro (Inst.inst_bridge_loc locSC_holds) (Inst.inst_bridge_que QUE_holds)

/-- `unOUClaims_holds` at the instance data: the `𝐇_t` claims for some `τ₀ > 0` and all `0 < τU ≤ τ₀`. -/
example : ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUE sz0 (1 / 10) τU ∧ UNOUDiag sz0 τU :=
  unOUClaims_holds 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible

/-- `unOUQUE_holds` at the instance data: `ouTauMax (1/6) (1/10) = 1/720`, `τU = 1/1000`. -/
example : UNOUQUE sz0 (1 / 10) (1 / 1000) :=
  unOUQUE_holds 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (le_min (le_min (by norm_num) (by norm_num)) (by norm_num))

end Instances

end RBM.Endpoints
