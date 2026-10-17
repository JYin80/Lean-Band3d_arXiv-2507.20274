/-
Release check for T2534 (dispatcher V5, 2026-10-17 01:25 UTC; DECISIONS §372 (2) (ix)): the BA-D assembly pins `Thm27`, `final_shape`
and `baStep5III_holds_any` at exact type before its 1b.
Statements only: Prop-valued `example`s whose term is a name; no proofs.
Run: lake env lean docs/tickets/checks/T2534-check.lean
Part 1 compiles on `main` after T2533 (R1) merges. Part 2 was activated by the dispatcher at the merge 4b68c4cc (2026-10-17 08:45 UTC).
-/
import RBM3D

open RBM RBM.Gauss RBM.BA

namespace RBM.Endpoints.T2534Check

/-- The new `Thm27` (closing (ii)): Theorem 2.7 at every `d ≥ 3`. -/
def Thm27New : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d

/-- The new final shape: the single hypothesis `UNL32`. -/
def FinalShapeNew : Prop :=
  RBM.Univ.UNL32 →
    (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧ Thm27New

end RBM.Endpoints.T2534Check

-- Part 1 (R1's theorem at exact type, merged by T2533; and the d = 3 form R2 must keep):
example : ∀ d : ℕ, 3 ≤ d →
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  RBM.BA.baStep5III_holds_any
example : RBM.Univ.UNL32 → RBM.BA.BAThm27L 3 := RBM.BA.baThm27L_three
#check @RBM.BA.baThm27L_any

-- Part 2 (activated at the merge 4b68c4cc):
example : RBM.Endpoints.T2534Check.FinalShapeNew := RBM.Endpoints.final_shape
example : RBM.Univ.UNL32 → RBM.Endpoints.T2534Check.Thm27New := RBM.Endpoints.Thm27_of_L32
example : RBM.Univ.UNL32 → ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d := RBM.BA.baThm27L_all
