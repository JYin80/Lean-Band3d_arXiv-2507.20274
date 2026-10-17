/-
Release check for T2533 (dispatcher V5, 2026-10-17 01:25 UTC; DECISIONS §372 (2) (i), (iii)): BA-D row R1.
Statements only: `#check` and Prop-valued `example`s whose term is a name; no proofs.
Run: lake env lean docs/tickets/checks/T2533-check.lean
Part 1 compiles on `main` before the row and on `t/T2533` after. Part 2 was activated by the dispatcher at the merge feb83715 (2026-10-17 08:24 UTC).
-/
import RBM3D

open RBM RBM.Gauss RBM.BA

namespace RBM.BA.T2533Check

/-- The target of R1 (closing condition (i)): case (iii) of Step 5 at the BA tuple for every `d ≥ 3`. -/
def Target : Prop :=
  ∀ d : ℕ, 3 ≤ d → STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

end RBM.BA.T2533Check

-- Part 1: unchanged by R1.
example : STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  RBM.BA.baStep5III_holds
example : RBM.Univ.UNL32 → RBM.BA.BAThm27L 3 := RBM.BA.baThm27L_three
#check @RBM.BA.baThm27L_any
#check @RBM.Endpoints.final_shape

-- Part 2 (activated at the merge feb83715):
example : RBM.BA.T2533Check.Target := RBM.BA.baStep5III_holds_any
