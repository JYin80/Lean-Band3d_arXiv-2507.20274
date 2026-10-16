/-
Release check for T2521 (MA-06b, the final shape; dispatcher V5, 2026-10-16 13:54 UTC; DECISIONS §358).
Part 1 (the release gate): merged names, checked with `docs/claude-team/tools/nsof.sh` on `main`.
Part 2 (proposals over merged names): the target texts `T2521_*`.
Part 3 (block comment): N2's `baThm27L_three` (T2520, `BA/UNBUniv`); activate after T2520 merges.
Statements only; no proofs.
Run: lake env lean docs/tickets/checks/T2521-check.lean
-/
import RBM3D.Main.BandTerminal
import RBM3D.BA.MAPins
-- ACTIVATE AFTER T2520 MERGES: import RBM3D.BA.UNBUniv

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

#check @RBM.Endpoints.band_terminal   -- Main/BandTerminal:104
#check @RBM.Endpoints.decol           -- Endpoints:165
#check @RBM.Endpoints.locSC           -- Endpoints:172
#check @RBM.Endpoints.QUE             -- Endpoints:182
#check @RBM.Endpoints.QDiff           -- Endpoints:197
#check @RBM.Endpoints.BUniv           -- Endpoints:209
#check @RBM.Univ.UNL32                -- Universality/Pins:281
#check @RBM.BA.BAThm27L               -- BA/MAPins:126
-- (not imported here: `RBM.BA.unMLOutBA_three`, BA/MainIndTermBA:47; read through N2) 

/-! ## Part 2: the target texts -/

namespace RBM.Endpoints.T2521Check

/-- Target 1: Theorem 2.7 at `d = 3`. -/
def T2521_Thm27 : Prop := RBM.BA.BAThm27L 3

/-- Target 2. -/
def T2521_Thm27OfL32 : Prop := RBM.Univ.UNL32 → T2521_Thm27

/-- Target 3: the final shape. -/
def T2521_FinalShape : Prop :=
  RBM.Univ.UNL32 →
    (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧
      T2521_Thm27

/-- The band half: `band_terminal` has exactly the type of the band conjunct of `T2521_FinalShape` (exact-type check, name only). -/
example : RBM.Univ.UNL32 →
    RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff :=
  RBM.Endpoints.band_terminal

end RBM.Endpoints.T2521Check

/- ACTIVATE AFTER T2520 MERGES (check the name on `main` with `nsof.sh`):
#check @RBM.BA.baThm27L_three
example : RBM.Endpoints.T2521Check.T2521_Thm27OfL32 := RBM.BA.baThm27L_three
-/
