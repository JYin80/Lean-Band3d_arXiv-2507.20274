module

public import RBM3D.Main.BandTerminal

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `RBM3D` named in its proof. The
definitions that occur in the statements are those of `RBM3D/MainDefs.lean`.
-/

section
namespace RBM.Endpoints

/-- Theorem 2.1: delocalization of the bulk eigenvectors; the statement is `RBM.Endpoints.decol`. -/
theorem theorem_2_1 : decol :=
  decol_holds

/-- Theorem 2.2: the local law, (2.14) and (2.15); the statement is `RBM.Endpoints.locSC`. -/
theorem theorem_2_2 : locSC :=
  locSC_holds

/-- Theorem 2.3: quantum unique ergodicity, (2.18) and (2.19); the statement is `RBM.Endpoints.QUE`. -/
theorem theorem_2_3 : QUE :=
  QUE_holds

/-- Theorem 2.5: quantum diffusion, (2.22)–(2.25); the statement is `RBM.Endpoints.QDiff`. -/
theorem theorem_2_5 : QDiff :=
  QDiff_holds

end RBM.Endpoints
end
