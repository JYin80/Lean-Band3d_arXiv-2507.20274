/-
Release check for T2312 (dispatcher V1, Wed Oct  7 10:07 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §123).
Gate LW-13b-1 (identity twin): `RBM3D/Graph/LWMomExpD.lean` (new file), theorem `lwMomExp_valOnD_eq_valOn`.
Section 1: merged names the proof uses, with exact namespaces (file:line on `main`).
Section 2: the new constant (the pin) in the temporary namespace `RBM.Graph.T2312Check`.
  T2312 defines it in `RBM.Graph` (LWMomExpD.lean).
Section 3: the public theorem shape as `_pin : Prop`.
Section 4: Prop-valued example.
Statements and `#check` only: no proof, no tactic block. Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2312-check.lean`.
-/
import RBM3D.Graph.LWMomExp

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- T2281 (LW-13a Near): `RBM3D/Graph/LWMomExp.lean`, namespace `RBM.Graph`
#check @RBM.Graph.lwMomExp_valOnD
#check @RBM.Graph.lwMomExp_nearD
#check @RBM.Graph.AnpDetNearAt
#check @RBM.Graph.AnpDetNear
#check @RBM.Graph.lwMomExp_near
-- T2289 (LW-13c Far): `RBM3D/Graph/LWMomExpFar.lean`, namespace `RBM.Graph`
-- (imported transitively through AnpKey6 / AuxGraph; check directly)
#check @RBM.Graph.NGraph.valOn
-- AnpKey6.lean: `RBM3D/Graph/AnpKey6.lean`, namespace `RBM.Graph`
#check @RBM.Graph.anpKey6_w
#check @RBM.Graph.anpKey6_val_eq

noncomputable section

namespace RBM.Graph.T2312Check

open RBM RBM.Graph NGraph

/-! ## 2. New constant: the identity twin pin -/

/-- **LW-13b-1 identity twin** (`7_8:1636`, DECISIONS §123): the domain-restricted value
`lwMomExp_valOnD Γ ξ a b D` equals `NGraph.valOn` restricted to `D^q = piFinset D`.
Declared here without proof (this check file contains no proofs). -/
def lwMomExp_valOnD_eq_valOn_pin : Prop :=
  ∀ {p q : ℕ} {ι : Type*}
    (Γ : NGraph p q) (ξ : ι → ι → ℝ) (a b : Fin p → ι) (D : Finset ι),
    lwMomExp_valOnD Γ ξ a b D =
      Γ.valOn ξ a b (Fintype.piFinset (fun _ : Fin q => D))

/-! ## 3. Public theorem shape -/

def identity_twin_pin : Prop := lwMomExp_valOnD_eq_valOn_pin

/-! ## 4. Prop-valued example -/

example : Prop := identity_twin_pin

end RBM.Graph.T2312Check

end
