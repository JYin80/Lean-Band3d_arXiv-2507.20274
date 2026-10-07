/-
Release check for T2311 (dispatcher V1, Wed Oct  7 08:xx UTC 2026; CLAUDE.md §4 step 0; DECISIONS §116).
Gate LW-14e-3 (Sim): `RBM3D/Graph/LWExpSim.lean` (new file), theorems `partitionSim` and `childrenSim`.
Section 1: merged names the proofs use, with exact namespaces (file:line on `main`).
Section 2: the new constants (verbatim probe text from t/T2288:RBM3D/Probe/T2288Cert.lean) in the
  temporary namespace `RBM.Graph.T2311Check`; T2311 defines them in `RBM.Graph` (LWExpSim.lean).
  `Cand.toR` is declared as `axiom` here (its implementation uses proof term `cands_spec`, proved in
  LWExpSim.lean; the axiom does not appear in the main build — this file is never imported or merged).
Section 3: the two public theorem shapes as `_pin : Prop`.
Section 4: Prop-valued example.
Statements and `#check` only: no proof, no tactic block. Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2311-check.lean`.
-/
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.LWExpCert

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- T2306 (LW-14e-1 Cert): `RBM3D/Graph/LWExpCert.lean`, namespace `RBM.Graph.LWCert` (`:35`)
#check @RBM.Graph.LWCert.MNode
#check @RBM.Graph.LWCert.cMerge
#check @RBM.Graph.LWCert.cPartition
#check @RBM.Graph.LWCert.Cand
#check @RBM.Graph.LWCert.cands
#check @RBM.Graph.LWCert.fams
#check @RBM.Graph.LWCert.renum
#check @RBM.Graph.LWCert.labsOf
#check @RBM.Graph.LWCert.goodB
-- T2307 (LW-14e-2 Term5): `RBM3D/Graph/LWExpTerm5.lean`, namespace `RBM.Gauss.Sizes` (`:51`)
#check @RBM.Gauss.Sizes.lwSplitLoopsX
#check @RBM.Gauss.Sizes.lwSplitLoopsX_spec
#check @RBM.Gauss.Sizes.pcomp
#check @RBM.Gauss.Sizes.partitionX
#check @RBM.Gauss.Sizes.val_eq_partitionX
#check @RBM.Gauss.Sizes.RCand
#check @RBM.Gauss.Sizes.RCand.kids
-- `RBM3D/Graph/LWGGExp.lean`, namespace `RBM.Graph` (`:56`)
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.oe2xR4
#check @RBM.Graph.oe2xR5
#check @RBM.Graph.oe2xR6
#check @RBM.Graph.oe2xR7
#check @RBM.Graph.oe2xR8
-- `RBM3D/Graph/LWWeightExp.lean`, namespace `RBM.Graph` (`:51`)
#check @RBM.Graph.owxT1
-- `RBM3D/Graph/LWStein.lean`, namespace `RBM.Graph` (`:82`)
#check @RBM.Graph.lwSplit

noncomputable section

namespace RBM.Graph.T2311Check

open RBM RBM.Graph RBM.Graph.LWCert RBM.Gauss.Sizes

/-! ## 2. New constants (verbatim probe text from t/T2288:RBM3D/Probe/T2288Cert.lean) -/

/-- `MNode.toP` (probe 457-463): pack a model node as a `PGraph (Fin 2)`. -/
def MNode.toP (N : MNode) (h : Function.Surjective N.ext) : PGraph (Fin 2) where
  E' := Fin (N.a + 1)
  I' := Fin N.b
  ext := N.ext
  ext_surj := h
  g := N.g

/-- `Rel` (probe 465-472): simulation relation between a model node and a packed graph. -/
def Rel (N : MNode) (P : PGraph (Fin 2)) : Prop :=
  ∃ (eE : Fin (N.a + 1) ≃ P.E') (eI : Fin N.b ≃ P.I'),
    (∀ i, P.ext i = eE (N.ext i)) ∧
    P.g.solid = N.g.solid.map (SEdge.map (Sum.map eE eI)) ∧
    P.g.waved.map (fun e => (e.x, e.y)) =
      N.g.waved.map (fun e => (Sum.map eE eI e.x, Sum.map eE eI e.y)) ∧
    P.g.dotted = N.g.dotted.map (DEdge.map (Sum.map eE eI))

/-- `Cand.toR` (probe 547-552): needs `cands_spec` (proved in LWExpSim.lean);
    declared as `axiom` here — never imported into the main build. -/
axiom Cand.toR (N : MNode) (h : Function.Surjective N.ext)
    (c : Cand N.a N.b) (hc : c ∈ cands N.g) : RCand (MNode.toP N h)

/-- `cPartitionX` (probe 572-577): model partition with exponents. -/
def cPartitionX {a b : ℕ} (Γ : LGraph (Fin (a+1)) (Fin b))
    (ext : Fin 2 → Fin (a+1)) : List ((ℕ × ℕ) × MNode) :=
  (Γ.dotChoices.map Γ.withDots).flatMap fun Δ =>
    match cMerge Δ ext with
    | none => []
    | some N => (lwSplitLoopsX N.g.solid).map fun r => (r.1, { N with g := { N.g with solid := r.2 } })

/-- `famsX` (probe 579-585): model families with exponents. -/
def famsX {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin b)) (c : Cand a b) :
    List ((ℕ × ℕ) × Σ b' : ℕ, LGraph (Fin (a+1)) (Fin b')) :=
  [((3, 0), ⟨b, oe2xR2 1 g c.q c.x c.y c.y'⟩),
   ((1, 0), ⟨b + 1, renum (owxT1 1 g c.x)⟩),
   ((3, 0), ⟨b + 2, renum (oe2xR4 1 g c.q c.x c.y c.y')⟩),
   ((1, 0), ⟨b + 1, renum (oe2xR5 1 g c.q c.x c.y c.y')⟩),
   ((3, 0), ⟨b + 2, renum (oe2xR6 1 g c.q c.x c.y c.y')⟩)] ++
  (lwSplit c.q.2).flatMap fun q' =>
    [((1, 0), ⟨b + 1, renum (oe2xR7 1 g c.x c.y c.y' q')⟩),
     ((3, 0), ⟨b + 2, renum (oe2xR8 1 g c.x c.y c.y' q')⟩)]

/-- `childrenX` (probe 591-593): model children with exponents. -/
def childrenX (N : MNode) (c : Cand N.a N.b) : List ((ℕ × ℕ) × MNode) :=
  (famsX N.g c).flatMap fun f =>
    (cPartitionX f.2.2 N.ext).map fun r => ((r.1.1 + f.1.1, r.1.2 + f.1.2), r.2)

/-- `PartitionSim` (probe 598-605): Bridge 1 — model partition vs real partition. -/
def PartitionSim : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (m : ℂ),
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : PGraph (Fin 2)) =>
        Rel r.2 Q ∧ Q.g.coeff = m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff)
      (cPartitionX N.g N.ext) ((N.g.partition m).map (pcomp (MNode.toP N h)))

/-- `ChildrenSim` (probe 606-610): Bridge 2 — model children vs real children. -/
def ChildrenSim : Prop :=
  ∀ (N : MNode) (h : Function.Surjective N.ext) (c : Cand N.a N.b) (hc : c ∈ cands N.g),
    List.Forall₂ (fun (r : (ℕ × ℕ) × MNode) (Q : (ℕ × ℕ) × PGraph (Fin 2)) =>
        Rel r.2 Q.2 ∧ r.1 = Q.1)
      (childrenX N c) (Cand.toR N h c hc).kids

/-! ## 3. Public theorem shapes -/

def partitionSim_pin : Prop := PartitionSim
def childrenSim_pin : Prop := ChildrenSim

/-! ## 4. Statement shapes at concrete merged data -/

example : Prop := partitionSim_pin ∧ childrenSim_pin

end RBM.Graph.T2311Check

end
