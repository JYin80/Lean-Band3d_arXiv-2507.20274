/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Lean

/-!
# Axiom audit: the `#assert_rbm_axioms` command

`#assert_rbm_axioms` walks every declaration in the namespace `RBM` visible in the
current environment, collects the axioms it depends on (the same computation as
`#print axioms`), and **fails** unless each of them is either

* one of `propext`, `Classical.choice`, `Quot.sound`, or
* one of the named **interface axioms** listed in `RBM.Audit.interfaceAxioms`.

Any `sorry` (`sorryAx`) therefore breaks the build, and so does any new `axiom` that has
not been added to the list deliberately.

The interface list is **empty**, as in the sister projects `RBM1D` and `RBM2D`: what this
paper cites rather than proves is carried as hypotheses (`RBM.PropTH`, see
`RBM3D/Propagator/Interface.lean`), so a result resting on a borrowed estimate says so in
its own statement.  The list is kept, and the command still checks it, so that a future
exception would have to be written down here.

The command also:

* fails if any listed interface axiom does not exist, or exists but is not an axiom --
  so the list cannot rot as the interface files are edited;
* fails if it finds fewer than `20` theorems in `RBM`, so that a renamed namespace cannot
  make the audit pass vacuously;
* reports what the development consists of -- **theorems**, definitions and axioms,
  counting only handwritten declarations (recursors, `casesOn`, `noConfusion`, equation
  lemmas and internal proofs are the compiler's, not the project's);
* reports, for each interface `Prop` (`RBM.Audit.interfaceProps`), how many theorems carry
  it as a hypothesis, excluding the `Prop`'s own projections.  That count is the honest
  measure of how much of the development rests on what the paper cites rather than proves:
  it is `0` while the borrowing is inert, and turns positive the moment a real result
  depends on it.
-/

namespace RBM.Audit

open Lean Elab Command

/-- The axioms every `RBM` declaration may use unconditionally. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Interface axioms: **none**.  The results this paper cites but does not prove are
`Prop`s in `RBM3D/Propagator/Interface.lean` (`RBM.PropTH`), assumed by the theorems that
need them, not asserted.  The list is kept so that the exception remains available and
visible: adding a name here would be a deliberate act, recording that the development is
allowed to rest on a result from outside the paper. -/
def interfaceAxioms : List Name := []

/-- The interface `Prop`s: the statements this paper cites rather than proves, carried as
hypotheses.  A theorem whose *type* mentions one of these rests on a borrowed result, and
says so; counting those theorems is how this development measures how much of it is
carried by the borrowing. -/
def interfaceProps : List Name :=
  [`RBM.ThetaDecay, `RBM.ThetaDecayShort, `RBM.ThetaDiffOne, `RBM.ThetaDiffTwo,
   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep]

/-- Declarations the compiler generates (recursors, `casesOn`, `noConfusion`, equation
lemmas, internal proofs) are not part of the development and are not counted. -/
def isHandwritten (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (`RBM).isPrefixOf n && !n.isInternalDetail && !isAuxRecursor env n && !isNoConfusion env n
    && !(match ci with | .recInfo _ => true | _ => false)

/-- Fails unless every declaration in `RBM` uses only `allowedAxioms` together with the
declared `interfaceAxioms`, and reports what the development consists of: how many
theorems, how many definitions, how many axioms, and how many theorems rest on each
interface hypothesis. -/
elab "#assert_rbm_axioms" : command => do
  let env ← getEnv
  -- the interface list must name real axioms
  for n in interfaceAxioms do
    match env.find? n with
    | none => throwError m!"axiom audit: interface axiom `{n}` does not exist"
    | some (.axiomInfo _) => pure ()
    | some _ => throwError m!"axiom audit: `{n}` is listed as an interface axiom but is \
        not an axiom"
  -- the handwritten declarations of `RBM`, classified
  let handwritten := env.constants.fold (init := #[]) fun acc n ci =>
    if isHandwritten env n ci then acc.push (n, ci) else acc
  let thms := handwritten.filter fun (_, ci) => match ci with | .thmInfo _ => true | _ => false
  let axs := handwritten.filter fun (_, ci) => match ci with | .axiomInfo _ => true | _ => false
  let defs := handwritten.filter fun (_, ci) =>
    match ci with
    | .defnInfo _ | .inductInfo _ | .ctorInfo _ | .opaqueInfo _ => true
    | _ => false
  if thms.size < 20 then
    throwError m!"axiom audit: only {thms.size} theorems found in `RBM`"
  -- every declaration may use only the permitted axioms
  let permitted := allowedAxioms ++ interfaceAxioms
  let mut bad : Array MessageData := #[]
  let mut counts : Array (Name × Nat) := interfaceAxioms.toArray.map (·, 0)
  for (n, _) in handwritten do
    let usedAxioms ← collectAxioms n
    let extra := usedAxioms.filter fun a => !permitted.contains a
    unless extra.isEmpty do
      bad := bad.push m!"{n} depends on {extra.toList}"
    counts := counts.map fun (a, k) => if usedAxioms.contains a && a != n then (a, k + 1) else (a, k)
  unless bad.isEmpty do
    throwError m!"axiom audit failed:\n{MessageData.joinSep bad.toList "\n"}"
  -- how much of the development rests on the borrowed results
  -- a Prop's own projections (`PropTH.decay`, …) mention it but rest on nothing
  let isInterfaceOwn (n : Name) : Bool := interfaceProps.any fun p => p.isPrefixOf n
  let usage := interfaceProps.map fun p =>
    (p, (thms.filter fun (n, ci) =>
      !isInterfaceOwn n && (ci.type.getUsedConstants).contains p).size)
  let carried : Nat := usage.foldl (init := 0) fun acc (_, k) => acc + k
  let usageReport := usage.map fun (p, k) => m!"  {p}: {k}"
  let axiomLine :=
    if interfaceAxioms.isEmpty then
      m!"no project axioms: what the paper cites rather than proves is carried as \
        hypotheses, not asserted"
    else
      m!"interface axioms, with the number of other declarations depending on each:\n\
        {MessageData.joinSep (counts.toList.map fun (a, k) => m!"  {a}: {k}") "\n"}"
  let carriedLine :=
    if carried = 0 then
      m!"no theorem yet rests on the borrowed results"
    else
      m!"theorems resting on each borrowed result:\n{MessageData.joinSep usageReport "\n"}"
  logInfo m!"axiom audit: {thms.size} theorems, {defs.size} definitions, {axs.size} axioms \
    in `RBM` (compiler-generated declarations excluded).\n\
    All within {allowedAxioms}; {axiomLine}.\n\
    {carriedLine}."

end RBM.Audit
