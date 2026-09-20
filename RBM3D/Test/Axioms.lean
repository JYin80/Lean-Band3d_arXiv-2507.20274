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
* fails if it finds fewer than `20` declarations in `RBM`, so that a renamed namespace
  cannot make the audit pass vacuously;
* prints, for each interface axiom, how many `RBM` declarations depend on it.  That count
  is the honest measure of how much of the development rests on borrowed results, and it
  should be watched: a discharged axiom is one whose count can go to zero.  With the list
  empty the command says so instead.
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

/-- Fails unless every declaration in `RBM` uses only `allowedAxioms` together with the
declared `interfaceAxioms`, and reports the dependency count of each interface axiom. -/
elab "#assert_rbm_axioms" : command => do
  let env ← getEnv
  -- the interface list must name real axioms
  for n in interfaceAxioms do
    match env.find? n with
    | none => throwError m!"axiom audit: interface axiom `{n}` does not exist"
    | some (.axiomInfo _) => pure ()
    | some _ => throwError m!"axiom audit: `{n}` is listed as an interface axiom but is \
        not an axiom"
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if (`RBM).isPrefixOf n then acc.push n else acc
  if names.size < 20 then
    throwError m!"axiom audit: only {names.size} declarations found in `RBM`"
  let permitted := allowedAxioms ++ interfaceAxioms
  let mut bad : Array MessageData := #[]
  let mut counts : Array (Name × Nat) := interfaceAxioms.toArray.map (·, 0)
  for n in names do
    let axs ← collectAxioms n
    let extra := axs.filter fun a => !permitted.contains a
    unless extra.isEmpty do
      bad := bad.push m!"{n} depends on {extra.toList}"
    counts := counts.map fun (a, k) => if axs.contains a then (a, k + 1) else (a, k)
  unless bad.isEmpty do
    throwError m!"axiom audit failed:\n{MessageData.joinSep bad.toList "\n"}"
  if interfaceAxioms.isEmpty then
    logInfo m!"axiom audit: {names.size} declarations in `RBM`, all within \
      {allowedAxioms}.  No interface axioms: what the paper cites rather than proves is \
      carried as hypotheses (`RBM.PropTH`)."
  else
    let report := counts.toList.map fun (a, k) => m!"  {a}: {k}"
    logInfo m!"axiom audit: {names.size} declarations in `RBM`, all within \
      {allowedAxioms} plus the declared interface.\n\
      Declarations depending on each interface axiom:\n{MessageData.joinSep report "\n"}"

end RBM.Audit
