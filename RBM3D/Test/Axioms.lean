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

/-! ### The two ledgers

A premise this development does not prove is one of two things, and the difference
matters more than the count:

* **borrowed** -- the paper cites it from the literature rather than proving it.  These
  are long-term assumptions: discharging one means proving something the paper itself
  does not.
* **owed** -- the paper does prove it (or it is a routine consequence), and it is assumed
  here only to get on with the next layer.  These are debts of this formalization, not of
  the paper.

Reporting them in one list makes "zero axioms" look better than the situation is.
-/

/-- Premises the **paper** cites rather than proves. -/
def borrowedProps : List Name :=
  [`RBM.ThetaDecay, `RBM.ThetaDecayShort, `RBM.ThetaDiffOne, `RBM.ThetaDiffTwo,
   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep]

/-- Premises **this development** owes: provable here, assumed for now.

`KLoopBound` is here rather than in `borrowedProps` because the paper does prove it:
Appendix A.5 says the proof "is analogous to that of Lemma 3.11 in `[YY_25]`, but requires
additional modifications to handle the higher-dimensional setting `d ≥ 3`.  For the
reader's convenience, we provide the proof below", and then gives it in full.  Assuming it
here is a debt of this formalization (the molecule layer is missing), not a borrowing. -/
def owedProps : List Name :=
  [`RBM.Loop.TwoLoopBounded, `RBM.Loop.KLoopBound]

/-- Predicates that *define the objects under study* rather than assert a result about
them: assuming one is saying what the data is, not borrowing a theorem.  They are listed
so that the scan below can tell them apart from real premises -- and so that adding one
is a deliberate act. -/
def structuralProps : List Name :=
  [`RBM.Loop.IsKLoop,         -- `Def_Ktza`: what it means to be a family of `K`-loops
   `RBM.Loop.IsDiag,          -- `(i,j)` is a diagonal of the polygon
   `RBM.Loop.Crossing,        -- two diagonals cross
   `RBM.SameSignOutside,      -- `A ⊇ I_diff(σ)`, the condition of `lem:sum_decay_nonzero`
   `RBM.Graph.Case.Rel,       -- the case relation of `lem_scalingorder`, a parameter
   `RBM.NormStochDom]         -- `‖A‖ ≺ ζ`: notation of `(stoch_domination)`, not a result

/-- The premises the audit reports on: borrowed plus owed. -/
def interfaceProps : List Name := borrowedProps ++ owedProps

/-- **Non-vacuity certificates** (`docs/QUEUE.md`, Q41).  For a premise `p`, a theorem of
this development witnessing that `p` is *satisfiable*: either an object that satisfies it,
or a weakening of it that is proved here.

This is the one thing the axiom count cannot see.  If a premise is false, every theorem
carrying it is vacuously true, and the audit still reports `0 axioms` and a healthy list
of dependents -- which is exactly what happened while `(prop:ThfadC_short)` was stated
without its `σ₁ = σ₂` restriction (`docs/paper-deltas.md`, D11).  The certificate column
below is the positive half of that record; `RBM3D/Test/InterfaceShape.lean` holds both
halves and says, premise by premise, what a certificate would take.

A certificate must name a real theorem, for a registered premise; otherwise the build
fails.  The column is deliberately mostly empty: it reports a gap rather than hiding it. -/
def certificates : List (Name × Name) :=
  [(`RBM.ThetaDecay, `RBM.Test.thetaDecay_fixedL),
   (`RBM.ThetaZeroMode, `RBM.Test.thetaZeroMode_fixedL),
   (`RBM.ThetaDiffOne, `RBM.Test.thetaDiffOne_fixedL),
   (`RBM.ThetaDiffTwo, `RBM.Test.thetaDiffTwo_fixedL),
   (`RBM.PropTH, `RBM.Test.propTH_fixedL),
   (`RBM.Loop.TwoLoopBounded, `RBM.Test.twoLoopBounded_kTwoLoop)]

/-! ### Finding the premises, instead of being told them

`interfaceProps` used to be a hand-written list, and the moment a new assumption appeared
the report stayed silent about it -- a report that claims to account for everything and
quietly does not.  The scan below finds the premises itself: a `Prop`-valued definition in
`RBM` that some theorem takes as a hypothesis and **no** theorem of this development
proves.  Anything it finds that is in none of the three lists above fails the build.
-/

/-- The type is `∀ …, Prop`. -/
private partial def resultIsProp : Expr → Bool
  | .forallE _ _ b _ => resultIsProp b
  | .sort u => u == .zero
  | _ => false

/-- The constants occurring in the hypotheses of a `∀`-telescope. -/
private partial def binderConsts : Expr → Array Name
  | .forallE _ d b _ => binderConsts b ++ d.getUsedConstants
  | _ => #[]

/-- The head constant of the conclusion of a `∀`-telescope. -/
private partial def conclusionHead : Expr → Option Name
  | .forallE _ _ b _ => conclusionHead b
  | e => e.getAppFn.constName?

/-- `Prop`-valued definitions of `RBM`, the theorems that assume them, and the theorems
that prove them.  `ignore` keeps the audit's own fixtures out of the development.

A structure's projections do not count as proving its fields: `PropTH.decay` produces a
`ThetaDecay` from a `PropTH`, which is bookkeeping, not a proof.

Neither does a **certificate**: `twoLoopBounded_kTwoLoop` concludes
`TwoLoopBounded d L (kTwoLoop …)`, so its conclusion head is the premise, but it proves it
of *one* family, not of the arbitrary `K` that every theorem carrying the premise quantifies
over.  Counting it as a proof made the premise disappear from the scan -- a report that
goes quiet exactly when someone certifies an assumption is worse than no report -- so the
names in `certificates` are excluded here (`witness`). -/
def scanPremises (env : Environment) (ignore : Name → Bool) (witness : Name → Bool) :
    Array Name := Id.run do
  let keep (n : Name) : Bool := (`RBM).isPrefixOf n && !n.isInternalDetail && !ignore n
  let propDefs := env.constants.fold (init := #[]) fun acc n ci =>
    if keep n && (match ci with | .defnInfo _ | .inductInfo _ => true | _ => false)
        && resultIsProp ci.type then acc.push n else acc
  let mut assumed : Array Name := #[]
  let mut proved : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if keep n then
      match ci with
      | .thmInfo _ =>
        for c in binderConsts ci.type do
          if propDefs.contains c && !assumed.contains c then assumed := assumed.push c
        let isProj := propDefs.any fun p =>
          isStructure env p && (getStructureFields env p).any fun f => p ++ f == n
        unless isProj || witness n do
          match conclusionHead ci.type with
          | some h => if propDefs.contains h && !proved.contains h then proved := proved.push h
          | none => pure ()
      | _ => pure ()
  return assumed.filter fun n => !proved.contains n

/-- Declarations the compiler generates (recursors, `casesOn`, `noConfusion`, equation
lemmas, internal proofs) are not part of the development and are not counted. -/
def isHandwritten (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (`RBM).isPrefixOf n && !(`RBM.Audit).isPrefixOf n && !n.isInternalDetail
    && !isAuxRecursor env n && !isNoConfusion env n
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
  -- every certificate must name a real theorem, for a registered premise
  for (p, c) in certificates do
    unless (borrowedProps ++ owedProps ++ structuralProps).contains p do
      throwError m!"axiom audit: `{c}` is registered as a certificate for `{p}`, which is \
        not a registered premise"
    match env.find? c with
    | some (.thmInfo _) => pure ()
    | _ => throwError m!"axiom audit: the certificate `{c}` of `{p}` is not a theorem"
  -- the premises, found rather than declared
  let found := scanPremises env (fun n => (`RBM.Audit).isPrefixOf n)
    (fun n => certificates.any fun (_, c) => c == n)
  let classified := borrowedProps ++ owedProps ++ structuralProps
  let unregistered := found.filter fun n => !classified.contains n
  unless unregistered.isEmpty do
    throwError m!"axiom audit: {unregistered.size} premise(s) that no theorem of this \
      development proves are in none of `borrowedProps`, `owedProps`, \
      `structuralProps`:\n  {unregistered.toList}\n\
      Classify each of them: borrowed from the literature, owed by this formalization, \
      or a predicate that defines the objects under study."
  -- how much of the development rests on each premise
  -- a Prop's own projections (`PropTH.decay`, …) mention it but rest on nothing
  let isInterfaceOwn (n : Name) : Bool := interfaceProps.any fun p => p.isPrefixOf n
  let usageOf (ps : List Name) := ps.map fun p =>
    (p, (thms.filter fun (n, ci) =>
      !isInterfaceOwn n && (ci.type.getUsedConstants).contains p).size)
  let usage := usageOf interfaceProps
  let carried : Nat := usage.foldl (init := 0) fun acc (_, k) => acc + k
  let certOf (p : Name) : MessageData :=
    match certificates.find? (fun (q, _) => q == p) with
    | some (_, c) => m!" [certificate: {c}]"
    | none => m!" [no certificate]"
  let ledger (title : MessageData) (ps : List Name) : MessageData :=
    m!"{title}\n{MessageData.joinSep ((usageOf ps).map fun (p, k) =>
      m!"  {p}: {k}{certOf p}") "\n"}"
  let usageReport := usage.map fun (p, k) => m!"  {p}: {k}"
  let axiomLine :=
    if interfaceAxioms.isEmpty then
      m!"no project axioms: what the paper cites rather than proves is carried as \
        hypotheses, not asserted"
    else
      m!"interface axioms, with the number of other declarations depending on each:\n\
        {MessageData.joinSep (counts.toList.map fun (a, k) => m!"  {a}: {k}") "\n"}"
  let _ := usageReport
  -- how the premises the scan found fall into the three ledgers, and which registered
  -- premises nothing currently rests on
  let foundBorrowed := found.filter (borrowedProps.contains ·)
  let foundOwed := found.filter (owedProps.contains ·)
  let foundStructural := found.filter (structuralProps.contains ·)
  let unused := classified.filter fun n => !found.contains n
  let registryLine :=
    if unused.isEmpty then
      m!"registry: {borrowedProps.length} borrowed + {owedProps.length} owed + \
        {structuralProps.length} structural, every one of them carrying something"
    else
      m!"registry: {borrowedProps.length} borrowed + {owedProps.length} owed + \
        {structuralProps.length} structural; {unused.length} registered premise(s) carry \
        nothing yet: {unused}"
  let carriedLine :=
    if carried = 0 then
      m!"no theorem yet rests on a premise"
    else
      m!"{ledger m!"theorems resting on each premise the PAPER borrows:" borrowedProps}\n\
        {ledger m!"theorems resting on each premise THIS FORMALIZATION owes:" owedProps}"
  logInfo m!"axiom audit: {thms.size} theorems, {defs.size} definitions, {axs.size} axioms \
    in `RBM` (compiler-generated declarations excluded).\n\
    All within {allowedAxioms}; {axiomLine}.\n\
    {carriedLine}\n\
    premises found by scanning: {found.size} (borrowed {foundBorrowed.size}, \
    owed {foundOwed.size}, structural {foundStructural.size}).\n\
    {registryLine}.\n\
    non-vacuity certificates: {certificates.length} of \
    {borrowedProps.length + owedProps.length} premises in the two ledgers; the rest are \
    not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would \
    take)"

/-- **Reverse test.**  Fails unless the scan reports `p` as an unclassified premise.  The
point of `#assert_rbm_axioms` is that adding an assumption without classifying it breaks
the build; this checks that the mechanism actually fires, on a fixture kept out of the
development (`RBM.Audit.Fixture`). -/
elab "#assert_rbm_audit_detects " p:ident : command => do
  let env ← getEnv
  let n := p.getId
  let found := scanPremises env (fun _ => false)
    (fun n => certificates.any fun (_, c) => c == n)
  let classified := borrowedProps ++ owedProps ++ structuralProps
  let unregistered := found.filter fun m => !classified.contains m
  unless unregistered.contains n do
    throwError m!"audit reverse test: the scan did not report `{n}` as an unclassified \
      premise; it found {unregistered.toList}"
  logInfo m!"audit reverse test: an unclassified premise is caught ({n})."

end RBM.Audit
