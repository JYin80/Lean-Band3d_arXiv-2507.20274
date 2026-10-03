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

/-- Premises the **paper** cites rather than proves.  The pins of `lem_propTH` properties
5–8 (T2003, DECISIONS §13) and their KL-local form (T2004, §15) replace the old `ThetaDecay`
… `PropTH` as the statements route H (DECISIONS §14) discharges; they are not authorised
external inputs (DECISIONS §5), so they must end up proved.  Route H proved `lem_propTH`
5–8 for every `d ≥ 3` (T2023, T2024, T2027), so `Prop5Decay`, `Prop8ZeroMode`, `Prop5to8`,
`ThetaDecay`, `ThetaDecayShort` and `ThetaZeroMode` left this list. -/
def borrowedProps : List Name :=
  [`RBM.ThetaDiffOne, `RBM.ThetaDiffTwo, `RBM.PropTH, `RBM.Loop.KTreeRep, `RBM.Loop.KLPT]

/-- Premises **this development** owes: provable here, assumed for now.

`KLoopBound` is here rather than in `borrowedProps` because the paper does prove it:
Appendix A.5 says the proof "is analogous to that of Lemma 3.11 in `[YY_25]`, but requires
additional modifications to handle the higher-dimensional setting `d ≥ 3`.  For the
reader's convenience, we provide the proof below", and then gives it in full.  Assuming it
here is a debt of this formalization (the molecule layer is missing), not a borrowing. -/
def owedProps : List Name :=
  [`RBM.Loop.TwoLoopBounded, `RBM.Loop.KLoopBound,
   `RBM.Green.GaussIBP,  -- Stein identity and finite polynomial moments of `Sizes.seqP`; proved by S1-19 (RBM2D `IBPPoly:299`), taken by `Tame.integrable` (T2031)
   `RBM.Gauss.Sizes.STKbound,       -- `ML:Kbound` (`1_2:1056`), hypothesis of `STStep1`: proved by KL7 (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STLK,           -- (a) of `lem:main_ind` at `s`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STLmax,         -- `(eq:loopbound_s)`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STDecay,        -- (b), first part: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STDecayStrong,  -- (b), second part: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STLocalMax,     -- (c) `(Gt_bound+IND)`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STExp2,         -- (d) `(Eq:Gtlp_exp+IND)`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STMainInd,      -- `lem:main_ind`: end of the ST-6 chain; class not signed in §19, owed by the §20 rule (T2028)
   `RBM.Gauss.Sizes.STConArg,       -- `lem_ConArg` (`3_5:42`): S1-32 (T2028, §20 rule; class not signed in §19)
   `RBM.Gauss.Sizes.STStep1,        -- Step 1 of `lem:main_ind` (`1_2:1317`): S1-36 (T2028, §20 rule; class not signed in §19)
   `RBM.Gauss.Sizes.STBootstrap,    -- continuity bootstrap of Step 1 (`3_5:64`): S1-36 (T2028, T2015 b.10)
   `RBM.Gauss.Sizes.STNetLift,      -- net lift of Step 1: S1-34 (T2028, T2015 b.10)
   `RBM.Gauss.Sizes.STForbidden,    -- forbidden-region estimate of Step 1: S1-36 (T2028, §20 rule; class not signed in §19)
   `RBM.Green.GbEXPV3Theorem,       -- `lem_GbEXP` in the RBM2D form (`3_5:14`): S1-30 `gbEXPV3` (T2028)
   `RBM.Green.GijOmegaSeq,          -- `(GijGEX)` on `Ω` per sequence: S1-24 `gijOmegaSeq`, RBM2D `Green/EntryGauss.lean:55` (T2028)
   `RBM.Green.AsGMcPT,              -- `(asGMc)` per time: from (`Gtmwc`) of Step 1, RBM2D `Path/GoodSet.lean:439` `goodSet_asGMc` (T2028, §20 rule)
   `RBM.Gauss.Sizes.STLmaxU, -- `(Eq:LGxb)` uniform in `u ∈ [s,t]`: ST-6 chain / Step 4
   `RBM.Gauss.Sizes.STLKU, -- `(Eq:L-KGt-flow)` uniform in `u ∈ [s,t]`: ST-6 chain / Step 3 (not in the §25 list; owed, T2049 proposal)
   `RBM.Gauss.Sizes.STStep3R, -- Step 3 per regime `R` (generic form): assembly S3-27 (not in the §25 list; owed, T2049 proposal)
   `RBM.Gauss.Sizes.STStep4R, -- Step 4 per regime `R` (generic form): assembly S3-27 (not in the §25 list; owed, T2049 proposal)
   `RBM.Gauss.Sizes.STStep3, -- Step 3, any regime: assembly S3-27 (T2049 proposal)
   `RBM.Gauss.Sizes.STStep3I, -- Step 3, case (i): assembly S3-27 (T2049 proposal)
   `RBM.Gauss.Sizes.STStep3II, -- Step 3, case (ii): assembly S3-27 (T2049 proposal)
   `RBM.Gauss.Sizes.STStep4, -- Step 4, any regime: assembly S3-27 (T2049 proposal)
   `RBM.Gauss.Sizes.STStep4I, -- Step 4, case (i): assembly S3-27 (T2049 proposal)
   `RBM.Gauss.Sizes.STStep4II, -- Step 4, case (ii): assembly S3-27 (T2049 proposal)
   `RBM.Gauss.Sizes.STIngR, -- generic setting of an ingredient of Steps 3-4 (T2049 proposal; owed)
   `RBM.Gauss.Sizes.STIterR, -- generic setting of `lem:iterations` (T2049 proposal; owed)
   `RBM.Gauss.Sizes.STContract, -- `(yi2oslxj2)`, `(u2jzooi-2)`: new at d >= 3 (DECISIONS §25)
   `RBM.Gauss.Sizes.STNewPQ, -- `lem: newPQ` (DECISIONS §25)
   `RBM.Gauss.Sizes.STSEforLn, -- `lem:SEforLn` (DECISIONS §25)
   `RBM.Gauss.Sizes.STOeqNQ, -- `lem:STOeq_NQ` (DECISIONS §25)
   `RBM.Gauss.Sizes.STOeqQt, -- `lem:STOeq_Qt` (DECISIONS §25)
   `RBM.Gauss.Sizes.STOeqQtNZ, -- `lem:STOeq_Qt_nonzero` (DECISIONS §25)
   `RBM.Gauss.Sizes.STIterations, -- `lem:iterations`, case (i) (DECISIONS §25)
   `RBM.Gauss.Sizes.STIterationsII, -- `lem:iterations`, case (ii) (DECISIONS §25)
   `RBM.Gauss.Sizes.STMollifierEx, -- `rmk:choosechi`: existence of the mollifier (DECISIONS §25)
   `RBM.Gauss.Sizes.STQopNorm, -- `lem_+Q` with `4 ≤ W^ε`, `L^d ≤ W^K` (DECISIONS §25)
   `RBM.Gauss.Sizes.STWardTypePPin, -- `(eq:Ward_typeP)` (DECISIONS §25)
   `RBM.Gauss.Sizes.STB45Pin, -- `(y27kasdfg)` (DECISIONS §25)
   `RBM.Gauss.Sizes.STNewKLK, -- `lem:newKLK` (`3_5:371-378`): ST2-07 (+ST2-06b) (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STContractPt, -- pointwise contraction inequality `ygdhmsgq0` (`3_5:751-797`): ST2-08 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STEMn2Poly, -- `lem: EMn2_N`, `(eq:MG_conclusion)` (`3_5:427-432`): ST2-09 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STEMn2Exp, -- `lem: EMn2_N`, `(eq:MG_conclusion3)` (`3_5:437-440`): ST2-10, ST2-11 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STGridRepN, -- `Sol_CalL` + `lem:DIfREP` on the grid, every loop length (`3_5:134-148`, `218-240`); `STGridMart` is `m = 2`: ST2-12, ST2-13 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STK2decay, -- `(eq:kn2sol_decay)`, `(eq:simpleboundK)` (`3_5:457`, `518`): ST2-06 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STNetLift2, -- net lift of Step 2 (`1_2:1400`): ST2-18, ST2-19 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STScaleExists, -- scale family of `(eq:def_ell1)` (`3_5:521-527`, `571-577`): ST2-05 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STOptL2, -- `(eq:opt_L2)` (`3_5:470`): ST2-14, ST2-15 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLocalAvgOfL2, -- closing paragraph of Step 2 (`3_5:455-465`): ST2-16, ST2-17 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STStep2, -- Step 2 of `lem:main_ind` (`1_2:1340-1357`): ST2-04 (`ST_step2_of_pins`) (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWB, -- `lem:LWterm` (`3_5:385-404`): LW gate, bridge in ST2-03 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWT, -- `lem: EWGn2_N` (`3_5:406-415`): LW gate, bridge in ST2-03 (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STInitialGT2, -- `(initialGT2)` (`3_5:28-30`): Step 1 / ST-6 chain (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWassm, -- `(eq:LW_assm)` (`3_5:388`): Step 1 / ST-6 chain (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWassmExp] -- `(eq:LW_assm_exp)` (`3_5:409`): Step 1 / ST-6 chain (T2066, DECISIONS §28)

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
   `RBM.NormStochDom,         -- `‖A‖ ≺ ζ`: notation of `(stoch_domination)`, not a result
   `RBM.NormStochDomAt,       -- notation of `(stoch_domination)` at scale `N`
   `RBM.Path.PerTimeDomAt,    -- notation of `(stoch_domination)` at scale `N`
   `RBM.Gauss.Sizes.WO,       -- `(eq:WO)`: the window of the size sequence
   `RBM.Gauss.Sizes.Bandwidth, -- `(Main_DEL_COND)`: `W ≥ N^𝔠`
   `RBM.Gauss.Sizes.SizeTendsto, -- `N → ∞` along the size sequence
   `RBM.Gauss.Sizes.Admissible, -- the standing hypotheses of the main results
   `RBM.Gauss.Sizes.locDomain, -- the spectral domain `𝐃_{κ,ε}`
   `RBM.Green.GoodEvent,      -- the event Ω of (4.10): every entry of `G` within `δ` of `m·I`
   `RBM.Green.LDERow,         -- row large-deviation event, input of `lem_GbEXP` (later ST-1)
   `RBM.Green.LDECol,         -- column large-deviation event, input of `lem_GbEXP` (later ST-1)
   `RBM.Green.LDEQuad,        -- quadratic large-deviation event; h.p. bound S1-19 `stochDom_ldeQuad`
   `RBM.Green.Stable,         -- stability of `1 − ξS` with constant `K`; band profile S1-24
   `RBM.EKFastDecay,          -- `(deccA0)`: decay of the tensor `A` beyond the window `W^ε ℓ_s`, a data condition on `A` (EK-3, T2034)
   `RBM.Green.AgreeOffRow,    -- two samples agree on every coordinate off row `i` (S1-11 RowIndep)
   `RBM.Green.FinDep,         -- `g` reads finitely many Gaussian coordinates: a property of the function, hypothesis of `Tame.ofBdd` (T2031)
   `RBM.Graph.Tame1,          -- `F` is `C¹`-tame (tame, differentiable along every coordinate, tame partials): hypothesis of `stein_sample`; proved for resolvent polynomials by `lwPoly_tame1` (T2060)
   `RBM.Gauss.Sizes.STConStInd, -- `(con_st_ind)` (`1_2:1296`): a condition on the time sequences (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STFlow, -- the setting of `MR:locSC` and `zztE`: `Admissible` and `locDomain` (T2028, DECISIONS §19)
   `RBM.Graph.LGraph.DotWF, -- at most one dotted edge per pair of vertices, none a loop (`def_graph1`, `7_8:141`; T2050)
   `RBM.Gauss.Sizes.STPsiClass, -- the class of profiles `Ψ_t(|a-b|)` of `(eq:Psi)` (`3_5:385-393`): data condition of `STLWB`, `STEMn2Poly` (T2066)
   `RBM.Graph.LGraph.Consistent] -- a term `Dot · Γ` of the dotted edge partition has no `×`-dotted edge inside a class of `=`-dotted edges (`dot-def`, `7_8:221`; T2050)

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
  [(`RBM.ThetaDiffOne, `RBM.Test.thetaDiffOne_fixedL),
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
