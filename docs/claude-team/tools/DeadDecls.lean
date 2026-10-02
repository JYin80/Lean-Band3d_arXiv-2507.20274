/-
DeadDecls (T2273, DECISIONS §244): report every unreachable declaration of the `RBM3D` library.

Run from the main worktree (it needs the built `RBM3D` library):

    lake env lean docs/claude-team/tools/DeadDecls.lean

Prints a report on stdout.  Nothing is written, the library is not modified.

Method.  The environment is `import RBM3D`.  A declaration is *in scope* when its declaring
module is `RBM3D` or `RBM3D.*` (`getModuleIdxFor?`).  Starting from the roots below, the tool
computes the set of reached constants; only in-scope constants are expanded (Mathlib and Lean
cannot refer back to `RBM3D`).  Edges of a reached constant `c`:
  * every constant in `c.type` and in `c.value?` (opaque values included);
  * inductive types: all constructors, the recursor, and the `all` block (mutual types);
  * a constructor reaches its inductive type; a projection function reaches its structure;
  * a structure reaches all its projection functions (the structure is one unit);
  * a constant without declaration ranges (`match_1`, `proof_1`, `eq_1`, `_unfold`, `induct`,
    `_auxLemma.n`, ...) reaches its nearest ancestor name that is a constant;
  * a constant of the unit of an inductive/structure `T` (below) reaches `T`.
Generated constants of an inductive/structure `T` (`T.casesOn`, `T.recOn`, `T.rec`,
`T.noConfusion`, `T.mk.noConfusion`, `T.noConfusionType`, `T.below`, `T.brecOn`, and
attribute-generated ones such as `T.ext`/`T.ext_iff`) DO have declaration ranges in Lean 4.34:
those of the `structure`/`inductive` command.  Generic unit rule: an in-scope constant with a
declaration range whose name extends an in-scope inductive `T` (`T` is a proper name prefix)
and whose line range lies inside `T`'s line range belongs to `T`'s unit; constructors and
projection functions belong to their structure's unit.  A unit is counted once, as `T`.
Reported (unreached) are the units of in-scope constants that have declaration ranges, i.e. are
user-written.
Meta code (syntax/macro/elab/parser/delaborator/tactic constants) is listed separately and is
not a candidate for deletion.

Limitations (not edges): `implemented_by`/`csimp`/`extern` attribute targets, `@[simp]`/instance
lemmas that were never used in a term, and `deriving` handlers' instances.
-/
import RBM3D

open Lean Elab Command

namespace DeadDecls

/-- Namespaces and constants whose mention in a type marks a constant as meta code. -/
def metaPrefixes : List Name :=
  [`Lean.Elab, `Lean.Meta, `Lean.MetaM, `Lean.Syntax, `Lean.TSyntax, `Lean.Parser,
   `Lean.PrettyPrinter, `Lean.ParserDescr, `Lean.TrailingParserDescr, `Lean.Macro, `Lean.MacroM,
   `Lean.CoreM, `Lean.Core, `Lean.Expr, `Lean.Environment]

/-- Roots given by full name. -/
def fixedRoots : List Name :=
  [`RBM.Endpoints.locSC_holds, `RBM.Endpoints.QDiff_holds, `RBM.Endpoints.decol_holds,
   `RBM.Endpoints.QUE_holds, `RBM.Endpoints.bUniv_holds,
   `RBM.Endpoints.admissible_witnessSizes, `RBM.Endpoints.locSC_holds_instance,
   `RBM.Endpoints.mSC_eq_msc]

/-- Constants named by the statement and the proof of the two `example`s of
`RBM3D/Main/BUnivHolds.lean` (an `example` is not a constant, so they are listed by hand).
Full names, resolved under the `open`s of that file. -/
def exampleRoots : List Name :=
  [`RBM.Endpoints.bUniv_holds, `RBM.Univ.L32, `RBM.Endpoints.kPoint,
   `RBM.Gauss.Sizes.seqXmat_isHermitian, `RBM.Gauss.Xmat_isHermitian, `RBM.Gauss.Sizes.seqP,
   `RBM.Endpoints.gueP, `RBM.Endpoints.witnessSizes, `RBM.Endpoints.admissible_witnessSizes,
   `RBM.Univ.Step1CondCheck.bump, `RBM.Univ.Step1CondCheck.bump_testFun]

/-- Sanity expectations: (name, expected reached). -/
def sanity : List (Name × Bool) :=
  [(`RBM.Endpoints.p7Out_holds, false), (`RBM.Endpoints.p7ExpOut_holds, false),
   (`RBM.Endpoints.BUnivHoldsCheck.bUniv_holds_pin, false),
   (`RBM.Endpoints.stoAll_holds, true), (`RBM.Univ.L32, true)]

def isInScopeModule (m : Name) : Bool := m.getRoot == `RBM3D

def fmtName (n : Name) : String :=
  match privateToUserName? n with
  | some u => s!"private {u}"
  | none => toString n

structure Decl where
  name : Name
  modIdx : Nat
  startLine : Nat
  endLine : Nat
  isMeta : Bool

def mentionsMeta (ci : ConstantInfo) : Bool :=
  ci.type.getUsedConstants.any fun c => metaPrefixes.any (·.isPrefixOf c)

/-- Generic unit rule: the nearest proper name prefix `T` of `n` that is an in-scope inductive
whose line range contains the line range of `n` (both ranged). -/
def inductUnit? (env : Environment) (inScope : Name → Bool) (rangeOf : Name → Option (Nat × Nat))
    (n : Name) : Option Name := Id.run do
  let some (s, e) := rangeOf n | return none
  let mut p := n.getPrefix
  while !p.isAnonymous do
    if inScope p then
      if let some (.inductInfo _) := env.find? p then
        if let some (ps, pe) := rangeOf p then
          if ps ≤ s && e ≤ pe then return some p
    p := p.getPrefix
  return none

/-- Canonical unit of a constant: structure for a projection, inductive for a constructor,
`T` for a generated (ranged) constant of an inductive `T` (generic rule above). -/
def unitOf (env : Environment) (inScope : Name → Bool) (rangeOf : Name → Option (Nat × Nat))
    (n : Name) : Name :=
  match env.getProjectionFnInfo? n with
  | some info =>
    match env.find? info.ctorName with
    | some (.ctorInfo cv) => cv.induct
    | _ => n
  | none =>
    match env.find? n with
    | some (.ctorInfo cv) => cv.induct
    | _ => (inductUnit? env inScope rangeOf n).getD n

def edges (env : Environment) (inScope : Name → Bool) (rangeOf : Name → Option (Nat × Nat))
    (n : Name) : Array Name := Id.run do
  let hasRange : Name → Bool := fun m => (rangeOf m).isSome
  let some ci := env.find? n | return #[]
  let mut out : Array Name := ci.type.getUsedConstants
  -- a member of the unit of `T` reaches `T`
  let u := unitOf env inScope rangeOf n
  if u != n then out := out.push u
  if let some v := ci.value? true then
    out := out ++ v.getUsedConstants
  match ci with
  | .inductInfo iv =>
    out := out ++ iv.ctors.toArray ++ iv.all.toArray
    out := out.push (n ++ `rec)
    if let some si := getStructureInfo? env n then
      for fi in si.fieldInfo do
        out := out.push fi.projFn
  | .ctorInfo cv => out := out.push cv.induct
  | .recInfo rv => out := out ++ rv.all.toArray
  | _ => pure ()
  if let some info := env.getProjectionFnInfo? n then
    out := out.push info.ctorName
    if let some (.ctorInfo cv) := env.find? info.ctorName then out := out.push cv.induct
  -- auxiliary names: reach the nearest ancestor that is a constant
  if !hasRange n then
    let mut p := n.getPrefix
    while !p.isAnonymous do
      if env.contains p then
        out := out.push p
        break
      p := p.getPrefix
  return out

def pad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

def run : CommandElabM Unit := do
  let env ← getEnv
  let hdr := env.header
  -- in-scope modules and constants
  let mut modOf : Std.HashMap Name Nat := {}
  let mut inScopeMods : Array Nat := #[]
  for i in [0:hdr.moduleNames.size] do
    if isInScopeModule hdr.moduleNames[i]! then
      inScopeMods := inScopeMods.push i
      for c in hdr.moduleData[i]!.constNames do
        modOf := modOf.insert c i
  let mut ranges : Std.HashMap Name (Nat × Nat) := {}
  for (c, _) in modOf.toList do
    if let some r ← liftCoreM <| findDeclarationRanges? c then
      ranges := ranges.insert c (r.range.pos.line, r.range.endPos.line)
  let rangeOf : Name → Option (Nat × Nat) := fun n => ranges[n]?
  let inScope : Name → Bool := fun n => modOf.contains n
  -- roots
  let mut rootsUsed : Array (Name × String) := #[]
  for r in fixedRoots do rootsUsed := rootsUsed.push (r, "ticket root")
  for r in exampleRoots do
    if !fixedRoots.contains r then
      rootsUsed := rootsUsed.push (r, "added by hand: constant of the `example`s in Main/BUnivHolds.lean")
  let auditNames := modOf.toList.filterMap fun (c, _) => if `RBM.Audit |>.isPrefixOf c then some c else none
  let auditSorted := auditNames.toArray.qsort (fun a b => a.toString < b.toString)
  for r in auditSorted do rootsUsed := rootsUsed.push (r, "namespace RBM.Audit")
  -- closure
  let mut reached : Std.HashSet Name := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut stack : Array Name := #[]
  let mut missing : Array Name := #[]
  for (r, _) in rootsUsed do
    if env.contains r then
      stack := stack.push r
    else
      missing := missing.push r
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if reached.contains n then continue
    reached := reached.insert n
    if modOf.contains n then
      for m in edges env inScope rangeOf n do
        if !reached.contains m && modOf.contains m then
          stack := stack.push m
          if !parent.contains m then parent := parent.insert m n
  -- declarations (units)
  let mut decls : Array Decl := #[]
  for (c, mi) in modOf.toList do
    if let some (s, e) := ranges[c]? then
      if unitOf env inScope rangeOf c == c then
        -- a unit is reached when it or any of its projections / constructors is reached
        let some ci := env.find? c | continue
        decls := decls.push { name := c, modIdx := mi, startLine := s, endLine := e,
                              isMeta := mentionsMeta ci ||
                                c.components.any fun x => x.toString.startsWith "_aux_" }
  let isReached (d : Decl) : Bool := reached.contains d.name
  -- header
  let mut out : Array String := #[]
  out := out.push s!"DeadDecls report: modules {hdr.moduleNames.size}, in scope {inScopeMods.size}, constants in scope {modOf.size}, counted declarations {decls.size}"
  out := out.push ""
  out := out.push "## (a) roots actually used"
  for (r, why) in rootsUsed do
    let ok := if env.contains r then "" else "  [MISSING]"
    out := out.push s!"- {r}  ({why}){ok}"
  out := out.push s!"- ({auditSorted.size} constants in RBM.Audit; {reached.size} in-scope constants reached)"
  if !missing.isEmpty then out := out.push s!"MISSING ROOTS: {missing}"
  out := out.push ""
  out := out.push "## sanity checks"
  for (n, exp) in sanity do
    let r := reached.contains n
    out := out.push s!"- {n}: {if r then "reached" else "UNREACHED"} (expected {if exp then "reached" else "unreached"}) {if r == exp then "OK" else "MISMATCH"}"
  -- why-chains for sanity names that are reached but expected unreached
  for (n, exp) in sanity do
    if reached.contains n && !exp then
      let mut chain : Array Name := #[n]
      let mut cur := n
      for _ in [0:200] do
        match parent[cur]? with
        | some p => chain := chain.push p; cur := p
        | none => break
      out := out.push s!"  reached via (first discovered path, from the name up to a root): {" <- ".intercalate (chain.toList.map toString)}"
  -- all direct referrers (among reached constants) of sanity names that are reached but expected unreached
  for (n, exp) in sanity do
    if reached.contains n && !exp then
      let refs := reached.toList.filter fun m => modOf.contains m && m != n &&
        (edges env inScope rangeOf m).contains n
      let refs := (refs.map toString).toArray.qsort (· < ·)
      out := out.push s!"  all reached direct referrers of {n}: {", ".intercalate refs.toList}"
  let rootReached := rootsUsed.all fun (r, _) => reached.contains r
  out := out.push s!"- every root reached: {rootReached}"
  out := out.push ""
  -- per-module
  let modName (i : Nat) : String := toString hdr.moduleNames[i]!
  let mut byMod : Std.HashMap Nat (Array Decl) := {}
  for d in decls do
    byMod := byMod.insert d.modIdx ((byMod.getD d.modIdx #[]).push d)
  let sortedMods := inScopeMods.qsort fun a b => modName a < modName b
  out := out.push "## (b) per module: declarations total (non-meta), reached, unreached; unreached as `name  start-end` sorted by line"
  out := out.push ""
  out := out.push "| module | total | reached | unreached |"
  out := out.push "|---|---|---|---|"
  let mut totDecl := 0
  let mut totUnr := 0
  let mut totSpan := 0
  let mut totUnion := 0
  let mut detail : Array String := #[]
  let mut deadMods : Array Nat := #[]
  let mut metaRows : Array String := #[]
  let mut modsWithDecls := 0
  let mut metaTotal := 0
  let mut metaUnr := 0
  for i in sortedMods do
    let ds := byMod.getD i #[]
    if ds.isEmpty then continue
    modsWithDecls := modsWithDecls + 1
    let nm := ds.filter (!·.isMeta)
    let mm := ds.filter (·.isMeta)
    let unr := (nm.filter (!isReached ·)).qsort fun a b =>
      a.startLine < b.startLine || (a.startLine == b.startLine && a.name.toString < b.name.toString)
    let reachedCnt := nm.size - unr.size
    let reachedMeta := (mm.filter isReached).size
    totDecl := totDecl + nm.size
    totUnr := totUnr + unr.size
    metaTotal := metaTotal + mm.size
    out := out.push s!"| {modName i} | {nm.size} | {reachedCnt} | {unr.size} |"
    if reachedCnt + reachedMeta == 0 && nm.size > 0 then deadMods := deadMods.push i
    if !unr.isEmpty then
      detail := detail.push s!"### {modName i}  ({unr.size} unreached of {nm.size})"
      -- union of line intervals (declarations may overlap)
      let mut covered : Std.HashSet Nat := {}
      for d in unr do
        detail := detail.push s!"{fmtName d.name}  {d.startLine}-{d.endLine}"
        totSpan := totSpan + (d.endLine - d.startLine + 1)
        for l in [d.startLine:d.endLine+1] do covered := covered.insert l
      totUnion := totUnion + covered.size
    -- meta
    let mUnr := (mm.filter (!isReached ·)).qsort fun a b =>
      a.startLine < b.startLine || (a.startLine == b.startLine && a.name.toString < b.name.toString)
    metaUnr := metaUnr + mUnr.size
    if !mUnr.isEmpty then
      metaRows := metaRows.push s!"### {modName i}: {mUnr.size} unreached meta declaration(s) of {mm.size}; file contains reached declarations: {if reachedCnt + reachedMeta > 0 then "yes" else "no"} ({reachedCnt} non-meta, {reachedMeta} meta)"
      for d in mUnr do
        metaRows := metaRows.push s!"  {fmtName d.name}  {d.startLine}-{d.endLine}"
  out := out.push ""
  out := out.push "### unreached declarations"
  out := out ++ detail
  out := out.push ""
  -- (c)
  out := out.push "## (c) modules with no reached declaration (whole module dead), and the modules that import them"
  let importers (i : Nat) : Array Nat := inScopeMods.filter fun j =>
    hdr.moduleData[j]!.imports.any fun imp => imp.module == hdr.moduleNames[i]!
  if deadMods.isEmpty then out := out.push "(none)"
  for i in deadMods do
    let ds := byMod.getD i #[]
    let imps := (importers i).map modName
    out := out.push s!"- {modName i}  ({(ds.filter (!·.isMeta)).size} declarations plus {(ds.filter (·.isMeta)).size} meta, last one ends at line {ds.foldl (fun a d => max a d.endLine) 0}); imported by: {if imps.isEmpty then "(no RBM3D module)" else ", ".intercalate imps.toList}"
  out := out.push ""
  out := out.push "## (d) meta list (not candidates for deletion): unreached syntax/macro/elab/parser/tactic-like declarations"
  if metaRows.isEmpty then out := out.push "(none)"
  out := out ++ metaRows
  out := out.push ""
  out := out.push "## (e) totals"
  out := out.push s!"- modules in scope: {inScopeMods.size}; with counted declarations: {modsWithDecls}"
  out := out.push s!"- declarations (non-meta units): {totDecl}; meta declarations: {metaTotal} (unreached meta: {metaUnr})"
  out := out.push s!"- unreached (non-meta): {totUnr}"
  out := out.push s!"- sum of unreached line spans (end-start+1 per declaration): {totSpan}"
  out := out.push s!"- unreached lines counted once (union of the intervals per module): {totUnion}"
  out := out.push s!"- modules with no reached declaration: {deadMods.size}"
  -- emit in chunks so that no message is huge
  let mut chunk := ""
  let mut cnt := 0
  for l in out do
    chunk := chunk ++ l ++ "\n"
    cnt := cnt + 1
    if cnt ≥ 200 then
      logInfo chunk.trimAsciiEnd.toString
      chunk := ""
      cnt := 0
  if !chunk.isEmpty then logInfo chunk.trimAsciiEnd.toString

end DeadDecls

run_cmd DeadDecls.run
