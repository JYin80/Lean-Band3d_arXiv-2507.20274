/-
DeadDecls (T2273, DECISIONS §244; RBM3D roots and groups T2522, DECISIONS §355 (1), §367): report
every unreachable declaration of the `RBM3D` library.

Run from the main worktree (it needs the built `RBM3D` library):

    lake env lean docs/claude-team/tools/DeadDecls.lean

Prints a report on stdout.  Nothing is written, the library is not modified.

RBM3D roots (T2522).  Core: `final_shape`, `Thm27`, `Thm27_of_L32`, `band_terminal`; the constants
named by the `example`s of `RBM3D/Main/FinalShape.lean` (listed by hand, `exampleRoots`); every
constant of the namespace `RBM.Audit` and its sub-namespaces.  Optional groups `G1`-`G4`
(`groups`) are reported beyond the core: for each, the extra declarations and lines its closure
adds to the core closure.  Section (g) lists the `Name` literals of every `Name`-valued constant
of `RBM.Audit` (the registry lists of `RBM3D/Test/Axioms.lean`) that are unreached in the core, with
their line in that file (read from the current directory).

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

/-- A private declaration `n` of module `m`: its mangled name. -/
def privName (m : Name) (n : Name) : Name := Name.mkNum (`_private ++ m) 0 ++ n

/-- Core roots by full name (T2522, DECISIONS §355 (1), §367): the four endpoints of
`RBM3D/Main/FinalShape.lean` and `RBM3D/Main/BandTerminal.lean`. -/
def fixedRoots : List Name :=
  [`RBM.Endpoints.final_shape, `RBM.Endpoints.Thm27, `RBM.Endpoints.Thm27_of_L32,
   `RBM.Endpoints.band_terminal]

/-- Core roots added by hand: constants named by the statement and the proof of the five
`example`s of `RBM3D/Main/FinalShape.lean` (§Instances and §BAInstances); an `example` is not a
constant, so they are listed by hand.  Full names, resolved under the `open`s of that file.
`FinalShape_hg` is `private` there. -/
def exampleRoots : List Name :=
  [`RBM.Univ.UNL32, `RBM.Endpoints.Inst.inst_decol, `RBM.Endpoints.Inst.inst_locSC,
   `RBM.Endpoints.Inst.inst_QUE, `RBM.Endpoints.Inst.inst_BUniv, `RBM.Endpoints.Inst.inst_QDiff,
   privName `RBM3D.Main.FinalShape `RBM.Endpoints.FinalShape_hg,
   `RBM.Univ.BAInst.S0, `RBM.Univ.BAInst.S0_adm, `RBM.BA.UNPinsInst.clsκ,
   `RBM.BA.UNPinsInst.clsκ_pos, `RBM.BA.UNPinsInst.fp, `RBM.Univ.BAInst.S0_bulk,
   `RBM.Univ.UNInst.bump, `RBM.Univ.UNInst.bump_testFun]

/-- Optional groups (T2522): name, description, roots (added to the core roots for that group's
closure).  The `example`s of the named file are listed by hand under that file's `open`s. -/
def groups : List (String × String × List Name) :=
  [("G1", "constants of the `example`s in Main/BandTerminal.lean §Instances",
    [`RBM.Endpoints.Inst.inst_decol, `RBM.Endpoints.Inst.inst_locSC, `RBM.Endpoints.Inst.inst_QUE,
     `RBM.Endpoints.Inst.inst_BUniv, `RBM.Endpoints.Inst.inst_QDiff,
     `RBM.Endpoints.Inst.inst_bridge_loc, `RBM.Endpoints.Inst.inst_bridge_que,
     `RBM.Endpoints.band_terminal, `RBM.Endpoints.unBUniv_of_L32, `RBM.Endpoints.decol_holds,
     `RBM.Endpoints.locSC_holds, `RBM.Endpoints.QUE_holds, `RBM.Endpoints.QDiff_holds,
     `RBM.Endpoints.unOUClaims_holds, `RBM.Endpoints.unOUQUE_holds, `RBM.Univ.UNOUQUE,
     `RBM.Univ.UNOUDiag, `RBM.Gauss.SizesInst.sz0, `RBM.Gauss.SizesInst.sz0_admissible,
     `RBM.Univ.UNL32]),
   ("G2", "constants of the `example`s in BA/MAPins.lean",
    [`RBM.Univ.BAInst.S0, `RBM.Univ.BAInst.S0_adm, `RBM.BA.UNPinsInst.clsκ,
     `RBM.BA.UNPinsInst.clsκ_pos, `RBM.BA.UNPinsInst.fp, `RBM.Univ.BAInst.S0_bulk,
     `RBM.Univ.UNInst.bump, `RBM.Univ.UNInst.bump_testFun,
     privName `RBM3D.BA.MAPins `RBM.BA.MAPins_hg, `RBM.BA.BAThm27L, `RBM.BA.BAlocSCFixed,
     `RBM.BA.BAQDiffFixed, `RBM.BA.BAMANetLoc, `RBM.BA.BAMADecol, `RBM.BA.BAMANetQD,
     `RBM.BA.BAMAQUE, `RBM.BA.BAMAFixed, `RBM.Univ.UNMLOutBA, `RBM.Univ.BAInst.inst_locAvg_domain,
     `RBM.BA.BAendDom, `RBM.BA.BAbulk, `RBM.BA.BAbulk_window, `RBM.BA.UNLocAvgBAAt,
     `RBM.BA.UNTrLocalBAAt, `RBM.BA.UNTrLocalInitBAAt', `RBM.Univ.UNLocAvgBA,
     `RBM.Univ.UNTrLocalBARow, `RBM.Univ.UNTrLocalInitBARow', `RBM.BA.UNLocAvgBA_iff_at,
     `RBM.BA.UNTrLocalBARow_iff_at, `RBM.BA.UNTrLocalInitBARow'_iff_at]),
   ("G3", "the general-`d` BA forms",
    [`RBM.BA.baThm27L_any, `RBM.BA.baThm27L_of_ML, `RBM.BA.baEnd_BUnivL_of_ML]),
   ("G4", "`bUniv_holds` and the constants of the `example`s in Main/BUnivHolds.lean",
    [`RBM.Endpoints.bUniv_holds, `RBM.Univ.kPoint, `RBM.Gauss.Sizes.seqXmat_isHermitian,
     `RBM.Gauss.Xmat_isHermitian, `RBM.Gauss.Sizes.seqP, `RBM.Univ.gueP,
     `RBM.Univ.UNInst.bump, `RBM.Univ.UNInst.bump_testFun, `RBM.Gauss.SizesInst.sz0,
     `RBM.Gauss.SizesInst.sz0_admissible, `RBM.Univ.UNNormBandRow, `RBM.Univ.UNL32,
     `RBM.Univ.UNMLOut, `RBM.Univ.UNLocAvgBand, `RBM.Univ.UNQueBand,
     `RBM.Univ.UNGUESchurTail])]

/-- Sanity: names whose status in the core closure is reported (ticket T2522). -/
def sanity : List Name :=
  [`RBM.BA.baThm27L_three, `RBM.BA.unMLOutBA_three, `RBM.Endpoints.bUniv_holds]

/-- The file whose name lists are reported in section (g). -/
def registryFile : String := "RBM3D/Test/Axioms.lean"

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

/-- A `Name` literal written as an expression (`Name.mkStr1 ..`, `Name.str p s`, ...). -/
partial def exprToName? (e : Expr) : Option Name :=
  match e with
  | .const c _ => if c == ``Lean.Name.anonymous then some .anonymous else none
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .const c _ =>
      if (c == ``Lean.Name.str || c == ``Lean.Name.mkStr) && args.size == 2 then
        match exprToName? args[0]!, args[1]! with
        | some p, .lit (.strVal s) => some (.str p s)
        | _, _ => none
      else if c.getPrefix == ``Lean.Name && (c.toString.startsWith "Lean.Name.mkStr") && args.size > 0 then
        args.foldl (init := some Name.anonymous) fun acc a =>
          match acc, a with
          | some p, .lit (.strVal s) => some (.str p s)
          | _, _ => none
      else none
    | _ => none

/-- The `Name` literals occurring in `e`, in order. -/
partial def collectNames (e : Expr) (acc : Array Name) : Array Name :=
  match exprToName? e with
  | some n => if n.isAnonymous then acc else acc.push n
  | none =>
    match e with
    | .app f a => collectNames a (collectNames f acc)
    | .lam _ t b _ => collectNames b (collectNames t acc)
    | .forallE _ t b _ => collectNames b (collectNames t acc)
    | .letE _ t v b _ => collectNames b (collectNames v (collectNames t acc))
    | .mdata _ b => collectNames b acc
    | .proj _ _ b => collectNames b acc
    | _ => acc

/-- First line (1-based) in `[s, e]` of `lines` that contains the name literal `` `n `` as a whole token. -/
def findNameLine (lines : Array String) (s e : Nat) (n : Name) : Option Nat := Id.run do
  let pat := "`" ++ n.toString
  for i in [s:e+1] do
    if h : i - 1 < lines.size then
      let l := lines[i - 1]
      let parts := l.splitOn pat
      for p in parts.drop 1 do
        if p.isEmpty || p.front == ' ' || p.front == ',' || p.front == ']' then return some i
  return none
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
  -- roots (core)
  let mut rootsUsed : Array (Name × String) := #[]
  for r in fixedRoots do rootsUsed := rootsUsed.push (r, "core: ticket root")
  for r in exampleRoots do
    if !fixedRoots.contains r then
      rootsUsed := rootsUsed.push (r, "core: added by hand, constant of the `example`s in Main/FinalShape.lean")
  let auditNames := modOf.toList.filterMap fun (c, _) => if `RBM.Audit |>.isPrefixOf c then some c else none
  let auditSorted := auditNames.toArray.qsort (fun a b => a.toString < b.toString)
  for r in auditSorted do rootsUsed := rootsUsed.push (r, "core: namespace RBM.Audit")
  let coreRoots : Array Name := rootsUsed.map (·.1)
  -- closure from a set of roots
  let closure (roots : Array Name) : Std.HashSet Name × Std.HashMap Name Name := Id.run do
    let mut reached : Std.HashSet Name := {}
    let mut parent : Std.HashMap Name Name := {}
    let mut stack : Array Name := #[]
    for r in roots do
      if env.contains r then stack := stack.push r
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
    return (reached, parent)
  let missing : Array Name := coreRoots.filter fun r => !env.contains r
  let (reached, parent) := closure coreRoots
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
    out := out.push s!"- {fmtName r}  ({why}){ok}"
  out := out.push s!"- ({auditSorted.size} constants in RBM.Audit and its sub-namespaces; {reached.size} in-scope constants reached in the core)"
  if !missing.isEmpty then out := out.push s!"MISSING ROOTS: {missing}"
  for (g, desc, rs) in groups do
    out := out.push s!"- {g} ({desc}; optional, not part of the core closure): {rs.length} roots"
    for r in rs do
      out := out.push s!"  - {g}: {fmtName r}{if env.contains r then "" else "  [MISSING]"}"
  out := out.push ""
  out := out.push "## sanity checks (core closure)"
  let rootReached := coreRoots.all fun r => reached.contains r
  out := out.push s!"- every core root reached: {rootReached}"
  for n in sanity do
    let r := reached.contains n
    out := out.push s!"- {n}: {if r then "reached" else "UNREACHED"} in the core"
    if r then
      let mut chain : Array Name := #[n]
      let mut cur := n
      for _ in [0:200] do
        match parent[cur]? with
        | some p => chain := chain.push p; cur := p
        | none => break
      out := out.push s!"  reached via (first discovered path, from the name up to a root): {" <- ".intercalate (chain.toList.map fmtName)}"
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
  -- (f) optional groups
  out := out.push ""
  out := out.push "## (f) optional groups: declarations and lines kept alive beyond the core closure"
  out := out.push ""
  let isCoreReached (d : Decl) : Bool := reached.contains d.name
  for (g, desc, rs) in groups do
    let (reachedG, _) := closure (coreRoots ++ rs.toArray)
    let inCore := rs.filter fun r => reached.contains r
    let notCore := rs.filter fun r => !reached.contains r
    let extra := decls.filter fun d => reachedG.contains d.name && !isCoreReached d
    let extraNM := extra.filter (!·.isMeta)
    let extraM := extra.filter (·.isMeta)
    let mut spanTot := 0
    let mut perMod : Std.HashMap Nat (Nat × Nat) := {}
    let mut covered : Std.HashMap Nat (Std.HashSet Nat) := {}
    for d in extraNM do
      let sp := d.endLine - d.startLine + 1
      spanTot := spanTot + sp
      let (c, l) := perMod.getD d.modIdx (0, 0)
      perMod := perMod.insert d.modIdx (c + 1, l + sp)
      let mut cs := covered.getD d.modIdx {}
      for l in [d.startLine:d.endLine+1] do cs := cs.insert l
      covered := covered.insert d.modIdx cs
    let union := covered.fold (fun a _ cs => a + cs.size) 0
    out := out.push s!"### {g}: {desc}"
    out := out.push s!"- roots: {rs.length}; already reached in the core: {inCore.length}; not reached in the core: {notCore.length}{if notCore.isEmpty then "" else " (" ++ ", ".intercalate (notCore.map fmtName) ++ ")"}"
    out := out.push s!"- extra over the core: {extraNM.size} declarations (non-meta), {extraM.size} meta declarations; sum of line spans {spanTot}; lines counted once (union per module) {union}; modules touched {perMod.size}"
    let top := (perMod.toList.toArray.qsort fun a b =>
      a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.2.2 > b.2.2) ||
        (a.2.1 == b.2.1 && a.2.2 == b.2.2 && modName a.1 < modName b.1)).toList.take 5
    out := out.push s!"- five largest modules it keeps alive (module: declarations, line spans):"
    if top.isEmpty then out := out.push "  (none: the group is inside the core)"
    for (mi, (c, l)) in top do
      out := out.push s!"  - {modName mi}: {c} declarations, {l} lines"
    out := out.push ""
  -- (g) name registry
  out := out.push s!"## (g) name lists of the Audit registry (`{registryFile}`): names unreached in the core"
  let src ← (try liftIO (IO.FS.readFile registryFile) catch _ => pure "")
  let lines := (src.splitOn "\n").toArray
  out := out.push s!"- source file read: {lines.size} lines"
  let regDefs := auditSorted.filter fun c =>
    match env.find? c with
    | some ci => (ci.value?.isSome) && !ci.type.isForall && ci.type.getUsedConstants.contains ``Lean.Name
    | none => false
  let mut regTotal := 0
  let mut regScope := 0
  let mut regUnr := 0
  for c in regDefs do
    let some ci := env.find? c | continue
    let some v := ci.value? | continue
    let ns := collectNames v #[]
    let (s, e) := (rangeOf c).getD (0, 0)
    let inSc := ns.filter inScope
    let unr := inSc.filter fun n => !reached.contains n
    let notConst := ns.filter fun n => !env.contains n
    regTotal := regTotal + ns.size
    regScope := regScope + inSc.size
    regUnr := regUnr + unr.size
    out := out.push s!"### {c}  (lines {s}-{e}): {ns.size} names, {inSc.size} in scope, {unr.size} unreached in the core, {notConst.size} not constants"
    let withLine := (unr.map fun n => ((findNameLine lines s e n).getD 0, n)).qsort fun a b =>
      a.1 < b.1 || (a.1 == b.1 && a.2.toString < b.2.toString)
    for (ln, n) in withLine do
      out := out.push s!"  {n}  line {ln}"
    for n in notConst do
      out := out.push s!"  (not a constant of the environment) {n}"
  out := out.push s!"- totals over {regDefs.size} name lists: {regTotal} names, {regScope} in scope, {regUnr} unreached in the core"
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
