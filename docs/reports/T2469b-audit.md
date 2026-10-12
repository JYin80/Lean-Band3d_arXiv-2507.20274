Auditor model: claude-opus-5-5
# T2469b audit (L3b2b of T2469: targets 1 (b)-(d), 2, 3, 4; `RBM3D/Graph/BALocReg2B.lean`) — round 1, Mon Oct 12 22:24:53 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2469b-audit1` (detached at t/T2469b = 40493044). Scratch: `scratchpad/T2469b/` (`audit.lean`, `pins.py`).
Scope per CONTROL H257 (3): target 1 (a) (`Graph/BALocReg2`) is merged on main (a931034a) and not audited here; reserve `BALocReg2C` unused.

## 4. Diff, forbidden tokens, build
```
$ git diff --name-status main...t/T2469b ; git merge-base main t/T2469b
A	RBM3D/Graph/BALocReg2B.lean
a931034ab1f655166500325eb04caf0f5379b279
$ git diff main...t/T2469b -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ grep -nE "sorry|admit|native_decide|^axiom|axiom |^inductive|^structure|^class|: Prop|open private" RBM3D/Graph/BALocReg2B.lean   (set_option lines filtered)
(no hit; only set_option linter.* lines 11-22)
$ lake build RBM3D.Graph.BALocReg2B 2>&1 | grep -E "error|warning|sorry|Build completed"
(only replayed style warnings of upstream modules Green/LDEQuad.lean, Defs/Tail.lean; no error) ; exit=0
```
The file is new (sole writable file `RBM3D/Graph/BALocReg2B.lean`); `RBM3D.lean` is not on the branch, the hub adds the root import at merge (rule (A) 4). No merged file edited; no frozen signature touched.

## 1. Statements against the pins (check file `docs/tickets/checks/T2469-check.lean`, Part 2)
```
$ python3 -I pins.py      # pin body vs theorem statement, whitespace-normalised text
T2469_E2Path      baShapePath_e2_tn        identical: True
T2469_MacroAPath  baShapePath_macroA_tn    identical: True
T2469_MacroBPath  baShapePath_macroB_tn    identical: True
T2469_PathBinder  baPathBinder_holds       identical: True
T2469_PathStep    baPathStep_closed        identical: True
T2469_LocReg15    baLocReg15_closed        identical: True
T2469_Binder6     baShapeLLBinder_holds    identical: True
T2469_ConclUpto5  baLocRegConcl_upto5      identical: True
T2469_Upto5       ba_localregular_upto5    identical: True
```
Elaboration check: `audit.lean` = the check file + `import RBM3D.Graph.BALocReg2B` + nine `example : T2469_X := <name>` + the two target 1 (b) check shapes
(`Γ.BAScost_trA`, `Γ.BAScost_trB`, binder text copied from the check) proved by `BALocReg2B_trA`, `BALocReg2B_trB` + `#print axioms`:
```
$ lake env lean scratchpad/T2469b/audit.lean 2>&1 | grep -E "error|axioms|sorry"
'RBM.Graph.baShapePath_e2_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapePath_macroA_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapePath_macroB_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baPathBinder_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baPathStep_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLocReg15_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapeLLBinder_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLocRegConcl_upto5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_localregular_upto5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALocReg2B_trA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALocReg2B_trB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALocReg2B_macroA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALocReg2B_macroB' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Target 1 (b): `BALocReg2B_trA` / `_trB` have exactly the check shapes' hypotheses (`hp`, `hp1`; `hp hq hp1 hq1 hsame hwf1 hwf2`), proved by the
elaboration above. `BALocReg2B_macroA` / `_macroB` add only `hN : Γ.Normal` and the constructor hypotheses (signatures `BALocReg2B.lean:155-158, 173-178`),
as the ticket's 1 (d) allows. Public helper names carry the file stem (§3 (E)).

## 2. Vacuity, hidden hypotheses, cycles
Merged definitions/binders used (signatures read, `BALocReg1.lean`, `BALocReg1B.lean`, `BAEngine.lean`):
```
BALocReg1.lean:566  def BAShapePath (sh) (T) : Prop := ∀ P LT, T P LT → ∀ Q, (sh, Q) ∈ LT → ∀ k, P.img.PathInv2 k → Q.img.PathInv2 k
BALocReg1.lean:631  theorem baPathStep_holds (hX : ∀ sh, sh = e2 ∨ sh = macroA ∨ sh = macroB → BAShapePath sh BAFrameStepTN) : BAPathStep (untag BALocStepT)
BALocReg1B.lean:264 theorem baLocReg15_holds (hX : <same binder>) : BALocReg15
BAEngine.lean:335   theorem ba_localregularX : (∀ sh, ... → BAShapeLL sh BAFrameStepTN) → ∀ p c, 0 < c → ∀ K0 d D, ∃ outs errs, BALocRegConcl ... ∧ ...
```
- `baPathStep_closed := baPathStep_holds baPathBinder_holds`, `baLocReg15_closed := baLocReg15_holds baPathBinder_holds` (`:349, :352`): the binders are discharged
  by the proved `_tn` theorems; no public theorem of the file carries a shape binder, `BAShapePath`/`BAShapeLL`/`BALocRegConcl` appear in a hypothesis only in
  `baLocRegConcl_upto5`, whose premise is concluded by `ba_localregularX baShapeLLBinder_holds` (instance below).
- No new `structure`, `class`, `inductive`, `Prop` def (grep above). Instance data `BALocReg2BInst.outsErT` is a `def` of a list.
- No cycle: the file imports merged modules only; dependencies `BALocReg1`, `BALocReg1B`, `BAShapeO2B`, `BAEngine`, `BALocReg2` are on main.
- No external hypothesis: "Inputs used as hypotheses only: none" (ticket) holds; the unproved `BAsim` is not referenced (`grep -rn 'BAsim\b' RBM3D/Graph/BALocReg2B.lean | wc -l` → `0`).

## 3. Compiled nonempty instances (section 6, `BALocReg2B.lean:389-620`; compiled by the module build above)
| endpoint | example (line) | concrete data, discharge |
|---|---|---|
| `baShapePath_e2_tn` | 470, 487, 521, 526, 550, 558 | `P_B` within (`hTB`, `pathInv2_B` k=1), `P_C` ggSplit (`hTC`, `pathInv2_C` k=2), `P_A` gg (`hTA`, `pathInv2_A` k=2), `baPEr` edge (`normalEr`, `hStepEr`, `pathInv2_Er`), a `p = 2` start term weight step (`baPathInit_holds 2`), hand-built `baPL`; tag existence by `decide +kernel` |
| `baShapePath_macroA_tn` | 470 | `P_B` `within`, `macroA` output exists (`decide +kernel`), `pathInv2_B` |
| `baShapePath_macroB_tn` | 487, 495 | `P_C`, j = 0, stage-1 (`d2`-`d4`) and stage-2 (`tr.gg2`) outputs |
| `BALocReg2B_trA`, `_macroA` | 567 | `baPB`, `pB`, normality by `decide`, `pathInv2_B` |
| `BALocReg2B_trB`, `_macroB` | 574 | `baPC`, `pC`, `qC`, `hsame`/`hwf1`/`hwf2` by `decide`, `pathInv2_C` |
| `baPathBinder_holds` | 543, 584, 591 (through `baPathStep_closed`, `baLocReg15_closed`) | see observation O1 |
| `baPathStep_closed` | 543 | twisted `edge` step at `baPEr` (`stepErT` proved), `PathInv2 1` proved (`pathInv2_ErT`), `e2` output exhibited |
| `baLocReg15_closed` | 584, 591 | `BALocReg1B_reach_locStd`: `p = 2` start term, `¬ P0.g.LocStd`, reached `Q` with `Q.g.LocStd`, `nM = 1`; and at a start term (`BAReach.refl`) |
| `baShapeLLBinder_holds` | 478 | `P_B` within, `e2`/`macroA` outputs, crude cost bound `-4` proved (`BAScost_locCostGeA_crude`) |
| `baLocRegConcl_upto5` | 599 | `p=2, c=1/4, K0=2, d=3, D=10`; premise from `ba_localregularX baShapeLLBinder_holds` |
| `ba_localregular_upto5` | 607 | same parameters + expectation identity at `flowP_data` (`d=3, L=4, W=2`, `ℓ0`), every hypothesis discharged |
No `N = 0`, empty index, collapsed window or `False` premise; the parent invariants `PathInv2 k` are proved at every witness, not assumed.

## 5. Paper deltas
`docs/paper-deltas.md:257-260` holds `T2469a`-`T2469c` (L3b2a). This report's candidates in `T2469b-prove.md` (d): `T2469d` (stage-2 transfer graph
`Γ → tr`, paper `B_graphical_lemmas.tex:393-405, 416` gives no path argument) and `T2469e` (BA composed statement vs band `lw_localregular_upto5`:
`PathInv2`, `n_M ≤ p`, `LocReg2` on `outs ++ errs`; `LocReg1`, `LocReg345` on image and shadow on `outs`). The Lean statements equal the pins verbatim;
the only Lean/paper differences (stage-2 route, statement shape of (1)-(5) at BA) are covered by `T2469a`, `T2469d`, `T2469e`.

## Observations (no RETURN)
- O1. `baPathBinder_holds` has no example of its own; it is applied in every instance of `baPathStep_closed`/`baLocReg15_closed`, and it is the
  conjunction of the three `_tn` theorems, each instantiated nondegenerately (table). Coverage is adequate.
- O2. In 599/607 the lists `outs`, `errs` are the existential output of `ba_localregularX`; `outs ++ errs ≠ []` is not shown (prove report (b) item 10
  states this). The conclusions of `baLocRegConcl_upto5` are shown non-vacuously through `baLocReg15_closed` at a concrete reached `Q` (584).
  Same pattern as the merged `BAEngineInst` (`BAEngine:483`).
- O3. `BALocReg2B_trB` keeps three unused hypotheses (`hsame`, `hwf1`, `hwf2`) to fit the check shape; the lemma is thereby weaker than provable, not a
  defect of the pinned targets.
- O4. The prove report's section (a) points to `T2469-prove.md` (a); allowed by the H257 (3) split.

## Verdict per target
| target | verdict |
|---|---|
| 1 (b) `BALocReg2B_trA`, `_trB`, `_macroA`, `_macroB` | PASS |
| 1 (c) `baShapePath_e2_tn`, `_macroA_tn`, `_macroB_tn` | PASS |
| 1 (d) `baPathBinder_holds` | PASS |
| 2 `baPathStep_closed`, `baLocReg15_closed` | PASS |
| 3 (a) `baShapeLLBinder_holds`, (b) `baLocRegConcl_upto5`, (c) `ba_localregular_upto5` | PASS |
| 4 instances | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
