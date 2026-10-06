Auditor model: claude-opus-5-5

# T2255 (LW-14c) audit, round 1 — Tue Oct  6 06:19:07 UTC 2026

Audit worktree `RBM3D-wt/T2255-audit1`, detached at `t/T2255` = `ba20118` (merge base with `main`: `88ee6fd`).
Pins: `docs/tickets/checks/T2255-check.lean` section 2. Paper: `paper/tex/B_graphical_lemmas.tex:66-110`, `7_8:895-930`.

## 1. Scope of the diff
```
$ git diff --stat main...t/T2255
 RBM3D/Graph/LWExpTerm3.lean | 2301 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    2 +
$ git diff main...t/T2255 -- RBM3D/Test/Axioms.lean | grep '^[+-] '
+   `RBM.Gauss.Sizes.LWG5Expand, -- `(eq:sizeGammamu_E)`, `B:91-108`: ... premise of `lwExpG5'_of_expand` (T2255): LW-14e   [owedProps, after LWExpG5']
+   `RBM.Gauss.Sizes.LWAttached, -- every internal molecule ... (`B:84-86`): a data condition on the graph, hypothesis of `lwGraphPrec1` (T2255)   [structuralProps]
$ git merge-tree --write-tree main t/T2255 >/dev/null; echo $?     # main now at 193512b (T2254 merged after the base)
0
```
Only the two sole writable files; no deletion in the registry (as the ticket requires); no merged file touched.

## 2. Statements against the pins (script)
Section 2 of the check file copied verbatim into `namespace RBM.Gauss.Sizes.T2255Audit` (file `pins.lean`, importing
`RBM3D.Graph.LWExpTerm3`), followed by:
```
example (k s : Bool) : LWG5GraphPin k s = RBM.Gauss.Sizes.LWG5Graph k s := rfl
example ... : LWG5DataPin sz n E t ω = RBM.Gauss.Sizes.LWG5Data sz n E t ω := rfl
example (P) : LWAttachedPin P ↔ RBM.Gauss.Sizes.LWAttached P := Iff.rfl
example (d) : LWG5ExpandPin d ↔ RBM.Gauss.Sizes.LWG5Expand d := Iff.rfl
example (d) : LwExpTerm3BridgePin d ↔ RBM.Gauss.Sizes.LwExpTerm3Bridge d := Iff.rfl
example (d) : LwGraphPrec1Pin d ↔ RBM.Gauss.Sizes.LwGraphPrec1 d := Iff.rfl
example (d) : LwExpG5'OfExpandPin d ↔ RBM.Gauss.Sizes.LwExpG5'OfExpand d := Iff.rfl
example (d) : LwCutExpOfExpandPin d ↔ RBM.Gauss.Sizes.LwCutExpOfExpand d := Iff.rfl
example (d) : LwTermEXPOfExpandPin d ↔ RBM.Gauss.Sizes.LwTermEXPOfExpand d := Iff.rfl
example : ∀ d, LwExpTerm3BridgePin d := @RBM.Gauss.Sizes.lwExpTerm3_bridge
example : ∀ d, LwGraphPrec1Pin d := @RBM.Gauss.Sizes.lwGraphPrec1
example : ∀ d, LwExpG5'OfExpandPin d := @RBM.Gauss.Sizes.lwExpG5'_of_expand
example : ∀ d, LwCutExpOfExpandPin d := @RBM.Gauss.Sizes.lwCutExp_of_expand
example : ∀ d, LwTermEXPOfExpandPin d := @RBM.Gauss.Sizes.lwTermEXP_of_expand
#print axioms (5 targets, 5 instances)
```
```
$ lake env lean pins.lean
'RBM.Gauss.Sizes.lwExpTerm3_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwGraphPrec1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpG5'_of_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwCutExp_of_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwTermEXP_of_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_prec1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_G5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm3_inst_term' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
All 9 definitions are the pins up to the suffix (by `rfl`/`Iff.rfl`), all 5 targets have exactly the pinned type.

Against the paper (by reading, pins fixed by the dispatcher):
* `LWG5Graph`: solid `G_{xα} G_{αγ} G_{γβ} G_{βy}` then `Ḡ_{xy}` (`s=false`, `SEdge.σ=false` = `star`) or `G_{yx}`;
  waved `(γ,α)` with `col = k` (`S` or `S⁺`), `(α,β)` black `S` — matches `B:68` `S_{γα}S_{αβ}(G_{xα}G_{αγ}G_{γβ}G_{βy}Ḡ_{xy})`.
* Target 2 is an exact identity (proved), the powers `t^{1|2}` and `W^{-2d}` are the bridge's; `B:68`'s factor `m` sits
  in T2243's `LWExpG5'` reduction (not here).
* Target 3 = `(Gammamuxy)` (`B:88`) with `q = n_M ≤ 1`, external vertices in distinct molecules (this is the setting of
  `def_auxgraph`, `7_8:895`, and a hypothesis of the merged `LWGtoAG`), attachment `LWAttached` (`B:84-86`, asserted
  in the paper, a hypothesis here), and the extra factor `t^{n_W}` (stronger than the paper; T2255a).
* Targets 4–5 are conditional on `LWG5Expand` (`(eq:sizeGammamu_E)` + the expansion `𝒢 =_E Σ Γ_μ`, `B:78-108`) and on
  LW-14d's three pins, as the ticket states. No special case passed off as the general statement: the unconditional
  `lwExpG5'_holds` etc. are explicitly deferred (ticket "Final assembly rule").

## 3. Build, hygiene, registry
```
$ lake build RBM3D.Graph.LWExpTerm3 2>&1 | grep -c "error"; tail -2
0
Build completed successfully (3881 jobs).
exit=0
$ lake env lean RBM3D/Graph/LWExpTerm3.lean     # direct re-elaboration of the file
exit=0   (only linter warnings: longLine in the module docstring)
$ grep -nE "\bsorry\b|\badmit\b|^axiom|native_decide" RBM3D/Graph/LWExpTerm3.lean
(no output)
$ lake build RBM3D 2>&1 | tail -1         # root at the branch base, imports unchanged
exit=0
$ printf 'import RBM3D\nimport RBM3D.Graph.LWExpTerm3\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean
axiom audit: 7591 theorems, 2551 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
  RBM.Gauss.Sizes.LWExpG5': 4 [no certificate]
  RBM.Gauss.Sizes.LWG5Expand: 3 [no certificate]
premises found by scanning: 155 (borrowed 1, owed 99, structural 38, refuted 6, superseded 11).
exit=0
```
Public names without the stem `lwExpTerm3_` (script over `theorem|def|…` headers) are exactly the pinned ones:
```
LWAttached lwCutExp_of_expand LwCutExpOfExpand lwExpG5'_of_expand LwExpG5'OfExpand LwExpTerm3Bridge LWG5Data
LWG5Expand LWG5Graph lwGraphPrec1 LwGraphPrec1 lwTermEXP_of_expand LwTermEXPOfExpand
```
Name clash against current `main` (`git grep -w -F NAME main -- 'RBM3D/*.lean'`, excluding the new file): 0 hits for each
of the 13 names above and for the prefix `lwExpTerm3_`.

## 4. Hidden hypotheses, vacuity, cycles
* Dependencies: imports are `LWExpTerm2`, `AuxGraph`, `AuxGraph2`, `ScaleFacts`, `IBPPoly` (all merged); no import of
  `RBM3D`; nothing downstream imported, so no cycle.
* Hypotheses of the targets are signature-level only: `STFlow` (structural, registered), `STLocalEntry`, `STLmax`
  (target 3), the five ST pins of `LWExpG5'` (target 4), `LWG5Expand` and `LWExpI1K/I23K/I41K` (targets 4–5) — all owed
  pins in `owedProps`. No new structure with Prop fields.
* `LWG5Expand` is an owed pin (LW-14e), not an external input; its consistency evidence is the preflight's order count
  (`ords.py`, (a)) and the merged `oe2x_graph_E` (exact identity of expectations; `GaussIBP sz` is unconditional by
  `RBM.Green.gaussIBP : ∀ sz, GaussIBP sz`, `IBPPoly.lean:305`). Targets 4–5 are therefore conditional, not vacuous by
  construction; their satisfiability rests on LW-14e (see Observation 1).

## 5. Compiled nonempty instances (in the file, compiled above)
| endpoint | instance | data | hypotheses left |
|---|---|---|---|
| `lwExpTerm3_bridge` | `lwExpTerm3_inst_bridge` (`:2248`) | `d=3`, `sz0`, `n=0`, `E=STflowE z0 0` (`|E|<2` by `st6_flowE_lt_two`), `t=1/16`, all `k,s,a,b` | none |
| `lwGraphPrec1` | `lwExpTerm3_inst_prec1` (`:2232`) | `d=3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `sz0`, `z0` (`flow_z0`), `tInst ≡ 1/16` (`tInst_range`), graph `lwExpTerm3_instGraph` | `STLocalEntry`, `STLmax` (owed pins) |
| `lwExpG5'_of_expand` | `lwExpTerm3_inst_G5` (`:2262`) | same | `LWG5Expand 3`, five ST pins |
| `lwCutExp_of_expand` | `lwExpTerm3_inst_cut` (`:2279`) | same | LW-14d pins, `LWG5Expand 3`, five ST pins |
| `lwTermEXP_of_expand` | `lwExpTerm3_inst_term` (`:2291`, into `inst_LWtermEXP`) | same | same |

The graph of instance (3) is nondegenerate: external `x, y`, one internal `α`, 5 solid, 2 waved, 3 `×`-dotted edges;
`nM = 1`, `Normal`, `LWAttached`, external molecules distinct, all by `decide` (`:2208-2221`), `scalingOrder = 7` (`:2243`).
Every deterministic hypothesis (`3 ≤ d`, positivity of `κ, ε, 𝔡`, the flow, `0 ≤ t ≤ lemT`, the graph facts) is
discharged; no `N = 0`, empty index, collapsed window or `False` premise.

## 6. Paper deltas
Proposed in the prove report (d): T2255a (`B:84`, factor `t^{n_W}`, `S⁺ = O(t)` proved in-file), T2255b (`B:74`, `x = y`
term needs `B_{t,0} ≥ c W^{-d}` via `STBctl_ge`), T2255c (`ξ' = min(N^τ ξ, Ψ)` on all edges), T2255d (route: `≺ → 𝔼`
applied to `t^{-n_W}Γ`). These cover the two expected deltas (a), (b) and the statement differences of target 3.

## 7. Verdicts
| target | verdict |
|---|---|
| 1 vocabulary `LWG5Graph`, `LWG5Data`, `LWAttached` | PASS |
| 2 `lwExpTerm3_bridge` | PASS |
| 3 `lwGraphPrec1` | PASS |
| 4 `lwExpG5'_of_expand` | PASS |
| 5 `lwCutExp_of_expand`, `lwTermEXP_of_expand` | PASS |
| 6 instances (1)–(3) | PASS |
| registry (`LWG5Expand` owed, `LWAttached` structural, no deletion) | PASS |

Overall: **PASS**.

## 8. Observations (no RETURN)
1. `LWAttached` and "external vertices in distinct molecules" are hypotheses of target 3 that the paper asserts as
   properties of the `Γ_μ` (`B:84-86`, `7_8:895`); in Lean they are obligations of `LWG5Expand` (LW-14e) for every
   output graph, including graphs produced by the partition step, where an internal vertex may be merged with `x` or
   `y`. LW-14e's preflight should check that no output has `x`, `y` in one molecule; if one does, `LWG5Expand` as pinned
   is false and targets 4–5 become vacuous. The dispatcher may want this recorded on the LW-14e ticket; it does not
   change this ticket's statements.
2. Not used by the proofs (carried as pinned): `STLmax` in target 3 (report (b) says so); `LWAvgLaw`, `STLK`, `STDecay`
   in target 4. Statements therefore slightly stronger in content than needed; no change required.
3. The branch base is `88ee6fd`; `main` has since merged T2254 (LW-14d), which deleted the `LWExpI1K/I23K/I41K` registry
   lines. `git merge-tree` is clean; the hub's full build at merge is the final check of the combined registry.
