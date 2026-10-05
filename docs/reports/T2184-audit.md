Auditor model: claude-opus-5-5

# T2184 audit (LW-10c1, `Graph/LocalRegular6a`) — round 1, Mon Oct  5 15:02:02 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2184-audit1`, detached at `t/T2184` = `7889bd2`; scratch in `$SP/T2184/`.

## 1. Diff scope, forbidden tokens
```
$ git diff --stat main...t/T2184
 RBM3D/Graph/LocalRegular6a.lean | 1188 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 1188 insertions(+)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |implemented_by|extern|unsafe|@\[csimp" RBM3D/Graph/LocalRegular6a.lean
(only docstring hits for the word "external": lines 31, 39, 88, 143, 165, 399, 501, 502, 1059, 1119; no token)
$ sed -n 6p RBM3D/Graph/LocalRegular6a.lean
import RBM3D.Graph.LocalRegular2
```
Sole writable file only; `RBM3D/Test/Axioms.lean` untouched (expected by the ticket: none owed). No merged file modified.

## 2. Build and axioms
```
$ lake build RBM3D.Graph.LocalRegular6a ; echo exit=$?     # build.log: no warning/error line names LocalRegular6a
✔ [3385/3385] Built RBM3D.Graph.LocalRegular6a (4.3s)
Build completed successfully (3385 jobs).
exit=0
$ lake env lean RBM3D/Graph/LocalRegular6a.lean ; echo exit=$?     # recompiled from source
exit=0
```
`#print axioms` (scratch `audit_pins.lean`, `lake env lean`, run in the audit worktree):
```
'RBM.Graph.LGraph.scost_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_cons_loop_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_le_of_lvl1Split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_partition_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scost_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.nElem_eq_zero_of_locStd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.locReg6_of_locCostGe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.locReg6far_of_locCostGe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.fxyPowGraph_locCostGe' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.fxyPowGraph_locReg6Inv' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Every declaration of the module (scratch `audit_ax.lean`, `Lean.collectAxioms` over `getModuleIdxFor? = LocalRegular6a`):
```
module decls: 152; axioms used by any: [Quot.sound, Classical.choice, propext]
exit=0
```
Registry pre-check (DECISIONS §20 (2)):
```
$ printf 'import RBM3D\nimport RBM3D.Graph.LocalRegular6a\n\n#assert_rbm_axioms\n' > AuditPre_tmp.lean ; lake env lean AuditPre_tmp.lean
axiom audit: 5538 theorems, 1977 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
exit=0
```

## 3. Statements against the pins
Target 1 (19 definitions) against section 2 of `docs/tickets/checks/T2184-check.lean`:
```
$ awk '/^section Pattern/{f=1} f{print} /^end Prims/{if(f){exit}}' <check> > v_check.txt ; (same on the file) > v_file.txt
$ wc -l v_check.txt v_file.txt ; diff v_check.txt v_file.txt && echo "DIFF EMPTY" ; grep -c '^def' v_file.txt
     129 v_check.txt
     129 v_file.txt
DIFF EMPTY
19
$ grep -n "^open\|^namespace\|^noncomputable section" RBM3D/Graph/LocalRegular6a.lean | head -3
102:noncomputable section
104:namespace RBM.Graph
(no file-level `open`; `open Classical in` only per declaration, as in the check file)
```
Targets 2–6 (11 theorems): the 11 Pins of section 3 copied verbatim by `awk` into `namespace RBM.Graph.AuditPins`
(`open RBM RBM.Graph`, so `LGraph.scost` etc. resolve to the file's definitions), each discharged by the file's theorem as a term:
```
theorem a1 : ScostPermPin := @LGraph.scost_perm
theorem a2 : ScostRelabelPin := @LGraph.scost_relabel
theorem a3 : ScostConsLoopPin := @LGraph.scost_cons_loop_ge
theorem a4 : ScostSplitPin := @LGraph.scost_le_of_lvl1Split
theorem a5 : ScostPartitionPin := @LGraph.scost_partition_ge
theorem a6 : ScostBotPin := @LGraph.scost_bot
theorem a7 : NElemLocStdPin := @LGraph.nElem_eq_zero_of_locStd
theorem a8 : LocReg6OfLocCostGePin := fun _ _ hQ h => locReg6_of_locCostGe hQ h
theorem a9 : LocReg6FarOfLocCostGePin := fun _ _ hQ hxy h => locReg6far_of_locCostGe hQ hxy h
theorem a10 : FxyLocCostGePin := fxyPowGraph_locCostGe
theorem a11 : FxyLocReg6InvPin := fxyPowGraph_locReg6Inv
$ lake env lean AuditPins_tmp.lean
'RBM.Graph.AuditPins.a1' … 'RBM.Graph.AuditPins.a11' depends on axioms: [propext, Classical.choice, Quot.sound]   (11 lines)
```
(That run's only error was in an appended `#eval` helper (`OfNat MessageData 0`), rerun as `audit_ax.lean`, exit 0, §2.)
Result: every target states its Pin exactly, with no added hypothesis and no reordering (the term-level `fun` in a8/a9 only
moves the implicit `{Q} {k}` to the Pin's explicit binders). Quantifier order: no `∀ᶠ`, no scale; the only parameter is `p`
(§29 checklist of the ticket: empty).

## 4. Hidden hypotheses, vacuity, cycles
- The definitions are the pinned text (diff empty); no structure is introduced, so no hypothesis sits in a field.
  `LocCostGe` is `∀ s, (far → ¬ s x y) → k ≤ scost P.g s` (a lower bound over all setoids; not vacuous: `far = true`
  still allows `⊥`, which separates `inl (P.ext 0)`, `inl (P.ext 1)` whenever `ext 0 ≠ ext 1`).
  `LocReg6Inv` = `Normal ∧ CircIffLoop ∧ LocCostGe false 2p ∧ LocCostGe true 3p`: all four conjuncts concluded by
  `fxyPowGraph_locReg6Inv`, not assumed.
- No external hypothesis anywhere (no limit check owed). `ScostLL` is a hypothesis of no theorem of the file.
- Dependencies: only merged modules (import `RBM3D.Graph.LocalRegular2`) and the file's `localReg6a_` helpers; no cycle.
- Public names: the only non-`localReg6a_` declarations are the 19 pinned definitions and the 11 pinned theorems.
```
$ for n in scost lwHalfPat lwElem LocCostGe LocReg6Inv ScostLL CircIffLoop lwPrim nElem skept sIntCls sElemCls locReg6far fxyPowGraph_locCostGe; do grep -rn "$n" RBM3D --include='*.lean' | wc -l; done   # main worktree
scost:0 lwHalfPat:0 lwElem:0 LocCostGe:0 LocReg6Inv:0 ScostLL:0 CircIffLoop:0 lwPrim:0 nElem:0 skept:0 sIntCls:0 sElemCls:0 locReg6far:0 fxyPowGraph_locCostGe:0
```

## 5. Compiled nonempty instances (file section 7, `RBM3D/Graph/LocalRegular6a.lean:960-1186`; compiled in §2)
| ticket | theorem (line) | data | hypotheses discharged |
|---|---|---|---|
| (1) `scost_perm` | `localReg6a_inst_perm` (966) | `fxyPowGraph 2`, reversed solid list, `⊥` | `(List.reverse_perm _).symm`, `rfl` |
| (2) `scost_relabel` | `localReg6a_inst_relabel` (972) | `fxyPowGraph 2`, `ext = id`, `vm = Sum.map id (swap 0 1)`, every `s` | `surjective_id`, `Surjective.sumMap`, `rfl` |
| (3) Lemma A | `localReg6a_inst_consLoop` (979) | `fxyPowGraph 2`, `e = ⟨true,true,inl 0,inl 0⟩`, `⊥` | `rfl rfl` |
| (4) `scost_le_of_lvl1Split` | `localReg6a_inst_splitCirc` (999), `_splitDrop` (1005) | `Fin 2 ⊕ Fin 1`, one loop at `inr 0`, every `s` | `lvl1Split.circ/.drop … .nil`, `rfl` |
| (5) `scost_partition_ge` | `localReg6a_inst_partition` (1011) | one-term partition of `fxyPowGraph 2`, `m = 1` | `partition_of_normal`, `fxyPowGraph_normal 2`, `DotWF` by `decide` |
| (6) `scost_bot` | `localReg6a_inst_bot2/3` (1025/1031) | `p = 2, 3`: `scost ⊥ = 6, 9` | `fxyPowGraph_normal`, `nElem = 4, 6` by `decide +kernel` |
| (7) `nElem_eq_zero_of_locStd` | `localReg6a_inst_nElemLocStd` (1037) | merged `localReg2_inst_Q` | `localReg2_inst_Q_locStd` |
| (8) initial values | `localReg6a_inst_cost2/3`, `_inv2/3` (1040–1057) | `p = 2` (`4`, `6`), `p = 3` (`6`, `9`) | none (no hypotheses) |
| (9) final step | `localReg6a_instXY_far_ord` (1111), `_all_ord` (1115) | `localReg6a_instXY : LGraph (Fin 2) (Fin 0)`, `ord = 4` (`decide`) | `LocStd` by `decide`, `ext 0 ≠ ext 1` by `decide`, `LocCostGe` by the theorems `_far`/`_all` |
| (10) extra | `localReg6a_instQ_all_ord/far_ord` (1176/1180) | `localReg2_inst_Q` (2 internal vertices), `ord = 2` | `LocStd`, `LocCostGe false 2` proved, `x ≠ y` |
No `N = 0`, empty index, `False` premise or huge witness: `p ∈ {2, 3}`, vertex sets `Fin 2 ⊕ Fin 4/6/2/1/0` as pinned.
Instance (9) has `I = Fin 0` exactly as the ticket pins; instance (10) additionally exercises the final step with internal
vertices. Every endpoint theorem of targets 2–6 is applied at concrete data (§5 table; lines above).

## 6. Paper deltas
Paper `7_8:815-818` `(eq:sizeGammamu)`: `ord ≥ 2p`; its endpoint form is c4's `lw_localregular`. Differences here:
- the route via `scost`/`LocCostGe` and initial values `3p`, `2p` instead of `ord + n_dv + n_lw`, `3p − n_dv/2` (`B:200-278`):
  candidate `T2184a` (prove report (d));
- merges as `Setoid (E ⊕ I)`, internal/kept/elementary definitions: candidate `T2184b`;
- the edge and `GG` cases omitted at `B:272-275`: candidate `T2184c` (to be numbered with c2–c4).
```
$ grep -n "T2184\|scost" docs/paper-deltas.md      # main worktree
(no output: not yet numbered; the three candidates are in the prove report (d), as the ticket expects)
```

## 7. Observations (no statement, instance, build, axiom or delta effect)
- O1. The prove report's finding F1 (the ticket's route for 4(a), "keep changes nothing", is not inductive without a
  prefix) is a route remark only; the pinned statement `ScostSplitPin` is proved unchanged (§3, a4).
- O2. The ticket's optional all-bound sharpness instance (`Setoid.ker`, value `4` at `p = 2`) is not compiled; it is
  marked optional in the ticket. Sharpness of the far bound is compiled (`scost ⊥ = 6, 9`; `4 ≤ ord = 4`).
- O3. Instance (5) is at the one-term (trivial) partition, as pinned.

## Verdict
| target | verdict |
|---|---|
| 1 vocabulary (19 defs) | PASS (verbatim, diff empty) |
| 2 `scost_perm`, `scost_relabel` | PASS |
| 3 `scost_cons_loop_ge` (Lemma A) | PASS |
| 4 `scost_le_of_lvl1Split`, `scost_partition_ge` (Lemma B) | PASS |
| 5 `scost_bot`, `nElem_eq_zero_of_locStd`, `locReg6_of_locCostGe`, `locReg6far_of_locCostGe` | PASS |
| 6 `fxyPowGraph_locCostGe`, `fxyPowGraph_locReg6Inv` | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
