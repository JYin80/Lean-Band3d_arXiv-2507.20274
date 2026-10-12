Auditor model: claude-opus-5-5
# T2447 audit (round 1): BA-L L3b4'' `Graph/BAShapeO2`, `Graph/BAShapeO2B`
Audit time: Mon Oct 12 11:26:58 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2447-audit1`, detached at `t/T2447` = 272d1f0. Scratch: scratchpad `T2447/`.

## 1. Diff, size, hygiene
```
$ git diff main...HEAD --name-only
RBM3D.lean
RBM3D/Graph/BAShapeO2.lean
RBM3D/Graph/BAShapeO2B.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean RBM3D/Graph/BAStepS.lean RBM3D/Graph/BAScost.lean RBM3D/Graph/BAScost2.lean | wc -l
       0
$ git diff main...t/T2447 -- RBM3D.lean   (hunk)
 import RBM3D.Graph.BALvl1C
+import RBM3D.Graph.BAShapeO2
+import RBM3D.Graph.BAShapeO2B
 
 /-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
 #assert_rbm_axioms
$ grep -nE "sorry|admit|native_decide|^\s*axiom|open private|^inductive|^structure|^class" RBM3D/Graph/BAShapeO2.lean RBM3D/Graph/BAShapeO2B.lean; echo "forbidden hits: $?"
forbidden hits: 1
$ wc -l RBM3D/Graph/BAShapeO2.lean RBM3D/Graph/BAShapeO2B.lean      (stop line 2000 per file)
    1094 RBM3D/Graph/BAShapeO2.lean
     447 RBM3D/Graph/BAShapeO2B.lean
$ for n in baShapeLL_e2_tn baShapeLL_macroA_tn baShapeLL_macroB_tn baLocReg6_holds BAShapeO2_ BAShapeO2B_; do printf "%s: " $n; git grep -l "$n" main -- RBM3D | wc -l; done
baShapeLL_e2_tn:        0
baShapeLL_macroA_tn:        0
baShapeLL_macroB_tn:        0
baLocReg6_holds:        0
BAShapeO2_:        0
BAShapeO2B_:        0
```
Sole writable files only; frozen `BAStepS`/`BAScost*`/`Test/Axioms.lean` untouched; no forbidden token; no new `inductive`/`structure`.

## 2. Builds and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BAShapeO2 RBM3D.Graph.BAShapeO2B 2>&1 | grep -E "error|BAShapeO2|Build completed"
Build completed successfully (3827 jobs).
$ lake build 2>&1 | grep -E "error:|non-vacuity|Build completed|premise" | tail -3     (whole library, #assert_rbm_axioms + premise scan)
premises found by scanning: 117 (borrowed 1, owed 52, structural 45, refuted 6, superseded 13).
non-vacuity certificates: 0 of 90 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4273 jobs).
$ # ax.lean: import RBM3D.Graph.BAShapeO2B; #print axioms of every `theorem`/`def` (non-private) of both files
$ grep -c "#print" ax.lean; lake env lean ax.lean > ax.out; echo "exit $?"; grep -c "propext, Classical.choice, Quot.sound\]" ax.out; grep -v "propext, Classical.choice, Quot.sound\]" ax.out
59
exit 0
56
'RBM.Graph.BAShapeO2B_lwSplit_last' depends on axioms: [propext, Quot.sound]
'RBM.Graph.BAShapeO2_map_id' does not depend on any axioms
'RBM.Graph.BAShapeO2_perm_rot' depends on axioms: [propext]
```
All within {propext, Classical.choice, Quot.sound}.

## 3. Statements against the pins (scratch copy of the check file, not merged)
`audit-check.lean` = the check file's header and Part 2 verbatim (import `BAStepS` replaced by `BAShapeO2B`), plus:
```
example : T2447_E2TN := baShapeLL_e2_tn
example : T2447_MacroATN := baShapeLL_macroA_tn
example : T2447_MacroBTN := baShapeLL_macroB_tn
example : T2447_LocReg6Holds := baLocReg6_holds
example : T2447_Binder := by rintro sh (rfl|rfl|rfl); exacts [baShapeLL_e2_tn, baShapeLL_macroA_tn, baShapeLL_macroB_tn]
#print axioms baShapeLL_e2_tn   (and the other three)
```
```
$ lake env lean audit-check.lean > ac.out 2>&1; echo "exit $?"; grep -c error ac.out
exit 0
0
'RBM.Graph.baShapeLL_e2_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapeLL_macroA_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapeLL_macroB_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLocReg6_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Source text (BAShapeO2B.lean):
```
221:theorem baShapeLL_e2_tn : BAShapeLL BAShape.e2 BAFrameStepTN := by
269:theorem baShapeLL_macroA_tn : BAShapeLL BAShape.macroA BAFrameStepTN := by
303:theorem baShapeLL_macroB_tn : BAShapeLL BAShape.macroB BAFrameStepTN := by
350:theorem baLocReg6_holds : ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition →
351:    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q →
352:      locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧
353:        (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder)) := by
```
Targets 1–3 are the pinned closed `Prop`s; target 4 is `T2447_LocReg6Holds` (= the conclusion of `BALocReg6`, `BAStepS:98-104`, with the binder removed; same quantifier order p, P0, hP0, K, Q, hQ; same `2p`/`3p` thresholds). No binder restated as a new `Prop`; no new public `def` other than the vertex map `BAShapeO2_psi2`.

## 4. Hidden hypotheses, vacuity, cycles
- Targets 1–4 have **no hypotheses** of their own; nothing can hide in a structure field (none is defined).
- Dependencies are merged signatures: `baShapeLL_e2`, `baShapeLL_of_terms`, `baShapeLL_macroB` (`BAScost2:93,58,114`, T2426), `BAScostLL_macroA/_macroB`, `BAScostLL.trans` (`BAScost`), `baLocReg6_reach : BALocReg6` (`BAStepS:413`, T2443, no extra hypothesis). No dependency on any `T2447` consumer; no cycle.
- Stage 2 is route (β) (ticket open choice (1), permitted): `BAShapeO2B_macroA/_macroB` = `BAScostLL_macroA/_macroB ... |>.trans` of the file-1 lemmas at `Γ := tr`; no `baStep_of_simC'`, so `macroA`/`macroB` are not assumed (ticket target 6 constraint). Target 3 uses disjunct 2 of `baShapeLL_macroB` for both stages (BAShapeO2B.lean:306).
- Builder-lemma hypotheses (file 1, e.g. `BAShapeO2_gg2` / `_gg4`: `hN`, `hp`, `hq`, σ/circ, `hxy`, `hwf1`, `hwf2`, `hint`; `BAShapeO2_lw2`/`_lw4`: `hN`, `hp`, loop shape; `BAShapeO2_within`: `hN`, `hp`, σ/circ, `hsame`) are all supplied from the `BAFrameStepT` constructor fields and `P.g.Normal` inside targets 1–3 (BAShapeO2B.lean:225-265, 326-342). Nothing from (1)–(5)/`BAReach` invariants (O2R-C2 (d)).
- External hypotheses: none (no limit check needed).

## 5. Compiled nonempty instances (in the files; built in §2)
```
BAShapeO2B.lean:367  (i)  within at baPB: e2 and macroA output exist (tag_exists, decide +kernel); baShapeLL_e2_tn / _macroA_tn applied with ⟨by decide, hTB⟩
BAShapeO2B.lean:375  (iii) BAScostInst.gc = baPC ∧ pc = pC ∧ qc = qC := ⟨rfl, rfl, rfl⟩   (so (ii) serves for macro (b))
BAShapeO2B.lean:379  (ii) ggSplit at baPC, j = 0: e2 and macroB output; targets 1, 3 with ⟨by decide, hTC⟩
BAShapeO2B.lean:388  (ii) stage-1 (d2–d4) and stage-2 (tr.gg2) macroB outputs separately; target 3 at both
BAShapeO2B.lean:416  (iv) gg at baPA (hTA): target 1 at an e2 output
BAShapeO2B.lean:422  (v) p = 2: ∃ P0 ∈ partition (nonempty by decide), locReg6InvA 2 P0 ∧ ∀ K Q, BAReach K P0 Q → locReg6InvA 2 Q  via baLocReg6_holds, no hX
BAShapeO2B.lean:433,437  stage 2 BAShapeO2B_macroA at baPB, BAShapeO2B_macroB at baPC, every hypothesis by decide/rfl
BAShapeO2.lean:1059-1090  term lemmas at baPW, baPB, baPE, baPA, baPC
```
Data: R1 witnesses (E = Fin 2, I = Fin 3), concrete steps `hTA`/`hTB`/`hTC`, normality by `decide`, outputs located by `decide +kernel`; the cost premise `locCostGeA far (-4) P` is discharged by the merged `BAScost_locCostGeA_crude` (k = 2(waved − |I'|)), and `far` is universally quantified. No `N = 0`, empty index, collapsed window or `False` premise. Every endpoint (targets 1–4) is applied.

## 6. Paper deltas
- Prove report (d)1 proposes the withdrawal line for `T2443d` (as the ticket requires); no new Lean/paper difference (targets are the pins; `T2447a` unused). Coverage complete.

## 7. Observations (no verdict effect)
- O1. The instances use the crude cost level `k = -4` from `BAScost_locCostGeA_crude`; the conclusion `locCostGeA far (-4) Q` is thus a weak test of `BAShapeLL`, but every hypothesis is discharged at concrete nondegenerate data, as in the merged `BAScost:1504` instance.
- O2. `main` has moved past the branch base (merge-base 1fec089, main 695cfc7); `RBM3D.lean` is a union of import lines at merge (ticket "RBM3D.lean: union"). The full build above is on the branch; the hub's merge build is the check after union.
- O3. `T2443d` is not (yet) present in `docs/paper-deltas.md` (`grep -n T2443 docs/paper-deltas.md` empty); the dispatcher applies the T2443 entry and the T2447 withdrawal together.
- O4. Prove report cites scratch-script output (`stmtdiff.py`, `table_final.py`) whose scripts are not in the repo; the audit re-derived the statement check by compiling (§3).

## 8. Verdict
| target | verdict |
|---|---|
| 1 `baShapeLL_e2_tn` | PASS |
| 2 `baShapeLL_macroA_tn` | PASS |
| 3 `baShapeLL_macroB_tn` | PASS |
| 4 `baLocReg6_holds` | PASS |
| 5 stage-1 builder lemmas (17 + lists) | PASS |
| 6 stage 2 (route β) | PASS |
| 7 instances (i)–(v) | PASS |

**T2447: PASS.** No dispatcher sign-off needed.
