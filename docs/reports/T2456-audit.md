Auditor model: claude-opus-5-5
# T2456 audit (round 2): BA-L L3b1 `Graph/BALocReg1`, `Graph/BALocReg1B`, under split Σ (CONTROL H250 (2))
Date: Mon Oct 12 17:10:16 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2456-audit2`, detached at `t/T2456` = `6926e67`. Scratch: scratchpad `T2456/`.
Scope (H250 (2), binding): targets 3 (c)-(e) (`BAShapePath` for `e2`, `macroA`, `macroB`) belong to L3b2 and are not a defect here; target 7 is `T2456_PathBinder → T2456_LocReg15`
(binder verbatim, no new `Prop`). Round 1 RETURN items: (1) target 3 (b) at R1's `ggSplit` `hTC`; (2) the `LocStd` branch of target 7 at a reached graph; (3) report.

## 1. Diff, size, hygiene
```
$ git diff --stat main...HEAD          # merge-base 6bdc5a3
 RBM3D/Graph/BALocReg1.lean  | 884 ++++
 RBM3D/Graph/BALocReg1B.lean | 926 ++++
 2 files changed, 1810 insertions(+)
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/BALocReg1.lean RBM3D/Graph/BALocReg1B.lean
RBM3D/Graph/BALocReg1.lean:0
RBM3D/Graph/BALocReg1B.lean:0
```
Only the sole writable files (both new; `RBM3D.lean` untouched, the hub adds the imports); no merged file edited, no frozen signature touched; both files under the 2,000 stop line.
No `inductive`, no `open private`; `Test/Axioms.lean` unchanged.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BALocReg1 RBM3D.Graph.BALocReg1B
✔ [3842/3843] Built RBM3D.Graph.BALocReg1 (4.8s)
✔ [3843/3843] Built RBM3D.Graph.BALocReg1B (15s)
Build completed successfully (3843 jobs).
$ grep -E "^(error|warning)" build.log | sed -E 's/:[0-9]+:[0-9]+:.*//' | sort | uniq -c   # no line names BALocReg1*; errors 0
$ lake build RBM3D | tail -1
Build completed successfully (4281 jobs).
$ lake env lean AssertT2456a.lean      # import RBM3D + both modules + #assert_rbm_axioms; exit 0, error lines 0, lines naming a new declaration 0
axiom audit: 13373 theorems, 4195 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
$ lake env lean AuditT2456.lean        # scratch copy of the check file + both modules (section 3); exit 0, errors 0
'RBM.Graph.baEquivPath_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baPathTwist_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapePath_s1_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapePath_e1_tn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShapePath_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baSimP'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baPathStep_of_simP'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baPathStep_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baPathInit_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baStart_nM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baShadow_locReg345' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLocReg15_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_fxyPow_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALocReg1B_reach_locStd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALocReg1Inst.pathInv2_C' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pins (`docs/tickets/checks/T2456-check.lean`)
Appended to the scratch copy of the check file (compiled, exit 0, 0 errors):
```lean
example : T2456_S1Path := baShapePath_s1_tn
example : T2456_E1Path := baShapePath_e1_tn
example : T2456_SimP := fun m => baSimP'_holds m
example : T2456_PathBinder → T2456_PathStep := baPathStep_holds
example : T2456_PathInit := baPathInit_holds
example : T2456_StartNM := baStart_nM_le
example : T2456_PathBinder → T2456_LocReg15 := baLocReg15_holds
example : T2456_ValueId := fun d L W _ _ g0 Em t m p hp ℓe => ba_fxyPow_integral_eq d L W g0 Em t m p hp ℓe
example : BALocReg15 = T2456_LocReg15 := rfl
example : (∀ p, BAPathInit p) = T2456_PathInit := rfl
example : (∀ m, BASimP' m BALocStepT) = T2456_SimP := rfl
example : (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) = T2456_PathBinder := rfl
example : BAShapePath BAShape.e1 BAFrameStepTN = T2456_E1Path := rfl
example : BAPathStep (untag BALocStepT) = T2456_PathStep := rfl
```
Text diff (`python3 -I pindiff.py`, whitespace-normalised bodies):
```
LocReg15  : BALocReg15 body == T2456_LocReg15 body: True
PathInit  : "∀ p : ℕ, "+BAPathInit body == pin: True
StartNM   : baStart_nM_le "(p : ℕ) : <stmt>" vs pin "∀ p : ℕ, <stmt>": True
SimP      : def: ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), (∀ k : ℕ, P.img.PathInv2 k → P'.PathInv2 k) ∧ ∀ Q : BAPGraph (Fin 2), (BAShape.band, Q) ∈ LT → ∃ L' ..., LocStep m P' L' ∧ ∃ R ∈ L', ∀ k, R.PathInv2 k → Q.img.PathInv2 k
            pin: ∀ (m : ℂ) (P ...) (LT ...), BALocStepT P LT → (same text)
hX of baLocReg15_holds: (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) : BALocReg15
PathBinder pin: ∀ sh : BAShape, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → ∀ P LT, BAFrameStepTN P LT → ∀ Q, (sh, Q) ∈ LT → ∀ k, P.img.PathInv2 k → Q.img.PathInv2 k
```
Quantifier order of target 7 as pinned (`p`, `P0 ∈ partition`, `K`, `Q`, `BAReach K P0 Q`), all `p : ℕ`, conclusions (path invariant, `n_M ≤ p`, `LocReg2`,
and under `Q.g.LocStd`: `LocReg1`, `LocReg345` on image and shadow) identical. Target 9 keeps `Even p`, `NeZero L`, `NeZero W` of the pin; no extra hypothesis.
Non-binding tool shapes (check file): `baEquivPath_holds` is one direction (check `↔`); `baShadow_locReg345` drops `Q.g.Normal` (weaker hypothesis, stronger result);
`baPathTwist_holds` is `↔` as in the check. Both differences are disclosed (`T2456e`).

## 4. Hidden hypotheses, vacuity, cycles
- New `Prop` defs: `BAShapePath`, `BASimP'`, `BAPathStep`, `BAPathInit`, `BALocReg15` (plus stem helpers `BALocReg1_PathAt`, `BALocReg1B_Good`); no `structure`/`class`.
  Each is concluded by a theorem in the files (`baShapePath_*`, `baSimP'_holds`, `baPathStep_holds`, `baPathInit_holds`, `baLocReg15_holds`; `BALocReg1B_Good.comp/.ext`).
- The only open hypothesis of any target is `hX` = `T2456_PathBinder` (rfl, section 3), as H250 (2) signs off; it is L3b2's pin, not used circularly
  (no file here imports L3b2; `baLocReg15_holds` uses `baPathStep_holds`, `baPathInit_holds`, `baStart_nM_le`, `baShadow_locReg345`, merged `baReach_bReach`, `baLvl1StepGood_holds`).
- `baShapePath_s1_tn` is vacuous by design (no constructor tags `s1`; ticket target 3 (a)). Not a hidden vacuity: the instance shows `s1 ∉` the outputs.
- C1, combinatorial: no external analytic hypothesis, so no limit check is due.

## 5. Compiled nonempty instances (target 10)
```
$ grep -n '^example' RBM3D/Graph/BALocReg1.lean RBM3D/Graph/BALocReg1B.lean | cut -c1-150
BALocReg1.lean:747:  twist + baEquivPath at the edge witness baPEr (PathInv2 1)                  [target 1]
BALocReg1.lean:752:  e1 output of hStepEr (BAFrameStepT.edge, hypotheses by decide) + s1 ∉ tags  [3 (a), 3 (b)]
BALocReg1.lean:765:  baSimP'_holds m at stepErT (BALocStepT), band output; baPathStep_holds hX   [2, 4]
BALocReg1.lean:874:  e1 output of R1's ggSplit hTC at P_C, PathInv2 2 (pathInv2_C)              [3 (b), round-1 item 1]
BALocReg1B.lean:330: start term of p = 2 with PathInv2 2 and n_M ≤ 2                            [5, 6]
BALocReg1B.lean:335: contract at a start term and every BAReach-reached Q (hX)                   [7]
BALocReg1B.lean:404: contract at R reached by one weight step (hX)                               [7]
BALocReg1B.lean:892: LocStd branch at Q reached by two BALocSteps, Q.g.LocStd, n_M = 1 (hX)     [7 LocStd, 8; round-1 item 2]
BALocReg1B.lean:905: hand-built LocStd lift of localReg2_inst_Q: LocReg345 image and shadow      [8]
BALocReg1B.lean:918: value identity at p = 2, d = 3, L = 4, W = 2, g0 = Em = t = 1, m = 1        [9]
```
(the bracketed descriptions are the auditor's reading of each example's statement, checked against the source.)
- Round-1 item 1, `:874`: `baShapePath_e1_tn _ _ ⟨by decide, hTC⟩ Q hQ 2 pathInv2_C`; the `e1` tag by `BASimInst.tag_exists … (by decide +kernel)`; `pathInv2_C`
  is proved (hand-built band twin `LCr`, `LCr_pathFam`, moved by `BALocReg1_pathAt_map`), `#print axioms` standard. Nondegenerate (R1's own witness, k = 2). **Met.**
- Round-1 item 2, `:892`: from `BALocReg1B_reach_locStd` (P0 ∈ partition of `fxyPowGraph 2`, `BALocStep P0 L1`, `Q1 ∈ L1`, `BALocStep Q1 L2`, `Q ∈ L2`,
  `¬ P0.g.LocStd`, `¬ Q1.g.LocStd`, `BAReach K P0 Q`, `Q.g.LocStd`, `Q.g.nM = 1`, all proved, kernel data by `decide`), then `baLocReg15_holds hX 2 P0 hP0 K Q hreach`
  concludes `LocReg1 Q.img ∧ LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2`. `hX` is the only hypothesis. **Met.**
- Under Σ, items (i) (`within` on `P_B`: `e2`, `macroA`) and (iii) (`gg` on `P_A`: `e2`) instantiate L3b2's shapes and move with them. Item (iv): R1's `P_E` has no
  `PathInv2 k` for any k (section (a) row 7, finding (1)); the replacement `edge` witness `baPEr` (normal, `PathInv2 1`, tags `band`/`e1`/`e2`) is used. Not degenerate.
- Every deterministic hypothesis is discharged (`decide`, `decide +kernel`, proved lemmas); no `N = 0`, empty index, `False` premise, or large witness.

## 6. Paper deltas
Candidates in the prove report (d): `T2456a` (3)-(5) read on the image and on the shadow; `T2456b` (eq:MolVW) counts atoms (= `T2397c`); `T2456c` walks, not paths;
`T2456d` split Σ binder on targets 4, 7; `T2456e` tool shapes (`→` for `baEquivPath_holds`, no `Normal` in `baShadow_locReg345`). Every Lean/paper and Lean/check difference
found in sections 3-5 is covered. `grep -n T2456 docs/paper-deltas.md` on main: none yet (the dispatcher numbers them).

## 7. Verdict per target
| target | verdict |
|---|---|
| 1 `baEquivPath_holds`, `baPathTwist_holds` | PASS |
| 2 `BASimP'`, `baSimP'_holds` | PASS (= `T2456_SimP`, rfl) |
| 3 (a) `baShapePath_s1_tn`, (b) `baShapePath_e1_tn`, `baShapePath_twist` | PASS |
| 3 (c)-(e) | not here (H250 (2): L3b2) |
| 4 `BAPathStep`, `baPathStep_of_simP'`, `baPathStep_holds` | PASS (`T2456_PathBinder → T2456_PathStep`) |
| 5 `BAPathInit`, `baPathInit_holds` | PASS |
| 6 `baStart_nM_le` | PASS |
| 7 `BALocReg15`, `baLocReg15_holds` | PASS in the signed Σ form `T2456_PathBinder → T2456_LocReg15` |
| 8 `baShadow_locReg345` | PASS |
| 9 `ba_fxyPow_integral_eq` | PASS |
| 10 instances | PASS (round-1 items 1, 2 met; (i), (iii) move with Σ; (iv) replacement witness) |

**Overall: PASS.** No dispatcher sign-off needed beyond H250 (2), which is already given.

### Observations (no statement, instance, build, axiom or delta effect)
- O1: the prove report is 299 lines: within CLAUDE.md §6 (300), over the ticket's 250.
- O2: `baShapePath_twist` and `baPathStep_of_simP'` are exercised only through `baPathStep_holds` (example `:765`); `baEquivPath_holds` is applied at the reflexive `BAEquivC`.
- O3: unprivate helpers are stem-prefixed or in namespace `RBM.Graph.BALocReg1Inst` (`LEr`, `baPEr`, `pathInv2_C`, …); `BALocReg1_locReg345_of_equiv`, `BALocReg1_molMap*`
  sit in `BALocReg1B.lean` with the sibling stem. Clash grep by the prover: 0 hits; L3b2 reuses `BALocReg1Inst.baPEr`.
- O4: the target 7 instance for item (vi) follows two weight steps, not section (a)'s weight → gg path; the ticket asks only for "reached by at least one step".
- Hub at merge: add `import RBM3D.Graph.BALocReg1`, `import RBM3D.Graph.BALocReg1B` after the last `import` of `RBM3D.lean`.
