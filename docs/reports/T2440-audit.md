Auditor model: claude-opus-5-5
# T2440 audit (round 2, after the rule-(B) repair under Amend 1): BA-L L3a3 `BALvl1A` (Mon Oct 12 05:40 UTC 2026)

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2440-audit2`, detached at `t/T2440` = `0fac439`. I wrote no source. Scratch files are in the scratchpad under `T2440/`.

## Verdict
- Targets 1-6: **PASS**. The registry pre-check now passes. The ticket passes: **PASS**, and no dispatcher sign-off is needed.

## 0. The repair is exactly Amend 1
```
$ git diff --stat ea4dd16 0fac439          (round-1 head -> repair head)
 RBM3D.lean             | 1 +
 RBM3D/Test/Axioms.lean | 1 +
$ git diff ea4dd16 HEAD -- RBM3D/Graph/BALvl1A.lean | wc -l
       0
$ git diff --numstat main...t/T2440
1	0	RBM3D.lean
676	0	RBM3D/Graph/BALvl1A.lean
1	0	RBM3D/Test/Axioms.lean
$ git diff main...t/T2440 -- RBM3D/Test/Axioms.lean   (hunk @@ -256,6 +256,7 @@ def structuralProps)
    `RBM.Graph.Lvl1Reach.below, -- auxiliary predicate ... `Lvl1Reach` (...) (T2128)
+  `RBM.Graph.BAReach.below, -- auxiliary predicate that Lean generates for the recursive inductive `BAReach` (BA twin of `Lvl1Reach.below`; T2440)
$ python3 -I cmp.py docs/tickets/T2440-amend-1.md   (Amend 1's quoted line vs the changed lines of Test/Axioms.lean)
changed lines: 1
added (indent stripped) == Amend 1 line: True
indent added/neighbour: 2 / 3
$ git diff main...t/T2440 -- RBM3D.lean
@@ -484,6 +484,7 @@ import RBM3D.Graph.BASim2
 import RBM3D.BA.TwistGridRem2
+import RBM3D.Graph.BALvl1A
 
 /-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
 #assert_rbm_axioms
```
- The diff touches only the sole writable files of Amend 1. `BALvl1A2.lean` is not used.
- `Test/Axioms.lean` changes by exactly one added line, in `structuralProps`, directly after the band twin `Lvl1Reach.below`. Its text equals Amend 1's line.
- The import is added after the last `import` line, and `#assert_rbm_axioms` stays last.
- Observation (whitespace only): the new line has 2 spaces of indentation and its neighbours have 3. Lean list syntax does not care, and no name or statement changes.

## 1. Statements: script diff against the check file and the T2395 probe
`BALvl1A.lean` is byte-identical to the round-1 head. I re-ran the diffs anyway.
```
$ awk-extract "def T2440_X" from check (rename -> target, T2440_LocStep -> BALocStep) ; awk-extract "def target" from BALvl1A.lean ; diff
== BALocStep:        2 lines   IDENTICAL
== BAtwistComb:      4 lines   IDENTICAL
== BAframeStepIdentity: 4 lines IDENTICAL
== BAlvl1StepIdentity:  4 lines IDENTICAL
$ git show t/T2395:RBM3D/Probe/T2395Pins.lean | sed -n 277,279p  vs  BALvl1A.lean:69-71
== BAReach vs probe 277-279    IDENTICAL
```
To check elaborated equality, I compiled `Eq.lean`. It is the check file verbatim, plus `import RBM3D.Graph.BALvl1A`, plus these lines:
```
example : ∀ {E : Type} (P : BAPGraph E) outs, T2440_LocStep P outs ↔ BALocStep P outs := fun _ _ => Iff.rfl
example (d : ℕ) : T2440_TwistComb d ↔ BAtwistComb d := Iff.rfl
example (d : ℕ) : T2440_FrameIdentity d ↔ BAframeStepIdentity d := Iff.rfl
example (d : ℕ) : T2440_StepIdentity d ↔ BAlvl1StepIdentity d := Iff.rfl
example (d : ℕ) : T2440_StepIdentity d := baLvl1StepIdentity_holds d
example (d : ℕ) : T2440_FrameIdentity d := baFrameStepIdentity_holds d
example (d : ℕ) : T2440_TwistComb d := baTwistComb_holds d
$ lake env lean Eq.lean                                   -> Eq exit 0 (no error lines)
$ lake env lean docs/tickets/checks/T2440-check.lean      -> check exit 0
```
- **Target 2 (packing).** This is unchanged from round 1.
  - `BALvl1A_pack` (`hℓ : ℓe = ℓ' ∘ P.ext`) gives `BAComb.val (P.outsOf Ts) D ℓe = baSum Ts D ℓ'`.
  - `BALvl1A_pack_zero` gives `= 0 ∧ P.val D ℓe = 0`.
  - `BALvl1A_comb_append` gives the value of `++`.
  - None has a data hypothesis or integrability, which matches the ticket.
- **Targets 4, 5 and macros `BALvl1A_macroA/B`.** Hypotheses exactly `3 ≤ L`, `BASelf`, `0 ≤ t`, `t < 1` (+ constructor premises); no `M a a = m`, `M a b = 0`, smallness of `g` (C1, F5); target 5 keeps `P.g.Normal` verbatim.

## 2. Vacuity, hidden hypotheses, cycles
- No new structure. `BAReach` is the probe's inductive; the registry line covers only its compiler auxiliary `.below` (as `Lvl1Reach.below`, T2128); no mathematical premise is registered.
- Dependencies all merged (`baExpFrameE_holds`, `lanlw_val`, `baTwistIntegral_gen`, `BASymm1_val_twist`, `BASymm1_data_real`, `val_eq_partition`, R1's `BAFrameStep`); no cycle; no external hypothesis.

## 3. Compiled nonempty instances (`BALvl1AInst`, d = 3, L = 4, W = 2, `flowP_data`)
```
$ sed -n 576,672p RBM3D/Graph/BALvl1A.lean | grep -nE "baFrameStepIdentity_holds|baLvl1StepIdentity_holds|baTwistComb_holds|BALvl1A_pack|BALvl1A_macro|BAReach"
20:  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ _ hFA ℓ0
21:  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) ... _ _ hFB ℓ0
22:  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) ... _ _ hFC ℓ0
23:  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) ... _ _ hFW ℓ1
24:  · exact baFrameStepIdentity_holds 3 4 2 (by norm_num) ... _ _ hFE ℓ0
32:  ⟨BALvl1A_macroA (by norm_num) ... (baPG baPB) pB (List.mem_cons_self ..) rfl rfl ℓ0,
33:    BALvl1A_macroB (by norm_num) ... (baPG baPC) pC qC (List.mem_cons_self ..) 0 rfl ⟨rfl, rfl, rfl, rfl⟩ ℓ0⟩
39:  baTwistComb_holds 3 4 2 g0P EP t0P m0P true true [baPG baPB, baPG baPC] ℓ0
45:  ⟨BALvl1A_pack (baPG baPE) _ D (ℓ' := ℓ0) rfl, BALvl1A_pack (baPG baPW) _ D (ℓ' := ℓ1) rfl⟩
63:  ⟨(BALvl1A_pack_zero P2 (baPW.lw2 pW) D ℓ0_not_factor).1, (...).2, by decide +kernel⟩
85:  ⟨baLvl1StepIdentity_holds 3 4 2 (by norm_num) ... _ _ locStepB normalB ℓ0,
86:    baLvl1StepIdentity_holds 3 4 2 (by norm_num) ... _ _ locStepC normalC ℓ0,
95:  exact ⟨R, BAReach.step _ _ R _ (BAReach.refl _) (by decide +kernel) (by decide +kernel) locStepB hR, hR⟩
```
- Target 4 at all five R1 data (`gg` P_A, `within` P_B, `ggSplit` P_C j = 0, `weight` P_W, `edge` P_E); target 5 at the `(true, true)` twists of P_B, P_C; target 3 at `[P_B, P_C]`; target 2 at P_E, P_W and the zero case `P2` (`ℓ0_not_factor` proved); `BAReach` in one genuine `step`.
- Every deterministic hypothesis is discharged by `norm_num`, `flowP_data`, `decide`/`rfl` or `decide +kernel`. Output lists are nonempty (`decide +kernel`). Nothing is degenerate.

## 4. Build, axioms, hygiene, registry pre-check
```
$ lake build RBM3D.Graph.BALvl1A RBM3D.Test.Axioms
✔ [3823/3824] Built RBM3D.Test.Axioms (10s)
✔ [3824/3824] Built RBM3D.Graph.BALvl1A (28s)
Build completed successfully (3824 jobs).        exit 0
$ lake build   (whole library, branch head)
info: RBM3D.lean:490:0: axiom audit: 12796 theorems, 4028 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4258 jobs).        exit 0
$ printf 'import RBM3D\n#assert_rbm_axioms\n' > Full.lean ; lake env lean Full.lean   (ticket item 7 pre-check)
axiom audit: 12796 theorems, 4028 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...   (lines joined)
premises found by scanning: 117 (borrowed 1, owed 52, structural 45, refuted 6, superseded 13).
Full exit 0
$ lake env lean Eq.lean   (#print axioms part)
'RBM.Graph.baTwistComb_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baFrameStepIdentity_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLvl1StepIdentity_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1A_pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1A_pack_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1A_comb_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1A_macroA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1A_macroB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1A_reach_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1AInst.locStepB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1AInst.locStepC' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1AInst.hFB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1AInst.hFC' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1AInst.ℓ0_not_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|^axiom|native_decide" RBM3D/Graph/BALvl1A.lean RBM3D/Test/Axioms.lean
RBM3D/Test/Axioms.lean:18:Any `sorry` (`sorryAx`) therefore breaks the build, and so does any new `axiom` that has
```
- The only grep hit is a pre-existing docstring (`Test/Axioms.lean:18`), outside the diff. No frozen signature is touched (0 deletions). `BALvl1A.lean`: 676 lines (stop line 2,000).

## 5. Paper deltas
- `docs/paper-deltas.md` has no T2440 entry yet. The prove report (d) item 2 proposes the following, unchanged from round 1:
  - `T2440a`: `P.g.Normal` is kept in target 5 although it is unused.
  - `T2440b`: the R1 steps `within` and `ggSplit` have no paper counterpart.
- The repair adds no statement difference. The registry line is a compiler auxiliary, not a paper statement.
- Round-1 observation, still open: the twist step is the Lean form of the paper's "by symmetry" reductions (`B_graphical_lemmas.tex:353-409`). The dispatcher may fold it into `T2440b`. It does not affect coverage of any target.

## 6. Observations (not RETURN)
- Main has moved since the merge base `fc541aa`: `git diff --stat fc541aa main -- RBM3D.lean` shows 4 insertions, and `Test/Axioms.lean` is unchanged on main. So `RBM3D.lean` needs the union of import lines at merge (H23 (b)). My full build ran on the branch head, so the hub's merge build is still needed.
- The indentation of the new registry line differs from its neighbours (§0). This is cosmetic.
- The instance-section public names in `RBM.Graph.BALvl1AInst` do not carry the `BALvl1A_` prefix literally. They follow the `BASymm2Inst` precedent (round 1).

## Per target
| Target | Statement | Instance | Build/axioms | Verdict |
|---|---|---|---|---|
| 1 `BALocStep`, `BAReach` | = check / probe | locStepB/C, one-step reach | ok | PASS |
| 2 packing | = ticket math | P_E, P_W, P2 (zero case) | ok | PASS |
| 3 `BAtwistComb` / `baTwistComb_holds` | = check | [P_B, P_C] | ok | PASS |
| 4 `BAframeStepIdentity` / `_holds` | = check | five R1 data | ok | PASS |
| 5 `BAlvl1StepIdentity` / `_holds` | = check / probe | twists of P_B, P_C | ok | PASS |
| 6 instances | compiled, nondegenerate | — | ok | PASS |
| Amend 1 registry line / pre-check | one line = Amend 1 | — | `import RBM3D` + `#assert_rbm_axioms` exit 0 | PASS |
