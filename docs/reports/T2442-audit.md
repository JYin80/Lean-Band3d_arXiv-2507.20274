Auditor model: claude-opus-5-5
# T2442 audit (round 1) — Mon Oct 12 08:49:49 UTC 2026
Branch `t/T2442` at 0b280c3 (base 4a0b23b). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2442-audit1` (detached). Scratch: `scratchpad/T2442/` (`audit.lean`, `scan.lean`).

## 1. Diff, size, hygiene
```
$ git diff --name-status main...t/T2442
A	RBM3D/Graph/BALvl1B.lean
A	RBM3D/Graph/BALvl1B2.lean
$ git diff main...t/T2442 -- RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ wc -l RBM3D/Graph/BALvl1B.lean RBM3D/Graph/BALvl1B2.lean      # stop line 2,000 per file
     491 RBM3D/Graph/BALvl1B.lean
     318 RBM3D/Graph/BALvl1B2.lean
$ git show t/T2442:<f> | grep -cE '\bsorry\b|\badmit\b|native_decide|^\s*axiom |open private|^\s*inductive '
RBM3D/Graph/BALvl1B.lean: 0
RBM3D/Graph/BALvl1B2.lean: 0
$ git grep -nE "^(theorem|def|lemma|namespace|abbrev|structure) <name>\b" main -- RBM3D | wc -l   # per new public name
BALvl1Good 0, BALvl1GoodLit 0, BAlvl1StepGood 0, BAstepMono 0, ba_good_of_lit 0, ba_lvl1StepGood_of_sim' 0,
baStepMono_holds 0, baLvl1StepGood_holds 0, BALvl1BInst 0
```
Only sole writable files touched (both new); `RBM3D.lean` import lines left for the hub; no frozen signature touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BALvl1B RBM3D.Graph.BALvl1B2
✔ [3825/3825] Built RBM3D.Graph.BALvl1B2 (5.7s)
Build completed successfully (3825 jobs).
exit=0
$ grep -E "^(warning|error).*BALvl1B" build.log      # warnings in the log are all replayed upstream files (LWLvl1, LWSymm, IBPPoly, ...)
(no output)
$ lake env lean audit.lean     # check-file Part 2 + import RBM3D.Graph.BALvl1B2 + rfl checks below + #print axioms
exit=0   (0 lines with "error")
'RBM.Graph.ba_good_of_lit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_lvl1StepGood_of_sim'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1B_lit_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1B_part_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baStepMono_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLvl1StepGood_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1B_within' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1B_ggSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1B_ord_d4' depends on axioms: [propext, Classical.choice, Quot.sound]
$ printf 'import RBM3D\nimport RBM3D.Graph.BALvl1B\nimport RBM3D.Graph.BALvl1B2\n#assert_rbm_axioms\n' > scan.lean; lake env lean scan.lean
axiom audit: 12956 theorems, 4067 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
premises found by scanning: 117 (borrowed 1, owed 52, structural 45, refuted 6, superseded 13).
exit=0
```
No name of this ticket appears in the scan's premise lists (`BALvl1GoodLit` is the conclusion head of the public `BALvl1B_lit_of_band`; `BAsim'`, `BAimg`, `BAtwistInv`, `BAstepMono` are heads of `baSim'_holds`, `BAimg_holds`, `baTwistInv_holds`, `baStepMono_holds`).

## 3. Statements against the pins (Lean-checked, not only text)
Appended to the check file's Part 2 (`docs/tickets/checks/T2442-check.lean:155-189`), compiled in `audit.lean` above (exit 0):
```
example : @BALvl1Good = @T2442_Good := rfl
example : @BALvl1GoodLit = @T2442_GoodLit := rfl
example : BAlvl1StepGood = T2442_StepGood := rfl
example : BAstepMono = T2442_StepMono := rfl
example : T2442_Reduction := ba_lvl1StepGood_of_sim'
example : T2442_StepMono := baStepMono_holds
example : T2442_StepGood := baLvl1StepGood_holds
```
Textual statements (from the files):
```
BALvl1B.lean:133: theorem ba_lvl1StepGood_of_sim' : ∀ m : ℂ, BAimg → BAsim' m → BAstepMono → BAtwistInv → BAlvl1StepGood
BALvl1B2.lean:252: theorem baStepMono_holds : BAstepMono
BALvl1B2.lean:264: theorem baLvl1StepGood_holds : BAlvl1StepGood :=
  ba_lvl1StepGood_of_sim' 0 BAimg_holds (baSim'_holds 0) baStepMono_holds baTwistInv_holds
BALvl1B.lean:79: theorem ba_good_of_lit {Γ : BAGraph E₁ I₁} {Q : BAGraph E₂ I₂} (h : BALvl1GoodLit Γ Q) (hx : Q.nExt ≤ Γ.nExt) : BALvl1Good Γ Q
BALvl1B.lean:250: theorem BALvl1B_part_struct (P : BAPGraph E0) {I0 : Type} [Fintype I0] [DecidableEq I0] (G : BAGraph P.E' I0) {k : ℕ}
    {T : BAGraph P.E' (I0 ⊕ Fin k)} (hExt : BASim_Ext G k T) (hG : G.Normal) :
    ∀ Δ ∈ T.splitG, Δ.Normal ∧ (P.BASim_outOf Δ).baInv = BASim_inv Δ ∧ Δ.nW = (BAWeightOp_circ T).nW ∧ Δ.nA ≤ (BAWeightOp_circ T).nA ∧
      Δ.nM ≤ (BAWeightOp_circ T).nM ∧ Δ.nExt ≤ (BAWeightOp_circ T).nExt ∧ Δ.nExt ≤ G.nExt
```
- Target 1: four defs equal the pins definitionally (`rfl`); two `Decidable` instances at B:75-76; `ba_good_of_lit` hypotheses = `BALvl1GoodLit` + `nExt ≤` (probe 289-297). PASS.
- Target 2: closes `T2442_Reduction` exactly; hypothesis `BAsim' m` (not `BAsim`). Proof uses the first disjunct of `BAsim'` (`T`, `L'`, `Q0`), `BAimg` normality of `T.img`, `lvl1_step_good`, `BALvl1B_lit_of_band` on the `baInv` equalities, `ba_good_of_lit`, twist-back by `ba_twist_counters` (B:133-148). PASS.
- Target 3: `BALvl1B_part_struct` has the ticket's hypotheses (`BASim_Ext Γ k T`, `Γ` normal, `Δ ∈ T.splitG`) and every listed conclusion (normal; packed invariants; `n_W` equal; `n_A`, `n_M`, `nExt` ≤ at `T°`), plus `Δ.nExt ≤ G.nExt` (stronger, not weaker). PASS.
- Target 4: `baStepMono_holds : BAstepMono` (= pin), `cases` on all five `BAFrameStep` constructors (`weight`, `within`, `edge`, `gg`, `ggSplit`; B2:254-260), macro claims `BALvl1B_within`, `BALvl1B_ggSplit`, new weak order of `d4` (`BALvl1B_ord_d4`, B2:91). PASS.
- Target 5: `baLvl1StepGood_holds : BAlvl1StepGood` (= pin), unconditional: all four hypotheses of target 2 discharged by merged theorems (`BAimg_holds` BAAtomic:706, `baSim'_holds` BASim3:1830, `baTwistInv_holds` BASymm1:175) and target 4. PASS.
- Target 7: no data hypothesis; no `inductive`; `Test/Axioms.lean` unchanged; `BALvl1B_lit_of_band` public. PASS.

## 4. Hidden hypotheses, vacuity, cycles
- No structure carries a hypothesis; the only new `def` Props besides the pins are `BALvl1B_Mono` (B:350, the five conclusions of `BAstepMono`, used only as a conclusion) and `BALvl1B_TermOk` (B:405, discharged by `BALvl1B_dterms_ok` B2:160).
- No cycle: `ba_lvl1StepGood_of_sim'` takes `BAstepMono` as a hypothesis; `baStepMono_holds` (B2) does not use the reduction; target 5 composes them. Dependencies (`BAsim'`/`baSim'_holds` T2423, `BAimg_holds` T2417, `baTwistInv_holds` T2425, `BALocStep`/instances T2440, `lvl1_step_good` LWLvl1) are on `main`.
- External hypothesis: none (C1).

## 5. Compiled nonempty instances (all in the two files, compiled by the module build)
| target | instance | data / hypotheses discharged |
|---|---|---|
| 1 `ba_good_of_lit`, defs | B:459 | `baPW`, `tW` = head of `lw2`; `scalingOrder` -2 → -1, `BALvl1GoodLit`, `nExt ≤` by `decide` |
| 3 `BALvl1B_part_struct` | B:470 | `G = baPC` normal (`decide`), `T = d1C` via `BASim_Ext_ext`; `d1C.splitG.length = 4` by `decide +kernel` |
| 4 (cases weight/edge/gg) | B:481 | `P_W`, `P_E`, `P_A`, concrete `lwSplit` memberships, `rfl` flags; output lists nonempty (`decide +kernel`) |
| 4 macro claims | B2:282 | `within` at `P_B` (`sameAtom` by `decide`), `ggSplit` at `P_C`, `j = 0`; outputs nonempty |
| 4 `baStepMono_holds` | B2:290 | the five frame steps `BALvl1AInst.hFA`-`hFE`, normality by `decide`, `0 < outs.length` by `decide +kernel` |
| 5 `baLvl1StepGood_holds` | B2:300 | `BALvl1AInst.locStepB`, `locStepC`, `normalB`, `normalC`; outputs nonempty |
| 2 `ba_lvl1StepGood_of_sim'` | B2:309 | arbitrary `m : ℂ`, all four hypotheses proved theorems, `locStepB`, `normalB`; outputs nonempty |
| data | B2:276 | `BASim_inv` of the five data by `decide`: nonzero `nS`, `nExt ∈ {1,2}`, nonempty `E`, `I` |
No `N = 0`, empty index, empty output list or `False` premise: every example carries `0 < outs.length` (or `splitG.length = 4`) proved by kernel evaluation. The instances are statement level (conclusions at the noncomputable packed outputs are obtained from the theorems, not evaluated), as the ticket's target 6 specifies ("statement level, as `BALvl1AInst`").

## 6. Paper deltas
`grep -n "BALvl1\|BAlvl1StepGood\|BAstepMono" docs/paper-deltas.md` → no hit. The Lean/paper difference (the paper, `B_graphical_lemmas.tex:407`, asserts only "an analogue of \Cref{lvl1 lemma} for the block Anderson model"; Lean fixes the measure `BALvl1Good` with `nExt` after `ord`) is proposed as candidate `T2442a` in the prove report §(d). Covered.

## 7. Observations (no verdict change)
- O1. Instance helpers `BALvl1BInst.tW`, `d1C`, `normalPC`, `outsW`, `outsE` (B:455-478) are public names without the `BALvl1B_` stem; they live in namespace `RBM.Graph.BALvl1BInst` (stem in the namespace, as `BALvl1AInst`). No clash: the full scan (`import RBM3D` + both modules) compiled.
- O2. Prove report (a)(i-vi) predicted ≈1,540 lines; delivered 809 (both files far under the 2,000 stop line).
- O3. `BALvl1B_part_struct` concludes one more fact than the ticket lists (`Δ.nExt ≤ G.nExt`); stronger, consumed by `BALvl1B_outs_mono`.

## Verdict
Targets 1-7: PASS. Overall: **PASS**. No dispatcher sign-off needed.
