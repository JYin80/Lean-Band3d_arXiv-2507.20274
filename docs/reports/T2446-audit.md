Auditor model: claude-opus-5-5
# T2446 audit (round 1) — BA-L L3a5 `Graph/BALvl1C`
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2446-audit1`, detached at `t/T2446` = 4a40bd2 (merge base with main 74af906). Started Mon Oct 12 10:19:34 UTC 2026 (`date -u`).

## 1. Statements against the pins (script diff, body after `:=`, whitespace-normalized)
```
$ python3 -I ext.py BALvl1C.lean docs/tickets/checks/T2446-check.lean ...
BAlvl1ExistsStep vs T2446_ExistsStep: IDENTICAL (83 chars)
BAlvl1Lemma vs T2446_Lemma: IDENTICAL (640 chars)
BAlvl1LemmaSize vs T2446_LemmaSize: IDENTICAL (820 chars)
$ python3 -I ext.py BALvl1C.lean t/T2395:RBM3D/Probe/T2395Pins.lean ...
BAlvl1ExistsStep vs BAlvl1ExistsStep: IDENTICAL (83 chars)
BAlvl1Lemma vs BAlvl1Lemma: IDENTICAL (640 chars)
```
Scratch copy of the check file (`import RBM3D.Graph.BALvl1C` added, not committed), appended lines:
```
example : BAlvl1ExistsStep = T2446_ExistsStep := rfl
example (d : ℕ) : BAlvl1Lemma d = T2446_Lemma d := rfl
example (d : ℕ) : BAlvl1LemmaSize d = T2446_LemmaSize d := rfl
example : T2446_ExistsStep := baLvl1ExistsStep_holds
example (d : ℕ) : T2446_Lemma d := baLvl1Lemma_holds d
example (d : ℕ) : T2446_LemmaSize d := baLvl1LemmaSize_holds d
example : T2446_Trans := @BAReach.trans
example : T2446_Induction := @ba_lvl1_induction
example : T2446_MuLt := fun K Γ Q hK hg => ba_lvl1_mu_lt hK hg
$ lake env lean T2446AuditCheck.lean > check.out; echo "check exit=$?"; grep -c error check.out
check exit=0
0
```
(Only warnings: unused binder names `K Γ Q` in the last `example`, scratch-only.) So targets 1, 2, 4, 5 equal the pins definitionally (`rfl`), `BAReach.trans`/`ba_lvl1_induction` have the pinned types, and `ba_lvl1_mu_lt` gives `T2446_MuLt` by unfolding. Measure (`BALvl1C.lean:95-100`): `((K - ord).toNat, nExt, nLoops, nS, nPairs)`, lex on `ℕ⁵` with `<` in every slot: the ticket's K3 measure. Quantifier order, the cutoff `K : ℤ`, the identity's data hypotheses (`3 ≤ L`, `BASelf`, `0 ≤ t < 1`, all `ℓe`), the window `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`, `1 ≤ W`, `1 ≤ L` are as pinned; `d` is free (no `3 ≤ d`), as in the pin.

## 2. Hidden hypotheses, vacuity, cycles
- No `structure`/`class`/`inductive` added: `grep -c "^inductive\|^structure\|^class" BALvl1C.lean` → `0`. The targets carry no premise beyond the pins.
- Premises used by public theorems, all merged and concluded by merged theorems: `BAReach` (inductive, `BALvl1A:69-71`; `BALvl1A_reach_refl`), `BALocStep` (`BALvl1A:65`, `∃ c t F, BAFrameStep (P.twist c t) F ∧ outs = F.map _`), `BALvl1Good` (`BALvl1B:63-67`, explicit counter inequalities). `BAGraph.LocStd` (`BAAtomic:70-73`) appears as a hypothesis only in private `BALvl1C_exists_pair` and inside the pins.
- Inputs: `baLvl1StepGood_holds` (`BALvl1B2:264`, proved: `ba_lvl1StepGood_of_sim' 0 BAimg_holds (baSim'_holds 0) baStepMono_holds baTwistInv_holds`), `baLvl1StepIdentity_holds` (`BALvl1A:547`), `BALvl1A_integrable_val`, `lvl1_choose_list`, `lvl1_sum_flatMap`, `lvl1_size_le`, `owx_integral_list_sum`: all on main. The unproved `BAsim` is not referenced: `grep -cw BAsim RBM3D/Graph/BALvl1C.lean` → `0`. No external hypothesis, so no limit check is required.
- Premise scan with the new module included:
```
$ printf 'import RBM3D\nimport RBM3D.Graph.BALvl1C\n#assert_rbm_axioms\n' > T2446AuditAx.lean; lake env lean T2446AuditAx.lean; echo "ax exit=$?"
axiom audit: 13036 theorems, 4108 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
premises found by scanning: 117 (borrowed 1, owed 52, structural 45, refuted 6, superseded 13).
ax exit=0
$ grep -nE "LocStd|BALvl1|BAReach|BALocStep|BAlvl1" ax.out    # no new premise flagged
(no output)
```
- No cycle: `BALvl1C` imports only `RBM3D.Graph.BALvl1B2` (line 6); the targets are proved from merged inputs, not from each other circularly (target 4 uses targets 2, 3; target 5 uses target 4).

## 3. Compiled nonempty instances (`BALvl1C.lean:564-623`, namespace `BALvl1CInst`; compile in the module build below)
| endpoint | line | data | deterministic hypotheses discharged |
|---|---|---|---|
| `baLvl1ExistsStep_holds` | 570-571 | `baPG baGGLhs` and `(baPG baPB).twist true true` | `Normal` by `decide` / merged `normalB`; `¬ LocStd` by `decide` (both) |
| `BAReach.trans`, `ba_lvl1_induction`, `ba_lvl1_mu_lt` (+ `baLvl1Lt_wf` via target 4) | 575-584 | an output `Q` of merged `locStepB`, `K = 100`; nonempty output list by `decide +kernel` (`0 < length`) | `ord < 100`, `¬ LocStd` by `decide +kernel`; `BALvl1Good` from `baLvl1StepGood_holds` |
| `baLvl1Lemma_holds` | 588-595, 599-605 | `d = 3`, `K = 10` at `baGGLhs`; `K = 3` at twist of `P_B`; `L = 4`, `W = 2`, `(g0P, EP, t0P, m0P)`, `ℓ0` | `Normal` by `decide`/`normalB`; `3 ≤ 4` by `norm_num`; `BASelf`, `0 ≤ t0P`, `t0P < 1` by merged `flowP_data` (`CouplingWindow:869`: `0 < t0P ∧ t0P < 1 ∧ BASelf 3 4 g0P EP m0P`) |
| `baLvl1LemmaSize_holds` | 609-621 | `d = 3`, `c = 1/4`, `K0 = 2`, `D = 10`, `baGGLhs`; size clause at `W = 4`, `L = 2`, `Ψ = 1/4`; identity at the flow data | `0 < 1/4`, `1 ≤ 4`, `1 ≤ 2`, `2^3 ≤ 4^2` by `norm_num`; `4^{-3/2} ≤ 1/4 ≤ 4^{-1/4}` by `calc` with `Real.rpow_le_rpow_of_exponent_le` |
None uses `N = 0`, an empty index, a collapsed window (`1/8 ≤ 1/4 ≤ 4^{-1/4} ≈ 0.707`), a `False` premise or a huge witness. No hypothesis is left as a pin-of-another-gate.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.BALvl1C > build.log 2>&1; echo "exit=$?"; tail -1 build.log; grep -c error build.log; grep -E "BALvl1C" build.log | head
exit=0
Build completed successfully (3826 jobs).
0
(no output: no warning in BALvl1C.lean)
$ lake build RBM3D > full.log 2>&1; echo "exit=$?"; tail -1 full.log      # branch state, RBM3D.lean unchanged
exit=0
Build completed successfully (4269 jobs).
$ (scratch check file) #print axioms ...
'RBM.Graph.baLvl1ExistsStep_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLvl1Lemma_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLvl1LemmaSize_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_lvl1_mu_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLvl1Lt_wf' does not depend on any axioms
'RBM.Graph.BAReach.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_lvl1_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1C_pair_selector' depends on axioms: [propext]
'RBM.Graph.BALvl1C_atCharge_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1C_hbad_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1C_end_in_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Graph/BALvl1C.lean | wc -l
       0
$ git diff --name-only main...HEAD
RBM3D/Graph/BALvl1C.lean
$ wc -l RBM3D/Graph/BALvl1C.lean      # stop line 2,000; reserve BALvl1C2 not created
     627 RBM3D/Graph/BALvl1C.lean
$ for n in <25 public names of BALvl1C>; do git grep -cwE "(theorem|def|abbrev|inductive|structure) $n" main -- RBM3D/; done   # main d5e9fa3
(no output: no clash)
```
Only the sole writable file is touched; `RBM3D.lean` and `Test/Axioms.lean` unchanged (the hub adds the import at merge). No frozen signature is edited (new file only). Unpinned helpers are public with the file stem `BALvl1C_` or `private` (§3 (E)).

## 5. Paper deltas
- Paper: `B_graphical_lemmas.tex:407-409` states the BA case only as repeated local expansions giving locally standard graphs "subject to the additional requirement that all solid edges are `G^c` edges". In Lean the `G^c` requirement is `BAGraph.Normal` (`BAVocab:158-159`: `∀ e ∈ Γ.solid, e.circ = true`), carried to every output by the third conjunct (`Q.g.Normal`); atom-level `LocStd`, the `ord ≥ K` cutoff, lists independent of the data, `=_E` as one integral identity at `PF d L W 0` under `BASelf`, `0 ≤ t < 1`, and the size form with constant 1 are covered by the prove report's candidate `T2446a` (report (d) l.215) together with merged entries D307/D308 for the band twin (`docs/paper-deltas.md:1239-1245`). No uncovered statement difference found.

## 6. Verdicts
| target | verdict |
|---|---|
| 1 `BAlvl1ExistsStep`, `BAlvl1Lemma` (pins, verbatim) | PASS |
| 2 `baLvl1ExistsStep_holds` | PASS |
| 3 `BALvl1Mu`, `BALvl1Lt`, `baLvl1Lt_wf`, `ba_lvl1_mu_lt`, `BAReach.trans`, `ba_lvl1_induction` | PASS |
| 4 `baLvl1Lemma_holds` | PASS |
| 5 `BAlvl1LemmaSize`, `baLvl1LemmaSize_holds` | PASS |
| 6 instances | PASS |
| 7 C1 / registry | PASS (data hypotheses are `BASelf`, `0 ≤ t < 1`, `3 ≤ L` only; no new inductive; scan clean) |

Observations (no effect on statement, instance, build, axioms or delta coverage):
- O1. The instances of targets 4 and 5 use the existential lists without exhibiting `outs ++ errs ≠ []`; the hypotheses are all discharged at nondegenerate data, which is what §4 step 2 asks. (Already noted by the prover, report (d).)
- O2. The target-5 instance reads the size clause at `L = 2` (allowed by the pin's `1 ≤ L`) while the identity is read at `L = 4`; both are within the pinned hypotheses.
- O3. Prove report (b) groups `BALvl1Lt` under "NONE" axioms; it is a `def`, consistent with the scratch output.

**Overall: PASS.** No dispatcher sign-off needed.
