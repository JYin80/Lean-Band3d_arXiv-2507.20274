Auditor model: claude-opus-5-5

# T2465 audit, round 1 (Mon Oct 12 20:19:11 UTC 2026, `date -u`)

Branch `t/T2465` at `a90e3aaf` (merge base with `main` `ad52b370`; `main` at `d0d9fe0f`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2465-audit1` (detached).
Scratch files: `<scratchpad>/T2465/audit/` (`sdiff.py`, `scr.lean`, `scr.out`, `assert.lean`). Nothing in the audit worktree was edited.

## 1. Diff scope and hygiene
```
$ git diff --stat main...t/T2465
 RBM3D/Graph/BAExp14e.lean | 433 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 433 insertions(+)
$ git diff --stat ad52b370 main -- RBM3D/       # what main gained since the branch base
 RBM3D/BA/Step1Prime.lean | 1181 +++
 RBM3D/Test/Axioms.lean   |   12 +-
$ grep -nwE "sorry|admit|axiom|native_decide|mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus" RBM3D/Graph/BAExp14e.lean | wc -l
       0
$ grep -cE "^(inductive|structure|class|axiom|instance)" RBM3D/Graph/BAExp14e.lean
0
$ grep -nE "^(theorem|def|private theorem|example)" RBM3D/Graph/BAExp14e.lean | cut -c1-90
60:def BAGraphPrecJoin (d : ℕ) : Prop :=
77:private theorem BAExp14e_kernels (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 <
139:private theorem BAExp14e_pathwise (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0
180:theorem baGraphPrecJoin_holds (d : ℕ) : BAGraphPrecJoin d := by
331:theorem baG5LeafPrec_of : ∀ d : ℕ, BAGraphPrecJoin d → BAG5LeafPrec1 d → BAG5LeafPrec
340:theorem baG5LeafPrec_holds : ∀ d : ℕ, BAG5LeafPrec d := fun d =>
347:theorem baExp14bS3_holds : ∀ d : ℕ, BAExp14bS3 d := fun d => baExp14bS3_of_leaf d (baG
365:def leafPrecInst (P : BAPGraph (Fin 2)) : Prop :=
374:theorem baAllMP_counters : BAG5LeafInst.baAllMP.g.nM = 0 ∧ BAG5LeafInst.baAllMP.g.nW =
386:example (hE : STLocalEntrygL ...) : leafPrecInst BAG5LeafInst.baAllMP
393:example (hE hA hL hK hD) : leafPrecInst BAG5LeafInst.baAllMP      -- baG5LeafPrec_of
401:example (hE hA hL hK hD) : leafPrecInst BAG5LeafInst.baAllMP      -- baG5LeafPrec_holds, n_M = 0 branch
410:example (hE hA hL hK hD) : leafPrecInst BAExp14dInst.leaf1P      -- baG5LeafPrec_holds, n_M = 1 branch
419:example (hE hA hL hK hD) : PrecL sz0 μ0 ... BAExp14bS3Fam ...     -- baExp14bS3_holds
```
Only the sole writable file `RBM3D/Graph/BAExp14e.lean` is touched (the `RBM3D.lean` import line is left to the hub, §3 (A) 4). Main's later changes (`Step1Prime`, `Test/Axioms.lean`) are disjoint from this file. No frozen file (`BAExp14b*`, `BAExp14c*`, `BAExp14d*`, `BAG5Leaf`, `BASizeClaim*`, `Test/Axioms.lean`) is edited by the branch.

## 2. Statements against the pins (script diff)
```
$ python3 -I sdiff.py   # check-file pin body vs Lean def body, whitespace-normalised
T2465_BAGraphPrecJoin (check) vs BAGraphPrecJoin (Graph/BAExp14e): found=True identical=True chars 673/673
T2465_BAG5LeafPrec (check) vs BAG5LeafPrec (Graph/BAExp14c): found=True identical=True chars 750/750
T2465_Q1Need (check) vs BAG5LeafPrec1 (Graph/BAExp14dB): found=True identical=True chars 763/763
```
So S3 (T2464's pin text) and S2 (T2466's export equals `T2465_Q1Need`) do not occur. Theorem types are checked against the pins by term-mode examples in a scratch copy of the check file (check file Section 1 + `import RBM3D.Graph.BAExp14e` + Section 2 + the lines below), not committed:
```
#check @RBM.BA.BAG5LeafPrec
#check @RBM.BA.baExp14bS3_of_leaf
example : ∀ d, T2465_BAGraphPrecJoin d := RBM.BA.baGraphPrecJoin_holds
example : ∀ d, T2465_LeafPrecOf RBM.BA.BAG5LeafPrec1 RBM.BA.BAG5LeafPrec d := RBM.BA.baG5LeafPrec_of
example : ∀ d, T2465_LeafPrecOf T2465_Q1Need T2465_BAG5LeafPrec d := RBM.BA.baG5LeafPrec_of
example : ∀ d, T2465_BAG5LeafPrec d := RBM.BA.baG5LeafPrec_holds
example : ∀ d, RBM.BA.BAExp14bS3 d := RBM.BA.baExp14bS3_holds
example : ∀ d, RBM.BA.BAExp14bS3 d := fun d => RBM.BA.baExp14bS3_of_leaf d (RBM.BA.baG5LeafPrec_holds d)
example : ∀ d, RBM.BA.BAG5LeafPrec1 d → T2465_Q1Need d := fun _ h => h
$ lake env lean scr.lean > scr.out 2>&1; echo exit=$?; grep -nE "error|sorry" scr.out | wc -l
exit=0
0
$ grep -E "BAG5LeafPrec :|baExp14bS3_of_leaf :" scr.out
BAG5LeafPrec : ℕ → Prop
baExp14bS3_of_leaf : ∀ (d : ℕ), BAExp14bS3OfLeaf d
```
Per target, statement reading:
- **Target 1** `BAGraphPrecJoin`: parameters in the paper's order (`3 ≤ d`, `κ ε 𝔡 > 0`, `𝔠`, `sz`, `z`, `BAFlow`, `t` with `0 ≤ t ≤ T₀`), then only `STLocalEntrygL` of the five Step 1/2 pins, then `∀ P` normal with `n_M = 0`. Conclusion `‖𝔼 Γ_xy‖ ≺ t^{n_W} η⁻¹ Bctl^{ord/2}` over all pairs. There is no `2 ≤ n_W` hypothesis, and the case `t^{n_W} = 0` is handled in the proof (`BAExp14c_val_zero`, `:304-313`), so the pin is not weakened.
- **Target 2** `baG5LeafPrec_of : ∀ d, BAGraphPrecJoin d → BAG5LeafPrec1 d → BAG5LeafPrec d` is `T2465_LeafPrecOf` with `Q1 := BAG5LeafPrec1`, `LP := BAG5LeafPrec`, as the release note fixes. `baG5LeafPrec_holds : ∀ d, BAG5LeafPrec d` is unconditional.
- **Target 3** `baExp14bS3_holds : ∀ d, BAExp14bS3 d` is the merged pin (five premises inside the def), equal to `baExp14bS3_of_leaf d (baG5LeafPrec_holds d)`.

## 3. Vacuity, hidden hypotheses, cycles
- No new `structure`/`class`/`inductive` (grep above). The only Prop premises of public theorems are `BAGraphPrecJoin d` and `BAG5LeafPrec1 d` in `baG5LeafPrec_of`, the pinned conditional form; both are discharged in `baG5LeafPrec_holds` by `baGraphPrecJoin_holds` and the merged `baG5LeafPrec1_holds` (T2466).
- Case split (`:331-336`): `BAG5LeafProps` conjunct 2 gives `n_M ≤ 1`. `n_M = 0` goes to target 1 (conjunct 1 `Normal`) and `n_M = 1` to `BAG5LeafPrec1` (the same five premises, no distinct-molecule hypothesis: identical to `T2465_Q1Need` above). Both branches are exercised by instances (`:401`, `:410`).
- Dependencies are merged results: `baClaimSize`, `baKBound_E`, `BAExp14c_val_env`, `BAExp14c_floor`, `BAExp14d_val_scale`, `lwExpTerm6_arith`, `BAExp14a_prec_integral`, `BAExp14a_det_iff`, `baExp14bS3_of_leaf`, `baG5LeafPrec1_holds`, plus five merged private lemmas reached by `open private` (`:39-42`). No cycle: `BAExp14e` imports only `BAExp14cB` and `BAExp14dB`, and nothing on `main` imports it.
- External hypothesis: only the registered owed pin `STLocalEntrygL` (another gate's input). Limit check in prove report (a)(ii): leading term ratio 0.983 < 1 against `W^d Bctl` at the instance. No new hypothesis is introduced.

## 4. Compiled nonempty instances
Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`; at `n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `Defs/Sizes.lean:260-267`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`), `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`, `:1254`). The leaf is `baAllMP` (`baAllM_leaf`: `BAG5Leaf`, `BAG5LeafProps`, `ord = 4`; `n_S = 0`, `n_W = 2`, `n_A = 0`, `n_M = 0` by `decide`, `BAG5Leaf.lean:1062-1065`), and T2466's `leaf1P` (`n_M = 1`) for the other branch.
| target | instance | deterministic hypotheses | kept (other gates' pins) |
|---|---|---|---|
| 1 `baGraphPrecJoin_holds` | `:386` at `baAllMP` | `3 ≤ 3`, `κ, ε, 𝔡 > 0`, `BAFlow`, `0 ≤ t ≤ T₀`, `Normal`, `n_M = 0`: all discharged | `STLocalEntrygL` |
| 2 `baG5LeafPrec_of` | `:393` at `baAllMP` | all discharged, both halves given by theorems | the five Step 1/2 pins |
| 2 `baG5LeafPrec_holds` | `:401` `baAllMP`; `:410` `leaf1P` | all discharged | the five Step 1/2 pins |
| 3 `baExp14bS3_holds` | `:419` at `d = 3`, `sz0`, `t ≡ 1/2` | all discharged | the five Step 1/2 pins |
None is degenerate: `N ≥ 2097152`, nonempty index `Idx 3 L W × Idx 3 L W`, `t = 1/2` inside `(0, T₀)`, `n_W = 2`, no `False` premise, witnesses of moderate size. All compile (build below).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BAExp14e 2>&1 | grep -E "^error|BAExp14e|Build completed|declaration uses" | tail -5
Build completed successfully (4046 jobs).
$ lake env lean scr.lean | grep "depends on axioms"
'RBM.BA.baGraphPrecJoin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baG5LeafPrec_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baG5LeafPrec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExp14bS3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14eInst.baAllMP_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D 2>&1 | grep -E "^error|axiom audit|Build completed" | tail -3
info: RBM3D.lean:534:0: axiom audit: 13598 theorems, 4345 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4302 jobs).
$ printf 'import RBM3D\nimport RBM3D.Graph.BAExp14e\n#assert_rbm_axioms\n' > assert.lean; lake env lean assert.lean | head -4; echo exit=$?
axiom audit: 13603 theorems, 4347 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit=0
```
(The output of `#assert_rbm_axioms` continues with the unchanged premise ledgers. `Test/Axioms.lean` is unchanged by the branch.)

## 6. Paper deltas
- The `t^{n_W}` factor in the bound `(Gammamuxy)` (`B:88`), and the `≺ → 𝔼` route, are covered by registered D573 (T2255a–d, `docs/paper-deltas.md`). It reads "`(Gammamuxy)` 带 `t^{n_W}`" ("`(Gammamuxy)` carries `t^{n_W}`").
- The leaf class `BAG5Leaf`/`BAG5LeafProps` is covered by T2398a (carried by `BAG5LeafPrec`, merged with T2464).
- The split `n_M = 0` (here) / `n_M = 1` (T2466) is a proof decomposition of the merged pin `BAG5LeafPrec`, whose union is the pin. It is not a statement difference.
- No uncovered Lean/paper statement difference was found. The prove report proposes no new candidate, and none is needed.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The file opens five private lemmas of merged files by `open private` (`BASizeClaim_theta_decay`, `BAVocab_val_of_factor`, `BAVocab_val_of_not`, `BAExp14d_svar0`, `BAExp14d_entry_whp`). If those are renamed, this file breaks. The prove report (d) records this. Precedent: `BAExp14c.lean:35-43`.
- O2. Prove report (a)(i) row 11 cites `BAExp14a_theta_l1` for the `S⁺'` kernel bound. Section (a′) corrects this to `BASizeClaim_theta_decay` + `lwKBound_of_decay`, which matches the code (`:117-118`, `:126`).
- O3. `BAGraphPrecJoin` asks only `Normal ∧ n_M = 0`, not the band's `LWJoined`. This makes the pin stronger than the band twin, not weaker, and the pin text equals the check file.
- O4. The branch base `ad52b370` is behind `main` `d0d9fe0f` by T2468 + H256. Those touch `BA/Step1Prime.lean` and `Test/Axioms.lean` (disjoint). The hub's full build at merge decides.

## Verdicts
| target | verdict |
|---|---|
| 1 `BAGraphPrecJoin`, `baGraphPrecJoin_holds` | PASS |
| 2 `baG5LeafPrec_of`, `baG5LeafPrec_holds` | PASS |
| 3 `baExp14bS3_holds` | PASS |
| 4 instances (`BAExp14eInst`) | PASS |
| 5 registry (none; no `inductive`, `Test/Axioms.lean` unchanged) | PASS |
Ticket T2465: **PASS**. No dispatcher sign-off needed.
