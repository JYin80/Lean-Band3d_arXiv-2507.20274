Auditor model: claude-opus-5-5

# T2193 audit, round 1 (Mon Oct  5 19:14:29 UTC 2026)

Inputs: `docs/tickets/T2193.md` and `docs/tickets/T2193-amend-1.md` (target 2 withdrawn, route (d)), `docs/reports/T2193-prove.md`,
branch `t/T2193` at `b502f4e` (merge base `3429d7d`), detached audit worktree `RBM3D-wt/T2193-audit1`.
Targets after Amend 1: **target 1** (pin change `STLemDecCalEConcl`), **target 3** (`stLemDecCalE_holds`, endpoint). Target 2 is withdrawn (Amend 1); target 2′ is internal to target 3.

## 0. Files touched
```
$ git diff --stat main...t/T2193
 RBM3D/Induction/LemDecCalEPrec.lean | 1704 +++++++++++++++++++++++++++++++++++
 RBM3D/Induction/Step5Pins.lean      |    6 +-
 RBM3D/Test/Axioms.lean              |    2 +-
 3 files changed, 1709 insertions(+), 3 deletions(-)
```
Exactly the three sole writable files.

## 1. Target 1: the pin `STLemDecCalEConcl` (`Step5Pins.lean:161`)
```
$ git diff main...t/T2193 -- RBM3D/Induction/Step5Pins.lean     (all hunks, `-`/`+` lines)
-for `D` with `W^D ≥ N`: the three bounds (`res_deccalE_lk`) ...
+for `D` with eventually `(L^dW^{6d})² ≤ W^D` and `J*_{u,D} ≤ W^{1/2}` (DECISIONS §61, §63; paper `W^D ≥ N`, paper-delta T2193a/b): the three bounds (`res_deccalE_lk`) ...
-    ∀ D : ℝ, 0 < D → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
+    (∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) →
+    ∀ D : ℝ, 0 < D →
+      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
$ # body of the branch's def (lines 162..before the next docstring) vs check file lines 32-60, blank lines dropped
$ diff pin_branch.txt pin_check.txt
27a28
> end RBM.Gauss.Sizes
```
The only difference is the check file's closing `end` line: the body equals `STLemDecCalEConcl_new_pin` (binder and name stripped).
`STLemDecCalE` (`:193`) and `inst_lemDecCalE` (`:596`) keep their text; no other pin changed. Compile consumers:
```
$ grep -rn 'STLemDecCalEConcl\|STLemDecCalE\b\|inst_lemDecCalE\|stLemDecCalE_holds' RBM3D --include='*.lean' | grep -v LemDecCalEPrec.lean
  (code) Step5Pins.lean:161 def, :193 STLemDecCalE, :596-597 inst_lemDecCalE; (docstrings only) Path/LemDecCalE.lean:35,97,
  Path/LemDecCalEdif.lean:78, Path/LemDecCalEwG.lean:79, Induction/LemDecCalELip.lean:15,846, Step5Pins.lean:19
$ git grep -n '<same pattern>' main -- 'RBM3D/*.lean' | grep -v 'Step5Pins\|Path/LemDecCalE\|LemDecCalELip\|Test/Axioms'
  (no output: no new consumer on current main 3fc9d03)
```
Mathematics: the change adds the premise `Jst ≤ W^{1/2}` (M3) and replaces the floor `N ≤ W^D` by `(L^dW^{6d})² ≤ W^D` (M1), exactly as the ticket
(§61/§63). Both premises are satisfiable (Jst ≡ 1; the floor at `sz0`, `D = 42`, every `n`: `lemDecCalEPrec_inst_floor`, §3), so the pin is not vacuous.
**Target 1: PASS.**

## 2. Target 3: `stLemDecCalE_holds`
```
$ grep -n "^theorem stLemDecCalE_holds" RBM3D/Induction/LemDecCalEPrec.lean
1550:theorem stLemDecCalE_holds (d : ℕ) : STLemDecCalE d := by
$ lake env lean axioms.lean    (#check, plus `example : STLemDecCalE = fun d => STIngR5 d STReg5III (fun sz E s t => STLemDecCalEConcl sz E s t) := rfl`)
RBM.Gauss.Sizes.stLemDecCalE_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STLemDecCalE d
```
- Statement: exactly the ticket's `theorem stLemDecCalE_holds (d : ℕ) : STLemDecCalE d`, with `STLemDecCalE` the merged pin after target 1 (no local restatement;
  the `rfl` example above compiles). No hypothesis of its own; quantifier order, regime (iii), `∀ᶠ` floor, `Prec` (uniform in `u`) and the right sides are those of the pin.
- Hidden hypotheses / vacuity: none in the signature; the proof `intro`s exactly the `STIngR5` data (`Step5Pins.lean`), chooses `𝔠d := 1/100`
  (allowed: `0 < 𝔠d ≤ 1/100`), and uses the pin's stochastic premises `STStep2Concl` (`.1 = STLocalEntryU`, `.2.1 = STAvgU`), `STLmaxU`, plus the pin's
  `Prec` premise on `STLK2`. No structure field carries an assumption; `lemDecCalEPrec_good`, `_Bounds`, `_R*` are public defs used internally.
- Cycle: the module imports only merged modules (`Path/LemDecCalEdif2`, `Path/LemDecCalEwG`, `Green/GbEXP`, `Path/NetLift2`, `Path/KellStar`, `Induction/Step5Kit`,
  `Induction/LemDecCalELip` = T2198, merged e4126a2); none of them mentions `stLemDecCalE_holds`; the pin `STLemDecCalE` is not assumed anywhere in the proof.
- Rule "do not use `stGbEXP_holds`/`STGijGEX` for M2": `grep -n 'stGbEXP_holds\|STGijGEX' RBM3D/Induction/LemDecCalEPrec.lean` → 0 lines (per-time `GijGEXPTSwap` via `gbEXPV3` instead, Amend 1 (P)).
**Target 3: PASS.**

## 3. Compiled nonempty instances (`LemDecCalEPrec.lean:1666-1702`, `section Instances`)
```
1672:theorem lemDecCalEPrec_inst_floor (n : ℕ) :
    (((sz0.L n : ℕ) : ℝ) ^ 3 * ((sz0.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz0.W n : ℕ) : ℝ) ^ (42 : ℝ)
1683:theorem lemDecCalEPrec_inst_Jst :   (Jst ≡ 1) : (∀ n u D, 1 ≤ 1) ∧ (∀ n u D, 1 ≤ W_n^{1/2})   (sz0)
1694:example := inst_lemDecCalE (stLemDecCalE_holds 3) 1 one_pos
1698:example (h : STLemDecCalEConcl sz0 (STflowE z0) sInst tInst) :=
  h (fun _ _ _ => 1) lemDecCalEPrec_inst_Jst.1 lemDecCalEPrec_inst_Jst.2 42 (by norm_num)
    (Eventually.of_forall lemDecCalEPrec_inst_floor)
```
The first example applies the endpoint at `d = 3`, data `(sz0, z0, sInst = 0, tInst = 1/16)`, `Cd = 1`, through the merged `inst_ing5_III`, which discharges
`3 ≤ 3`, `flow_z0`, `0 ≤ s < t ≤ lemT`, `sz0_reg5III`, `sz0_con`; the result type `InstIng5Concl` keeps only the stochastic Step 1-4 pins as hypotheses
(`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong`, `STStep1Loop`, `STStep2Concl`, `STLmaxU`, `STLKU`: other gates' pins). The second example discharges
the conclusion's deterministic premises (`Jst ≡ 1`, `D = 42`, the floor for every `n`); only the `Prec` premise on `STLK2` (the paper's `(eq:def_new_J*)`
hypothesis) stays. Nondegenerate: `L_n = 4(n+1) ≥ 4`, `W_n = (2(n+1))^5`, window `[0, 1/16]`, `STIdx2` nonempty, `Jst = 1`, `D = 42` (not astronomically large).
These are exactly the instances the ticket and Amend 1 require (target-2 instance dropped by Amend 1). Both compile (build in §4).

## 4. Build, axioms, forbidden tokens
```
$ cd RBM3D-wt/T2193-audit1 && lake build RBM3D.Induction.LemDecCalEPrec RBM3D.Induction.Step5Pins
Build completed successfully (3844 jobs).          (exit=0; 0 lines mention LemDecCalEPrec.lean: no warning, no error)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/LemDecCalEPrec.lean RBM3D/Induction/Step5Pins.lean | wc -l
0
$ lake env lean axioms.lean     (`#print axioms` for every `theorem|def|abbrev` at column 0 of the new file, 43 names)
exit=0
lines=43 standard-only=43 noaxioms=0
'RBM.Gauss.Sizes.stLemDecCalE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry (`Test/Axioms.lean`): the owed line `STLemDecCalE` is deleted (ticket) and `STLocalEntryU` is added as owed (§20 rule, reported by the pre-check:
it is now a hypothesis of five new lemmas). Pre-check on the **merge with current main** (`main` = 3fc9d03 has moved past the branch base; it changed
`Test/Axioms.lean` in T2201: `refutedProps`):
```
$ git merge-tree --write-tree main t/T2193    → clean (no conflict); scratch commit 264834d (unreferenced) checked out detached in the audit worktree
$ lake build <every module imported by RBM3D.lean> RBM3D.Induction.LemDecCalEPrec    → build exit=0
$ lake env lean precheck.lean     (RBM3D.lean's imports + `import RBM3D.Induction.LemDecCalEPrec` + `#assert_rbm_axioms`)
axiom audit: 5996 theorems, 2102 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STLocalEntryU: 5 [no certificate]
premises found by scanning: 110 (borrowed 1, owed 82, structural 23, refuted 4).
precheck exit=0
```
`STLemDecCalE` no longer appears among the owed premises (it is proved). The audit worktree was returned to `b502f4e` afterwards.

## 5. Paper deltas
Paper `3_5:2317-2338`: "for any `u ∈ [s,t]` ... large enough `D` (such that `W^D ≥ N`)", deterministic `J*` with `(eq:def_new_J*)` (`3_5:2310`).
Lean/paper differences and their coverage (prove report (d)):
| difference | candidate |
|---|---|
| floor `(L^dW^{6d})² ≤ W^D` (eventually) instead of `W^D ≥ N` | T2193a |
| added premise `J*_{u,D} ≤ W^{1/2}` | T2193b |
| conclusions uniform in `u` (`Prec`, net lift of the conclusions; `(GijGEX)` used per time, one orientation) vs "for any `u`" | T2193c′ (Amend 1) |
| realized control `J♯` (internal only; the statement keeps the deterministic `Jst`) | D499 (T2198c), cross-referenced |
| `N^τ`/`zdistInf`/explicit loss | earlier deltas (D374, D429, D434, D437, D439, D454), unchanged statement text |
Every statement difference is covered.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1 (hub, merge step 3): `main` changed `RBM3D/Test/Axioms.lean` after the branch base (T2201: `refutedProps`, primed `UN*'` lines). Bring this file in by a
  three-way merge of the branch's two hunks (clean, §4), **not** by copying the branch's file, which would revert T2201's registry changes and fail the build.
- O2: the ticket's acceptance text says line 163 is replaced "in place"; the branch splits the new `∀ D …` and floor over two lines (the check file's line
  breaks), so the hunk is +4/−2 instead of +3/−2 at `:162-163`. Content equals the check file (§1).
- O3: the prove report notes that `AsGMcPT` (owed) now has a theorem concluding it (`lemDecCalEPrec_asGMcPT`); it still lists as "carries nothing yet". Registry
  bookkeeping for the dispatcher; the registry pre-check exits 0.
- O4: the new file has public `def`s (`lemDecCalEPrec_good`, `_R1`…`_R3`, `_R2₀`, `_R3₀`, `_Bounds`, `abbrev _V3`), all with the file-stem prefix (§3 (E)).

## Verdict
- Target 1 (pin change): **PASS**.
- Target 3 (`stLemDecCalE_holds`): **PASS**.
- Target 2: withdrawn by Amend 1 (not audited).
**Ticket T2193: PASS.** No dispatcher sign-off needed.
