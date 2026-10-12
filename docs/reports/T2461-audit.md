Auditor model: claude-opus-5-5

# T2461 audit, round 1 (Mon Oct 12 17:22:16 UTC 2026)

Branch `t/T2461` at d36677f (merge base with main 62eed82; main a1628b9). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2461-audit1` (detached).
Targets: (1) `baNetLift2_holds`, (2) `baFlow_premises`, (3) the `d = 3` instances. Module `RBM3D.BA.NetLiftBA` (838 lines, stop line 2,000).

## 1. Diff scope
```
$ git diff --stat main...HEAD
 RBM3D/BA/NetLiftBA.lean | 838 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 838 insertions(+)
$ git diff main...HEAD -- RBM3D/Path RBM3D/Chain RBM3D/Induction RBM3D/BA/FlowPins.lean RBM3D/BA/TwistLoop.lean \
    RBM3D/BA/Step1Setup.lean RBM3D/BA/KBase.lean RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ grep -rn NetLiftBA RBM3D RBM3D.lean | grep -v "^RBM3D/BA/NetLiftBA.lean" | wc -l      (importers)
       0
```
Only the sole writable file; no frozen file, no `Test/Axioms.lean`; `RBM3D.lean` untouched (the hub adds the import line).

## 2. Statements against the pins (script)
`stmt.py` extracts the text between `theorem <name> (d : ℕ) :` and `:= by` and the body of `def T2461_* (d : ℕ) : Prop :=` in the check file, whitespace-normalised.
```
$ python3 -I stmt.py RBM3D/BA/NetLiftBA.lean docs/tickets/checks/T2461-check.lean
baNetLift2_holds vs T2461_NetLift2BA : IDENTICAL
baFlow_premises vs T2461_BAFlowPremises : IDENTICAL
```
The pin `STNetLift2gL` (`Chain/Step2Gen.lean:602`, unchanged on the branch) quantifies `κ ε 𝔡 > 0`, `𝔠`, `sz`, `z`, `Flow`,
`0 ≤ s ≤ t ≤ T0`, every `Cd`, and the three per-time families → the three uniform families. Target 1 instantiates it at the
quadruple `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`. The same quadruple as the consumer `BAStep2` (`FlowPins.lean:432`), checked:
```
example (d : ℕ) : BAStep2 d = STStep2G d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := rfl   -- compiles
```
Every `d`, no `3 ≤ d`; no premise beyond the pin's. Target 2 has the same body as the probe `T2452_ba_premises` (`t/T2452:RBM3D/Probe/T2452Pins.lean:179-181`).
In the probe the data binders are implicit; here they are explicit. The ticket allows this ("up to the name and binder implicitness").

Auditor examples required by the ticket. The check file with `import RBM3D.BA.NetLiftBA` and these lines appended inside `namespace RBM.BA`, compiled with `lake env lean`:
```
example : ∀ d : ℕ, T2461_NetLift2BA d := baNetLift2_holds
example : ∀ d : ℕ, T2461_BAFlowPremises d := baFlow_premises
```
Output: no error on any line before the trailing `#assert_rbm_axioms`. That command's partial-import error is explained in §5.

## 3. Hidden hypotheses, vacuity, cycles
- Both public theorems have exactly the pin's binders, with no structure argument. The per-time families `STStep2LocalPTgL`, `STStep2AvgPTgL`, `STStep2DecayPTgL` are premises *inside* the pin `STNetLift2gL`. The ticket authorises this ("Inputs used as hypotheses only (a)"), and the band pin has the same form.
- `BAFlow` is discharged at concrete data by the merged `flow_sz0`. `baFlow_premises` is used by target 1 and is not circular. Every private helper is under the stem `NetLiftBA_` or comes in by `open private` from merged modules (`Step1Setup`, `KBase`, `TwistKer2`, `NetLift1`, `NetLift2`). No private is edited or deleted.
- The new module adds no unclassified premise to the registry. I ran `#assert_rbm_axioms` with the same partial imports twice, with and without `import RBM3D.BA.NetLiftBA`:
```
$ wc -l prem_with.txt prem_without.txt ; diff prem_without.txt prem_with.txt ; echo diff-exit $?
      38 prem_with.txt
      38 prem_without.txt
diff-exit 0
```
The lists are identical. The 37 listed premises are a partial-import artefact (their producers are not imported) and are the same with and without the new file.
- C1 / spectral rule (ticket target 4), my grep (`grep -c -F`):
```
|E:0 2 - κ:0 mE:0 zt:0 etaT:0 lemT:0 lemE:0 STFlow:0 STflowE:0 v3_premises_of_stFlow:0 bandFM:0 nl_loop_sub:0 nl_eta_inv_le:0
nl_K_diff:0 nl_close:0 nl2_loop_sub:0 nl2_eta_inv_le:0 nl2_entry_:0 nl2_loc_close:0 nl2_avg_close:0 3 ≤ d:0
sorry:0 admit:0 native_decide:0 axiom:0 maxHeartbeats:0
```

## 4. Compiled nonempty instances (file lines 802-836, `namespace RBM.BA.NetLiftBAInst`)
- (a) Target 1 is applied at `d = 3`, `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/2`, `t ≡ 2/3`, with `t ≤ t₀` from `t0_sz0` and every `Cd`. The positivity premises are discharged by `by norm_num`, and `0 ≤ s`, `s ≤ t` by `norm_num`.
- (b) The same data with `s ≡ 0`, `t ≡ 1/2`, using `(half_lt_t0 n).le`.
- (c) Target 2 is applied at the data of (a).
- In (a) and (b) only `hL hA hD` stay as hypotheses. These are the three per-time pin statements, and CLAUDE.md §4 step 2 allows them to stay.
- The data are nondegenerate. `sz0` has `N_0 = (32·4)^3 = 2097152`, the window `s < t` is nonempty in both (a) and (b), and the witnesses are not astronomically large. All three examples compile in the module build (§5).

## 5. Build and axioms
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2461-audit1 && lake build RBM3D.BA.NetLiftBA ; echo exit $?
✔ [4062/4062] Built RBM3D.BA.NetLiftBA (10s)
Build completed successfully (4062 jobs).
exit 0
$ grep -n "NetLiftBA" build.log | grep -E "warning|error" | wc -l      (warnings/errors located in the new module)
0
$ lake env lean <check file + NetLiftBA + audit examples>    (lines 363-365 of output)
'RBM.BA.baNetLift2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFlow_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
...:238:0: error: axiom audit: 37 premise(s) that no theorem of this development proves are in none of ...
```
- Line 238 is the trailing `#assert_rbm_axioms` under partial imports. It is not a defect of this ticket: the identical list appears without the new module (§3).
- The hub runs `import RBM3D` + `#assert_rbm_axioms` in the full `lake build` at merge. The prove report says the full build passed with a temporary import line: `axiom audit: 13373 theorems, 4251 definitions, 0 axioms in RBM`.
- The other build warnings (793) are replayed from cached merged modules (`Graph/LWLvl1`, `Induction/EMn2Exp1`, ...). None comes from `NetLiftBA`.

## 6. Paper deltas
- The Lean target 1 is the merged pin at merged BA data. The paper's statement (`1_2:1400`; at BA `7_8:1993-1994`, where Step 2's lemmas "remain valid") is the uniform-in-`u` lift by "a standard net argument", with no BA text on the net.
- The prove report proposes `T2461a` (informational): BA has no written net lift, and the proof adds one routine BA modulus, the time-Lipschitz bound of `𝒦^{(2)}`. No paper statement changes.
- The `d`-generality (no `3 ≤ d`) is a strengthening that the pin already carries.
- Coverage: complete.

## 7. Observations (no RETURN)
- O1. The ticket's acceptance list asks for the import line in `RBM3D.lean`. The branch leaves it to the hub, which is the precedent of T2451 and is §3 (A) step 4.
- O2. The report's (c) says "Names verified absent: none looked for". This is acceptable.

## Verdicts
- Target 1 `baNetLift2_holds`: **PASS**.
- Target 2 `baFlow_premises`: **PASS**.
- Target 3 instances: **PASS**.

Ticket verdict: **PASS**. No dispatcher sign-off needed.
