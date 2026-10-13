Auditor model: claude-opus-5-5
# T2486 audit, round 1: part (a) of the pre-signed split (U2-BA (a), targets 1-5) — PASS

Date: Tue Oct 13 05:51:08 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2486-audit1`, detached at `t/T2486` = `19c7f4c7`
(merge base `66b2ab97`; `main` is now `e6c26ca4`). Inputs: ticket `docs/tickets/T2486.md`, Amend 1 (`T2486-amend-1.md`, read first),
check file `docs/tickets/checks/T2486-check.lean`, prove report `docs/reports/T2486-prove.md`. Scratch in `scratchpad/T2486/`.
Scope: section (a) of the prove report applies the pre-signed split (central 2,014 > 1,950), so this round audits only
`BA/KDecayBA.lean` (target 1) and `BA/SEforLnBA.lean` (targets 2-5). Part (b) (`B45BA`, targets 6-8) is for `t/T2486b` and is not audited here.

## 1. Diff and file ownership
```
$ git diff --stat main...HEAD
 RBM3D.lean              |   2 +
 RBM3D/BA/KDecayBA.lean  | 885 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/SEforLnBA.lean | 371 ++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   8 +-
$ git diff main...HEAD -- RBM3D.lean        # two import lines, before #assert_rbm_axioms: +import RBM3D.BA.KDecayBA, +import RBM3D.BA.SEforLnBA
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   # 4 lines, text after `--` only (owner texts)
-   `RBM.BA.STKcalDecaygL, -- ... owner U2-BA (`BAKcalDecay`); ...      +   ... BA: `baKcalDecay_holds` (T2486); ...
-   `RBM.BA.STSEforLnConclgL / STSEforLngL / STEKDecaygL, -- ... BA: U2-BA
+   ... BA: `baSEforLnConclgL_of`, `baSEforLn_holds`, `baEtermDecaygL` (T2486)
$ git diff --stat main...HEAD -- RBM3D/Chain RBM3D/Induction RBM3D/Loop | wc -l        # G1
       0
$ git diff --name-only main...HEAD -- RBM3D/BA      -> RBM3D/BA/KDecayBA.lean, RBM3D/BA/SEforLnBA.lean (both new)
```
Only sole writable files; no merged file edited; no registry line added or removed; no frozen signature touched.

## 2. Statements against the binding pins (script check)
`pins.lean` = check-file imports + `import RBM3D.BA.SEforLnBA` + the check's Part 2 (lines 184-318, verbatim, incl. Amend 1's
`T2486_BACarrierFacts`) + the auditor examples below + one deliberately wrong pairing (negative control).
```
example (d : ℕ) : T2486_BAKcalDecay d := baKcalDecay_holds d
example (d : ℕ) : T2486_BAKcalDecay d = BAKcalDecay d := rfl
example (d : ℕ) : T2486_BAWardCls d := baZeroModeGen_wardCls d
example (d : ℕ) : T2486_BAOneLoop d := baKsol_oneLoop d
example (d : ℕ) : T2486_BACarrierFacts d := baStep2Mat_carrierFacts d
example (d : ℕ) : T2486_BACarrierFacts d := ⟨fun sz lam0 E => ⟨baStep34_LCompat d sz lam0 E, baStep34_KCompat d sz lam0 E⟩, baStep2Mat_loopForm d⟩
example (d : ℕ) : T2486_BAFlowFacts d := baStep5CasesGen_flowFacts d
example (d : ℕ) : T2486_BASEforLnFacts d := baSEforLnGen_facts d
example (d : ℕ) : T2486_BASEforLn d := baSEforLn_holds d
example (d : ℕ) : T2486_BASEforLn d = BASEforLn d := rfl
example (d : ℕ) : T2486_BAEtermDecay d := baEtermDecaygL d
example : <check's 4 (a) shape, verbatim> := fun d hd ... h2 => baSEforLnConclgL_of d hd ... h2
-- negative control
example (d : ℕ) : T2486_BAWardCls d := baKcalDecay_holds d
$ lake env lean scratchpad/T2486/pins.lean ; grep error
pins.lean:202:39: error: Type mismatch      <- line 202 is the negative control; every other example elaborates
$ lake env lean docs/tickets/checks/T2486-check.lean ; echo exit=$?     # the check file on the branch
exit=0   (0 error lines)
```
| target | Lean | vs pin |
|---|---|---|
| 1 `BAKcalDecay` / `baKcalDecay_holds` | `3 ≤ d → ∀ sz κ ε 𝔠 𝔡 z, 0<κ → BAFlow … → STKcalDecaygL (baFMz sz z)`, def is `rfl` to pin | exact |
| 2 (a) `baZeroModeGen_wardCls` | `ZeroModeGen_WardCls sz (baFMz sz z)` every `n`, under `0<κ`, `BAFlow` | exact |
| 2 (b) `baKsol_oneLoop` | first conjunct of `Step2IterGen_OneLoop`, eventually in `n`; `.1` of merged `baStep2_oneLoop` (T2487; no second proof, no named Prop) | exact |
| 2 (c) LCompat/KCompat | **unguarded, every `sz, lam0, E`** (Amend 1); LoopForm under the flow | exact |
| 2 (c) `baStep5CasesGen_flowFacts` | `Step5CasesGen_FlowFacts d BAFlow baFMz BAflowT0` | exact |
| 3 `baSEforLnGen_facts` | `SEforLnGen_Facts d` at the BA tuple, every `d` | exact |
| 4 (a) `baSEforLnConclgL_of` | head `STSEforLnConclgL`; hypotheses = the 1a shape (`0<κ, 0<ε`, flow, `0<Cd, 0<𝔠d, 𝔠d Cd ≤ 1/30`, times, `STConStInd`, `STStep2ConclgL`), same order | exact (shape) |
| 4 (b) `BASEforLn` / `baSEforLn_holds` | every `R`; def is `rfl` to pin; no hypotheses | exact |
| 5 `baEtermDecaygL` | the four conjuncts of `T2486_EtermDecay` inline; ε-free; `STDecayLoopUgL` the consumer's input | exact (defeq) |
No special case or conditional adapter passes for a general target: every binding target is the pin itself.

## 3. Hidden hypotheses, vacuity, cycles
- Hypotheses of the public theorems are only those in the pins/shape (table above); no structure field carries a premise
  (`BAFlow`, `baFMz`, `baStep2Mat`, `SEforLnGen_Facts`, `STKcalDecaygL` are merged defs; X1-C4 grep below: 0 new defs of the classes).
- Hypotheses left that are other gates' pins: `STStep2ConclgL` (4 (a); T1-BA, registered `Test/Axioms.lean`), `STDecayLoopUgL`
  (5; T7-BA's, the `hEK` input of the consumer). Unproved route `Prop` as a premise of 1, 2, 3, 4 (b), 5: none.
- `BAFlow` is satisfiable: merged `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`). No external hypothesis.
- No cycle: `SEforLnBA → KDecayBA`, both import only merged modules (`Step2IterBA` for `baStep2_oneLoop`, T2487 merged 268e07d4, H273 (3)).
```
$ grep -rn 'import RBM3D.BA.KDecayBA\|import RBM3D.BA.SEforLnBA' RBM3D RBM3D.lean
RBM3D/BA/SEforLnBA.lean:9:import RBM3D.BA.KDecayBA
RBM3D.lean:575:import RBM3D.BA.KDecayBA
RBM3D.lean:576:import RBM3D.BA.SEforLnBA
```

## 4. Compiled nonempty instances (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `κ = 1/2`)
In-file (all compile with the module build, §5):
```
KDecayBA:823  inst_baKcalDecay   : STKcalDecaygL (baFMz sz0 zSeq) := baKcalDecay_holds 3 le_rfl sz0 (1/2) (1/10) (1/6) (1/10) zSeq (by norm_num) flow_sz0
KDecayBA:875  inst_baKcalDecay_far : ∃ n, ellT (L n) (lam n) 0 * W^(1/20) ≤ KLmaxDist 3 (L n) (instA n) ∧ ‖(baFMz sz0 zSeq).K n 0 ![+,-,+] (instA n)‖ ≤ W^(-1)
SEforLnBA:314 inst_wardCls, :318 inst_oneLoop, :325 inst_carrierFacts (LCompat ∧ KCompat at BAflowLam0/BAflowEs; LoopForm under flow_sz0),
SEforLnBA:333 inst_flowFacts, :340 example := baSEforLnGen_facts 3 sz0 … flow_sz0,
SEforLnBA:344 inst_seforLnConclgL (hStep2 : STStep2ConclgL …) : s ≡ 1/10 < t ≡ 1/2, 𝔠d = 1/100, Cd = 1, STConStInd by s1Setup_conStInd_const,
SEforLnBA:354 inst_baSEforLn := baSEforLn_holds 3 STAny,
SEforLnBA:361 example (hU : STDecayLoopUgL …) := baEtermDecaygL 3 le_rfl sz0 … flow_sz0 (1/10) (1/2) … hU 3 (by norm_num) ![true,false,true]
```
Target 1's far set is nonempty at concrete data (`k = 3`, `τ = 1/20`, `u = 0`, labels at distance `3·2(n+1)`), so the instance is not
vacuous. Every deterministic premise (`3 ≤ d`, `0 < κ, ε`, `BAFlow`, windows, `𝔠d Cd ≤ 1/30`, `STConStInd`) is discharged; left are
only `STStep2ConclgL` (T1-BA) and `STDecayLoopUgL` (T7-BA).
Auditor supplement for 4 (b) (the in-file `inst_baSEforLn` stops at `R = STAny`; this applies the pin at `sz0` and compiles in `pins.lean`):
```
example : ∃ 𝔠d, 0 < 𝔠d ∧ (STLKgL … (fun _ => 1/10) → STStep2ConclgL … (fun _ => 1/10) (fun _ => 1/4) 1 → STSEforLnConclgL … (fun _ => 1/10) (fun _ => 1/4)) := by
  obtain ⟨𝔠d, h0, -, h⟩ := baSEforLn_holds 3 STAny le_rfl (1/2) (1/10) (1/10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos
  refine ⟨𝔠d, h0, fun hLK h2 => h (1/6) sz0 zSeq flow_sz0 _ _ … (fun n => le_trans (by norm_num) (TwistStep2_T0_ge … flow_sz0 n)) trivial
    (baKbound_holds 3 le_rfl … flow_sz0) (baKward_holds 3 le_rfl … flow_sz0) hLK (s1Setup_conStInd_const … h0) h2⟩
```
(left: `STLKgL` at the initial time, the induction input of the merged pin shape, and `STStep2ConclgL`, T1-BA).

## 5. Builds and axioms
```
$ lake build RBM3D.BA.KDecayBA RBM3D.BA.SEforLnBA 2>&1 | tail -1; echo exit=$?
Build completed successfully (4097 jobs).   exit=0     (no error lines; warnings only in merged files / linters)
$ lake build 2>&1 | grep -E 'axiom audit|Build completed|error' ; echo exit=$?     # full library, branch root imports
info: RBM3D.lean:579:0: axiom audit: 14559 theorems, 4549 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4347 jobs).   exit=0     (grep -c error: 0)
$ lake env lean scratchpad/T2486/ax.lean      # #print axioms
RBM.BA.baKcalDecay_holds / baZeroModeGen_wardCls / baKsol_oneLoop / baStep34_LCompat / baStep34_KCompat / baStep2Mat_loopForm /
baStep2Mat_carrierFacts / baStep5CasesGen_flowFacts / baSEforLnGen_facts / baSEforLnConclgL_of / baSEforLn_holds / baEtermDecaygL /
KDecayBAInst.inst_baKcalDecay / KDecayBAInst.inst_baKcalDecay_far / SEforLnBAInst.inst_seforLnConclgL:
  [propext, Classical.choice, Quot.sound]      (15 of 15)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/BA/KDecayBA.lean RBM3D/BA/SEforLnBA.lean
(no output)
```

## 6. Ticket greps (explicit file arguments; zsh does not split `$F`)
```
C1 '\|E\||norm_mE|mSigma|SB d|zt E|etaT|STFlow|STflowE|seqHflow [^B]|lemT'      -> (no output)
withLam outside 'seqP (sz.withLam 0)' / 'seqP (sz0.withLam 0)'                  -> SEforLnBA.lean:20 (module docstring `seqP ∘ withLam 0`; not a statement)
UBA-C1 'gK|≤ A \*' -> (no output);  TN-C4 STGridRepNgL -> (no output);  X1-C4 (def|abbrev|structure) <8 class names> -> (no output)
class (t) 'KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|KLK_two|KLnodes|TSP' -c            -> SEforLnBA.lean:0, KDecayBA.lean:18
name clash: git grep '^(private )?(theorem|def|abbrev|lemma) <name>' main (e6c26ca4) for the 14 public target names -> 0 each;
            namespaces KDecayBAInst / SEforLnBAInst on main -> 0  (the `inst_*` names live there, rule (E) by namespace)
```

## 7. Paper-delta coverage
Lean/paper differences in part (a), each proposed in the prove report (d): `T2486a` (BA far decay of `𝒦` for every charge vector via
the cactus with `M`-edges; paper proves only `lem_pureloop`, `A:643-660`); `T2486b` (`W^{-Q} ≤ g₀`, `Q = d/2`, only for `W ≥ W₀(κ,𝔡)`,
i.e. eventually); `T2486c` (cutoff at `ℓ_u(g)` while the proof runs at `ℓ_u(g₀) ≤ ℓ_u(g)`); `T2486d` (existential walk bound and crude
slot/factor counts instead of the diameter `2n-3`). The ε-free `STKboundgL` (target 5) and the `∀ᶠ n` of 2 (b) are the pins' own
texts (ticket notes (2), 2 (b)), not new deltas. Coverage complete.

## 8. Observations (no statement, instance, build, axiom or delta effect)
- O1. `inst_baSEforLn` instantiates 4 (b) only at `R = STAny`; the concrete-data application is supplied by §4's auditor example
  (compiles). A future in-file instance at `sz0` would make this self-contained.
- O2. `main` moved from `66b2ab97` to `e6c26ca4` after the branch was cut; both `RBM3D.lean` and `Test/Axioms.lean` changed on `main`
  since. The hub's merge takes the union of lines (ticket "Sibling scan") and reruns the full build.
- O3. Merged `BAKbound`/`baKbound_holds` carry an unused `0 < ε`; the private ε-free copy `SEforLnBA_Kbound` stays (ticket note (2)).

## 9. Verdict
| target | verdict |
|---|---|
| 1 `BAKcalDecay`, `baKcalDecay_holds` | PASS |
| 2 (a) `baZeroModeGen_wardCls` | PASS |
| 2 (b) `baKsol_oneLoop` | PASS |
| 2 (c) `baStep34_LCompat`, `baStep34_KCompat`, `baStep2Mat_loopForm`, `baStep2Mat_carrierFacts`, `baStep5CasesGen_flowFacts`; 3 `baSEforLnGen_facts` | PASS |
| 4 (a) `baSEforLnConclgL_of`; 4 (b) `BASEforLn`, `baSEforLn_holds` | PASS |
| 5 `baEtermDecaygL` | PASS |
**Overall: PASS for part (a) (targets 1-5) of T2486.** No dispatcher sign-off needed. Part (b) (targets 6-8, `t/T2486b`) not audited here.
