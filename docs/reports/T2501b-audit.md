Auditor model: claude-opus-5-5
# T2501 row b audit (round 1), branch `t/T2501b` @ df731125, base db1932eb; written Wed Oct 14 03:56 UTC 2026 (`date -u`)

Judged against `docs/tickets/T2501.md` row b (targets 9-12) as amended by `T2501-amend-1.md` (private instance data allowed, fallback, stop line 900).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2501b-audit1` (detached at df731125). Scratch files in the scratchpad `T2501b/` (uncommitted).

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2501b
 RBM3D.lean                 |   1 +
 RBM3D/BA/Step5CasesBA.lean | 556 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   9 +-
$ git diff --stat db1932eb main      # main drift since base: docs only
 docs/DECISIONS.md | docs/ROUTES.md | docs/claude-team/WORKLOG.md | docs/paper-deltas.md | docs/queue/CONTROL.md | REQ-...-Vopen.md | docs/tickets/T2501-amend-1.md
$ grep -rln "import RBM3D.BA.Step5CasesBA" RBM3D RBM3D.lean
RBM3D.lean
```
`RBM3D.lean`: one line `+import RBM3D.BA.Step5CasesBA` after `import RBM3D.BA.CltFlowBA` (before `#assert_rbm_axioms`). `Test/Axioms.lean`: the five owedProps lines `STEtermsMidgL`, `STDuhamelIgL`, `STDuhamelIIgL`, `STIniTermIgL`, `STIniTermIIgL` deleted; T2462 header comment gains "… left this list (… BA: T2501)"; `STStep5ConclgL` stays with owner text "BA: the conclusions of `baStep5I_holds`, `baStep5II_holds`, `baStep5IV_holds` (T2501) and `baStep5III_holds` (T2499); reader V" — exactly the ticket's Registry paragraph. No merged `BA/*`, `Chain/*`, `Induction/*`, `Evolution/*` file touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.Step5CasesBA | grep -E 'error|sorry|Build completed'      (03:52:40-03:52:50 UTC; olean rewritten 03:52 UTC)
Build completed successfully (4214 jobs).
$ lake build 2>&1 | grep -E "error|registry:|axiom audit|Build completed"         (03:54:36-03:55:40 UTC)
info: RBM3D.lean:611:0: axiom audit: 14993 theorems, 4631 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 109 owed + 123 structural + 7 refuted + 18 superseded; 137 registered premise(s) carry nothing yet: [...
Build completed successfully (4381 jobs).
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/BA/Step5CasesBA.lean
(0 hits)
```
Axioms (scratch `pins.lean` = `docs/tickets/checks/T2501-check.lean` + `import RBM3D.BA.Step5CasesBA` + the pin examples of §3 + `#print axioms`; `lake env lean` exit 0, 0 error lines):
```
'RBM.BA.step5CasesGen_wardIdent_of_wardCls' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5CasesGen_wardIdent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTEtermsMidgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTDuhamelIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTDuhamelIIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIniTermIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTIniTermIIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTWardIIgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5I_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pins (compiled by Lean; definitional equality, no unfolding by hand)
Appended to the copy of the check (namespace `RBM.BA`); all elaborate (exit 0, 0 errors):
```
example : T2501_WardIdentBA := fun d => baStep5CasesGen_wardIdent d
example : <the check's bridge shape, :323-328, verbatim> := fun sz C h hc => step5CasesGen_wardIdent_of_wardCls sz C h hc
example : T2501_EtermsMidBA := baSTEtermsMidgL_holds        example : T2501_DuhamelIBA := baSTDuhamelIgL_holds
example : T2501_DuhamelIIBA := baSTDuhamelIIgL_holds        example : T2501_IniTermIBA := baSTIniTermIgL_holds
example : T2501_IniTermIIBA := baSTIniTermIIgL_holds        example : T2501_WardIIBA := baSTWardIIgL_holds
example : T2501_Step5IBA := baStep5I_holds                  example : T2501_Step5IIBA := baStep5II_holds
example : T2501_Step5IVBA := baStep5IV_holds
```
Each target is an exact term of its pin (`∀ d, 3 ≤ d →` the merged generic pin at the BA tuple `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; case (iv) every `d`, as pinned). The quantifier order, `∃ 𝔠d` placement, regimes and `Cd` are those of the merged `STIngR5gL` (`Chain/Step5Gen.lean:191-211`), not restated. The bridge's inline conjugation hypothesis `hc` is the check's shape verbatim (1852 `:77-80`); no named `Prop` added.
Target 9 vs paper: `Step5CasesGen_WardIdent` (`Step5CasesGen.lean:187-194`) is the first equality of `(zYU1)` (`3_5:2258-2261`): `(L−K)^{(2)}_{σ,a} − [Q^{(1)}∘(L−K)^{(2)}_σ]_a = Im (L−K)^{(1)}_{+,a_2}/(N η)`, `a_2 = a 1`. The bridge needs no `η ≠ 0` (case split at line 119; `x/0 = 0` both sides).

## 4. Hidden hypotheses, vacuity, cycles
- Every public target's hypotheses are in its signature: targets 10-11 have none beyond `3 ≤ d`; `baStep5CasesGen_wardIdent` has `0 < κ`, `BAFlow`; the bridge has `ZeroModeGen_WardCls sz C` (merged class, `ZeroModeGen.lean:289-295`, a Prop, no structure) and `hc`. No new structure/class.
- Discharges (read in the source, lines 128-262): Ward class `baZeroModeGen_wardCls` (U2-BA); `𝓛` conjugation conjunct `.2` of `baStep2_oneLoop` (every `n u a ω`); `𝒦` conjugation clause 3 of `IsKLoopS` via `open private SEforLnBA_Ksol_isKLoopS` from `BAflow_real` (every `n`, no `0 < g₀`; conjunct 1 of `baStep2_oneLoop`/`baKsol_one` not used, per ticket stop rule (8)); target 10 uses exactly the family table rows 1-12 (row a1/a2 producers `baIniTermGen_kerFacts`, `baIniTermGen_cltFlow`, `baEtermsMid_newKLKL`, `baLemDecCalELipG_flowMod`, `baKLip_two`; `baEMn2Hf`, `baEMn2Zf`, `stLWTgL_of_LWtermExpG`+`Step2EventsGenTw_baRot3`+`baLWtermExp_holds`, `baSTBdatagL_holds`, `baStep2_K2`, `gridRepTailGen_ker_BA`, `baGridMart_holds`, `Step2EventsGenTw_baGrid`, `baStep2Mat_Hpath_herm`, `baStep2Mat_loopForm`, private `hmn`/`hSr` copies).
- All dependencies are merged on main (imports lines 6-14, all pre-existing modules; the full build above links them). New leaf: no importer but `RBM3D.lean`, so no cycle. No external input.
Hypothesis-rule greps on `RBM3D/BA/Step5CasesBA.lean`:
```
C1   grep -nE 'BAK_le_small|BAMB_upper_small|Mbound_AO|W\^\(-eps|BAm_im_lower_window|\|E\||norm_mE|mSigma|SB d|E2Hyp|STGridRepNgL'  -> (0 hits)
X1-C4 grep -nE '^(noncomputable )?(def|abbrev|structure) '   -> (0 hits)
T24  grep -nE 'T24[0-9]*_'                                   -> (0 hits)
withLam outside `seqP (`:  grep -n withLam F | grep -v 'seqP ('  -> (0 hits)
private defs (Amend 1 item 1): lines 278, 285, 288, 391, 407, 428-433 (Step5CasesBA_sz/_w/_z/_Datum/_prem/_szI.._zIV), all `private`
public decls: 11 theorems (lines 83,128,179,194,208,223,230,236,248,254,260); name clash outside the file: 0 each
```

## 5. Compiled nonempty instances (target 12), `d = 3`
`grep -n '^example'`: 472, 476 (target 9), 490 (case iv), 497/502/509/514 (EtermsMid, DuhamelI, IniTermI, case i), 521/526/535/542/547 (EtermsMid, DuhamelII, IniTermII, WardII, case ii). All compile (module build §2).
- Target 9 (`baStep5CasesGen_wardIdent`, and through it the bridge with both hypotheses discharged): at the merged `(sz0, zSeq, flow_sz0)`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, as a class and at `n = 0`, `u = 1/2`, `σ = ![true,false]`, `a = 0`, every `ω`. No hypothesis left.
- Targets 10-11: private data `Step5CasesBA_sz L W₀ lam` (`L_n ≡ L`, `W_n = n + W₀`, `lam_n ≡ lam`), `z_n ≡ w − BAmSubord 3 L lam w`, `w = (5003/5000)i`, `(ε,𝔠,𝔡) = (1/2,1/9,1/10)`, `s ≡ 0`. `BAFlow`, `0 < κ`, `0 ≤ s`, `s < t`, `t ≤ BAflowT0` (via `TwistStep2_T0_ge`), the regime and `STConStInd` at every `𝔠d > 0` are proved (`Step5CasesBA_datum`, `_regI/_regMidI/_regII/_regMidII/_regIV`). Only hypothesis: `hp : Step5CasesBA_prem` = the nine carrier predicates of `STIngR5gL` (`STKboundgL, STKwardgL, STLKgL, STDecaygL, STDecayStronggL, STStep1LoopgL, STStep2ConclgL (Cd = 1), STLmaxUgL, STLKUgL`), as target 12 / Amend 1 item 3 allow.
Numbers re-checked by script:
```
$ python3 -I T2501b/inst.py
I hκ: True 0<t<=κ/(κ+1): True {'L_le_W0': True, 'WL_ge_100': True, 'lam_in_1_10': True, 'k_ge_3e4': True} regime: (True, True) Mid: True s<t: True 1-t= 0.99
II hκ: True 0<t<=κ/(κ+1): True {'L_le_W0': True, 'WL_ge_100': True, 'lam_in_1_10': True, 'k_ge_3e4': True} regime: (True, True) Mid: True s<t: True 1-t= 0.9991
IV hκ: True 0<t<=κ/(κ+1): True {'L_le_W0': True, 'WL_ge_100': True, 'lam_in_1_10': True, 'k_ge_3e4': True} regime: (True,) Mid: None s<t: True 1-t= 0.9995
```
(i) `(L,W₀,lam,κ,t) = (4,25,1,1/70,1/100)`: `1/16 ≤ 0.99`, `1 ≤ 1`; (ii) `(4,25,4,1/1100,9/10000)`: `1/4 ≤ 0.9991`, `1 ≤ 1`; (iv) `(3,40,6,1/1000,1/2000)`: `1 ≤ 4/3`. Nondegenerate: `N_n = ((n+W₀)L)^3 → ∞`, `s < t` strict, windows nonempty, no `False` premise, no astronomically large witness (`W₀ ≤ 40`). The paper fixes any `λ > 0` for BA (`7_8:1797`), so constant `lam ∈ [1, 6]` is in scope.

## 6. Paper deltas
Targets 10-11 are the merged generic pins at the BA tuple; target 9 is `(zYU1)`'s first equality (§3). No Lean/paper statement difference introduced by row b; the prove report proposes none (`T2501b-prove.md` (d)); `docs/paper-deltas.md` on main records D721 (row a1) and "no new candidate" for a2. Coverage: complete.

## 7. Verdicts
| target | verdict |
|---|---|
| 9 `step5CasesGen_wardIdent_of_wardCls`, `baStep5CasesGen_wardIdent` | PASS |
| 10 six ingredient pins | PASS |
| 11 `baStep5I_holds`, `baStep5II_holds`, `baStep5IV_holds` | PASS |
| 12 instances | PASS |
**Overall: PASS.** No dispatcher sign-off needed.

## 8. Observations (no RETURN)
- O1. The ticket text says case (iv)'s instance has "every premise discharged"; the example keeps the nine carrier predicates. They are not deterministic: `stStep5IVgL_holds` reads `hLKU` (`Chain/Step5CasesGen.lean:307`, `hLKU 2`), so they cannot be dropped at concrete data; CLAUDE.md §4 step 2 and Amend 1 item 3 allow other gates' pins as hypotheses. Read as T2499 does.
- O2. The ticket's instance hint (`(sz0, zSeq)`, regime from `half_lt_t0`) gives an empty regime (prove report (a) Finding 1); superseded by Amend 1 (private data), which the branch follows. Data + shared flow proof: lines 277-463 for three data (flow proof 297-372 shared), within Amend 1's 120 lines per datum; file 556 lines < stop line 900.
- O3. Prove report is 235 lines (CLAUDE.md §6 limit 300; ticket acceptance asks ≤ 150). Report-only; changes no statement, instance, build or axiom.
- O4. The bridge's instance is through its BA composition (both hypotheses discharged at `(sz0, zSeq)`), not a separate `example`; accepted.
- O5. `RBM3D.lean` and `Test/Axioms.lean` are a union with T2498 row a at merge (hub's full build decides).
