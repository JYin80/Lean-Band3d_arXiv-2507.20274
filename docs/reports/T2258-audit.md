Auditor model: claude-opus-5-5
# T2258 audit (round 1) — S3-12c2 uniform lift `stOeqNQ''_holds`
Date (`date -u`): Tue Oct  6 05:53:36 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2258-audit1` (detached at `7b379e5` = `t/T2258`; merge-base with `main` `9db01b0`). Ticket `docs/tickets/T2258.md`, check `docs/tickets/checks/T2258-check.lean`, prove report `docs/reports/T2258-prove.md` (line 1 `Prover model: claude-sonnet-5-5`).

## 1. Diff scope and hygiene
```
$ git diff --stat main...t/T2258
 RBM3D/Induction/NQEndFlowLift.lean | 1151 ++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean             |    1 -
$ git diff main...t/T2258 -- RBM3D/Test/Axioms.lean   (the only hunk)
-   `RBM.Gauss.Sizes.STOeqNQ'', -- `lem:STOeq_NQ`, R2* (DECISIONS §80): per-time form proved by T2246 (`stOeqNQPT''_holds`), lift S3-12c2
$ git diff main...t/T2258 -- RBM3D/Induction/NQEndFlow.lean RBM3D/Induction/ContinuityNet.lean RBM3D/Loop | wc -l
0
$ git diff --stat 9db01b0 main -- <NQEndFlow, ContinuityNet, LemDecCalELip, Loop/, Domination, StochDomAt, Step34Pins> | tail -1
(empty: no upstream drift since the branch base)
$ git merge-tree --write-tree --name-only main t/T2258   (main = 7672749)
1573aac8a53e02f53121b4c1fa07fb7d6aa346a4     exit 0 (clean merge)
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide|maxHeartbeats|^\s*(structure|class|instance)\b" NQEndFlowLift.lean | wc -l
0
$ grep -nE "^(theorem|lemma|def|noncomputable def|abbrev)" NQEndFlowLift.lean     (public declarations)
68:noncomputable def nqFlowSharp ...      581:theorem stKloop_lip ...
939:theorem stOeqNQ''_holds : ∀ d : ℕ, STOeqNQ'' d := by     974:theorem inst_OeqNQ'' : InstIngConcl ...
```
Only the two sole writable files; exactly the one owed registry line deleted; no merged/frozen signature touched; every other helper is `private` with prefix `nqLift_` (§3 (E)); no new structure/class (no hidden field).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.NQEndFlowLift; echo exit $?
info: RBM3D/Induction/NQEndFlowLift.lean:1150:0: 'RBM.Ind.stOeqNQ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/NQEndFlowLift.lean:1151:0: 'RBM.Ind.NQEndFlowLiftInst.inst_OeqNQ''' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3854 jobs).
exit 0
$ lake env lean RBM3D/Induction/NQEndFlowLift.lean   (fresh elaboration, not replayed); echo exit $?
exit 0
'RBM.Ind.nqFlowSharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stKloop_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stOeqNQ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.NQEndFlowLiftInst.inst_OeqNQ''' depends on axioms: [propext, Classical.choice, Quot.sound]
(0 warnings, 0 errors)
```

## 3. Statements against the pins (script)
Statement script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2258/stmt.lean` = check file header/§2/§3 (the `#check` lines dropped) + `import RBM3D.Induction.NQEndFlowLift` + the lines below, run with `lake env lean` in the audit worktree:
```
example : T2258_stKloop_lip := @RBM.Gauss.Sizes.stKloop_lip
example : T2258_stOeqNQ''_holds := @RBM.Ind.stOeqNQ''_holds
example : RBM.Ind.nqFlowSharp = nqFlowSharp := rfl
--- output ---
'RBM.Gauss.Sizes.stKloop_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stOeqNQ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.nqFlowSharp' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Private targets (not referable from outside the file): whitespace-normalised text diff of each pin in check §3 against the in-file `example : <stmt> := @<name>` (which compiles, §2):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2258/diff.py
T2258_sharp_one_le       vs in-file example @nqLift_sharp_one_le : IDENTICAL
T2258_sharp_le           vs in-file example @nqLift_sharp_le     : IDENTICAL
T2258_sharp_mono         vs in-file example @nqLift_sharp_mono   : IDENTICAL
T2258_sharp_prec         vs in-file example @nqLift_sharp_prec   : IDENTICAL
T2258_bootRHS_mono       vs in-file example @nqLift_bootRHS_mono : IDENTICAL
T2258_netPt_floor        vs in-file example @nqLift_netPt_floor  : IDENTICAL
T2258_core_below         vs in-file example @nqLift_core_below   : IDENTICAL
T2258_stKloop_lip        vs in-file example @stKloop_lip         : IDENTICAL
T2258_stOeqNQ''_holds    vs in-file example @stOeqNQ''_holds     : DIFF
nqFlowSharp def text (check §2 vs file): IDENTICAL
```
The one DIFF is a parser artefact (the pin `def T2258_stOeqNQ''_holds : Prop := ∀ d : ℕ, STOeqNQ'' d` is on one line and the regex wants a line break); the type is checked by Lean above (`example : T2258_stOeqNQ''_holds := @RBM.Ind.stOeqNQ''_holds`, exit 0).

Mathematics. `STOeqNQ''` (merged `NQEndFlow.lean:124`, unchanged) is the R2* form of `lem:STOeq_NQ` (`3_5:1136-1150`, bound `(am;asoiuw)`, uniform in `u ∈ [s,t]`, `B_s` in the second summand per DECISIONS §80). The target proves the pin itself (`∀ d`, the `∃ 𝔠d` taken from `stOeqNQPT''_holds d` at the same `(κ, ε, 𝔡, C_d)`, `:941-942`), not a special case or conditional adapter: the per-time pin is an internal *proved* input (merged T2246), not a hypothesis. `stKloop_lip`: `κ, gmax` before `∀ᶠ n`, all `k ≥ 2`, all labels, Lipschitz constant `N^{2k+2}` as pinned; its extra deterministic premises (`SizeTendsto`, `|E| ≤ 2-κ`, `0<lam≤gmax`, `t<1`, `(1-t)⁻¹ ≤ N` eventually) are binders of the signature, not hidden.

## 4. Vacuity, hidden hypotheses, cycles
- Dependencies (all merged on `main`, no cycle: the new module imports only merged modules, never `RBM3D`): `stOeqNQPT''_holds` (`:941`), `v3_premises_of_stFlow` (`:945`), `LemDecCalELip_env` (`LemDecCalELip.lean:751`), `cont_highProbAt_good`, `stochDomAt_of_perTimeDomAt`, `KLK_isKLoop`, `KLbound_holds`, `card_net_le` (uses type-checked by Lean, §2).
- No new external hypothesis; no structure field. Registry pre-check (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2258/reg.lean`: `import RBM3D` + `import RBM3D.Induction.NQEndFlowLift` + `#assert_rbm_axioms`, after `lake build RBM3D.Test.Axioms` on the branch registry):
```
$ lake env lean reg.lean; echo exit $?
exit 0
axiom audit: 7598 theorems, 2548 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 150 (borrowed 1, owed 95, structural 37, refuted 6, superseded 11).
registry: 2 borrowed + 157 owed + 98 structural + 7 refuted + 12 superseded; 126 registered premise(s) carry nothing yet: [...]
$ grep -c "STOeqNQ''" reg.log
0
```
(`import RBM3D` here loads the copied `main` cache at 7672749, hence counts differ from the prove report's `9db01b0` base; `owed` 157 agrees with its "after" run.) No unregistered premise; `STOeqNQ''` no longer owed, concluded by `stOeqNQ''_holds`.

## 5. Compiled nonempty instances (all in the file, compiled in §2)
| Endpoint | Instance | Data / discharged hypotheses | Verdict |
|---|---|---|---|
| `stOeqNQ''_holds` | `inst_OeqNQ''` (`:974`) via `inst_ing … (stOeqNQ''_holds 3) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos`; applied `example` `:983-999` at `n_=3, p=1, XL≡XLK≡1` | `d=3`, `sz0` (`n=0`: `L=4, W=32, N=2^21`), window `[0,1/16]`; `STKbound`/`STKward` discharged by `stKbound_of_flow`/`stKward_of_flow`; kept as hypotheses: `STLK`, `STStep2Concl`, pair `Ξ̂ ≺ 1` (other gates' pins, allowed by ticket/§4) | nondegenerate |
| `stKloop_lip` | `example` `:1058-1070` | `sz0`, `E = STflowE z0`, `t ≡ 1/16`, `k=3`, `κ=1/20`, `gmax=10`; `sz0_tendsto`, `hE'` from `v3_premises_of_stFlow`, `nqLift_flowLam`, `(1-1/16)⁻¹ = 16/15 ≤ N` all discharged | nondegenerate |
| `nqLift_core_below` | `example` `:1075-1098` | `sz0.seqP`, window `[0,1/16]`, `V=Fin 2`, `ξ=u`, `ζ≡1`, `A=Cv=1`, `Ξ=contGood sz0`, `ε≡1`; every hypothesis discharged | nondegenerate |
| envelope lemmas, `nqFlowSharp` | `:1004-1053` | `X≡1 ⇒ X♯≡1`; `X=2+u`: `X♯(0)=2`, `X♯(1)=1` (check §4); `X=2+|u|`: `le`, `mono` (`0 ≤ 1/32`), `prec` at the deterministic `w ≺ 2+|u|` (`prec_of_le`) | nondegenerate |
| `netPt_floor`, `bootRHS_mono` | `:1102-1109` | `A=1, N=4, x=1/2`; `B=1/2, n_=3, p=1`, controls `1 ≤ 2,3` | nondegenerate |
No `N=0`, empty index, collapsed window, `False` premise or astronomically large witness.

## 6. Paper deltas
Prove report (d) proposes `T2258a` (uniform-in-`u` form of `(am;asoiuw)` from the per-time one by a one-sided net on the monotone envelope; paper net remark commented out at `3_5:1182`, also `:1764`) and `T2258b` (deterministic Lipschitz time modulus of `𝒦^{(k)}`, `N^{2k+2}`, not stated in the paper). These are the two Lean/paper differences introduced by this ticket; the statement of `STOeqNQ''` itself is merged and unchanged (its deltas belong to §80/T2246). Coverage complete.

## 7. Observations (no verdict effect)
- The prove report's b1 build log shows "Replayed"; this audit re-elaborated the file from source (§2, exit 0).
- File length 1151 lines vs ticket central estimate 850 (below the 1500 stop threshold).

## Verdict per target
| Target | Verdict |
|---|---|
| 1 `nqFlowSharp` (verbatim) | PASS |
| 2 `nqLift_sharp_one_le/le/mono/prec` | PASS |
| 3 `nqLift_bootRHS_mono` (+ `ζ♯` monotone, `≤ ζ`, `≥ 1`) | PASS |
| 4 `nqLift_netPt_floor`, `nqLift_core_below` | PASS |
| 5 `RBM.Gauss.Sizes.stKloop_lip` | PASS |
| 6 `ξ` modulus / flow facts (private, consumed by 7) | PASS |
| 7 `RBM.Ind.stOeqNQ''_holds : ∀ d, STOeqNQ'' d` | PASS |
| Registry (one owed line deleted, no new premise) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
