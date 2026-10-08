Auditor model: claude-opus-5-5
# T2319 audit (round 2, after the round-1 repair) — written Thu Oct  8 09:23:20 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2319-audit2`, detached at `t/T2319` = `6cbecb2` (round-1 repair on top of `0ed1177`;
the hub's task text named `0ed1177`, but the branch tip is `6cbecb2`, which is what is audited). Scratch: `scratchpad/…/T2319/`.

## Verdict
| target | verdict |
|---|---|
| `cert_all'` (`LWExpCertBS1.lean:583`), with the pinned `belowOf'` (`LWExpCertB.lean:40`) | PASS |
| `cert_FF'` (`BS0:545`), `cert_FT'` (`BS1:563`), `goodB'_succ_of` (`B:101`), instances (1)-(7) | PASS |
Overall: **PASS**. Round-1 defect (`goodB_succ_of'` vs the pinned `goodB'_succ_of`) is repaired. No dispatcher sign-off needed.

## 1. Statement
```
$ sed -n '26,63p' docs/tickets/T2319.md > pin.txt; awk 'NR>=35 && NR<=72' RBM3D/Graph/LWExpCertB.lean > file.txt; diff pin.txt file.txt && echo PIN_IDENTICAL
PIN_IDENTICAL
$ diff <(tr -d "'" < RBM3D/Graph/LWExpCertB.lean) <(git show main:RBM3D/Graph/LWExpCert.lean | sed -n '152,215p;226,282p' | tr -d "'") | grep -E '^[0-9]'
1,34d0
45c11
99,100d64
158,243d121
$ … | sed -n '/^45c11/,/^99/p'
<   let X0 : List (ℕ × ℕ) := (Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)   -- T2319: was `Δ.dotted` (T2306); `withDots` keeps `dotBase` only
>   let X0 : List (ℕ × ℕ) := (Δ.dotted.filter fun e => !e.eq).map (pairOf a b)
```
`1,34` header/imports/options/`open`/namespace; `99,100` docstring + blank line; `158-243` split helpers, diagnostic, instances (5)-(7), `#print axioms`.
Since `tr -d "'"` hides misplaced primes (the round-1 defect), prime placement checked separately:
```
$ declared theorem names of BS0/BS1 (minus chc_/chd_) vs T2306's S0/S1 names with "'" appended
S0: NAMES_EQ_PRIMED     S1: NAMES_EQ_PRIMED
$ unprimed references to goodB|rootAt|kid|kids|kidsOk|rootInfo|belowOf|childrenB|cert_F?|cert_all|goodB_succ_of|root_F?_i|chs_|ch_ (followed by non-"'")
BS0: (none)   BS1: (none)   B: belowOf (lwCertB_cex_bites, pinned), rootInfo (lwCertB_root_eq, pinned), 2 in docstrings
$ grep -c "goodB_succ_of'" B BS0 BS1
0 / 0 / 0
```
Normalized diff of the chunk files (python: primes removed, `chc_`/`chd_` blocks dropped, each `ch_F?_i_j_l` reduced to its statement):
```
$ diff <(norm.py LWExpCertBS0.lean) <(norm.py main:LWExpCertS0.lean)
6c6   < import RBM3D.Graph.LWExpCertB              > import RBM3D.Graph.LWExpCert
9c9   < # LW-14e-1: … `LWG5Graph false false` with the corrected flag (chunks)   > … (chunks)
11d10 < `LWExpCertS0.lean` (T2306) with the primed names of `LWExpCertB` (…)
$ diff <(norm.py LWExpCertBS1.lean) <(norm.py main:LWExpCertS1.lean)
6,7c6,7 imports (LWExpCertB, LWExpCertBS0 vs LWExpCert, LWExpCertS0); 10c10, 12c12 module docstring only
$ counts per file: ch_ / chs_ / root_F?_i' / chc_ / chd_
S0 ch_: 78 chs_: 6 root_: 11 chc_: 231 chd_: 36
S1 ch_: 78 chs_: 6 root_: 11 chc_: 246 chd_: 40
$ grep -cE "^theorem ch[cd]_.*:= by decide \+kernel$"     267 (S0) / 286 (S1)   (= 231+36, 246+40)
```
So every `ch_`, `chs_`, `root_F?_i'`, `cert_F?'`, `cert_all'` statement is T2306's with primes; the Route 4 split (applied: prover's heaviest
chunk 51.16 s / 11.89 GB > 8 GB) changes only proofs of the `ch_` theorems; the 36 / 40 depth-2 nodes match the ticket. Sample (`BS0:338-344`):
`ch_FF_10_0_8' : goodB' 2 (kid' (rootAt' false false 10) 0 8) = true := lwcertB_two _ 4 (by decide +kernel) (by omega) (fun c hc => by interval_cases c; exacts [lwcertB_nokids _ _ chc_FF_10_0_8_0, lwcertB_onekid _ _ chc_FF_10_0_8_1 chd_FF_10_0_8_1_0, …])`.
Target statement (`BS1:583`): `theorem cert_all' : ∀ s, (rootInfo' false s).1 = true ∧ (rootInfo' false s).2.all (goodB' 3) = true` = ticket :24 verbatim.

## 2. Vacuity, hidden hypotheses, cycles
`cert_all'`, `cert_FF'`, `cert_FT'` are closed `Bool` equalities about one finite tree at the concrete root `LWG5Graph false s`: no hypotheses,
no structure fields. `goodB'_succ_of`'s hypotheses are the explicit assembly premises (T2306's `goodB_succ_of`, primed). The one new `Prop`
def `lwcertB_candGood` (`B:166`) is a conjunction used as the conclusion of `lwcertB_nokids/onekid` and as the premise of `lwcertB_two`,
always discharged by `decide +kernel` facts; no theorem leaves it open. Imports: `B ← LWExpCert`; `BS0 ← B`; `BS1 ← B, BS0` (no
`LWExpCertS0/S1`, `Probe`, or `RBM3D`); no cycle. No external hypothesis.

## 3. Compiled nonempty instances (`LWExpCertB.lean`, all `decide +kernel` at the real tree or at T2318's counterexample)
(1) `inner_node_one'` :134 (applies `goodB'_succ_of` at `rootAt' false false 0`, 2 candidates); (2) `lwCert_root0_nonleaf'` :147;
(3) `lwCert_roots_below'` :154; (4) `root_FF_shape'`, `root_FT_shape'` :142-143 (11 terms); (5) `lwCertB_lost_R2 = 5`, `lwCertB_lost_R8 = 36`
:212-213 (> 0: the change bites in the tree); (6) `lwCertB_cex_bites` :216 (1 / 2 / 1); (7) `lwCertB_root_eq` :223. Values = ticket :102.
Target applied in a scratch file (also every `#check @RBM.Graph.LWCert.*` line of the consumer's `docs/tickets/checks/T2318-check.lean`):
```
$ cat ex2.lean   (43 lines)
import RBM3D.Graph.LWExpSim
import RBM3D.Graph.LWExpCertBS1
open RBM.Graph.LWCert
example : ∀ s, (rootInfo' false s).1 = true ∧ (rootInfo' false s).2.all (goodB' 3) = true := cert_all'
example : (rootInfo' false true).1 = true ∧ (rootInfo' false true).2.all (goodB' 3) = true := cert_all' true
#check @RBM.Graph.LWCert.MNode … #check @RBM.Graph.LWCert.goodB'_succ_of … #check @RBM.Graph.LWCert.Cand.toR   (34 lines, from T2318-check.lean)
#print axioms cert_all' / cert_FF' / cert_FT' / goodB'_succ_of
$ lake env lean ex2.lean            (Thu Oct  8 09:21:57 UTC 2026, after BS1)
exit 0      error lines: 0
goodB'_succ_of : ∀ (n : ℕ) (N : MNode) (nc : ℕ),
  (cands N.g).length = nc →
'RBM.Graph.LWCert.cert_all'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWCert.cert_FF'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWCert.cert_FT'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWCert.goodB'_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Not degenerate: no `N = 0` node, no empty candidate list, no `False` premise; `lwCertB_cex` is degenerate by design (ticket (6)).

## 4. Build and axioms (H101/H118: one module per `lake build`, nothing else running, 30 s `ps` monitor)
```
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertB          08:26:29-08:26:38 UTC   (no LWExpCertB* .olean in the cloned cache: fresh)
Build completed successfully (3883 jobs).   8.45 real  6.55 user   3837902848 maximum resident set size   exit 0
info: RBM3D/Graph/LWExpCertB.lean:229:0: 'RBM.Graph.LWCert.goodB'_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound]
  :230-241 inner_node_one', root_FF_shape', root_FT_shape', lwCert_root0_nonleaf', lwCert_roots_below', lwcertB_nokids, lwcertB_onekid,
  lwcertB_two, lwCertB_lost_R2, lwCertB_lost_R8, lwCertB_cex_bites, lwCertB_root_eq: each "depends on axioms: [propext, Classical.choice, Quot.sound]"
$ BS0 pre: other lean/lake procs before: 0 ; vm_stat free+inactive+spec+purgeable GB: 11.4 ; Swapouts 36585306 ; memory free 63% ; 08:26:57 UTC
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertBS0        08:26:57-08:52:12 UTC
Build completed successfully (3884 jobs).
     1514.76 real      1471.04 user        57.22 sys
          6096748544  maximum resident set size
exit 0   Swapouts after: 36585306 (+0)
info: RBM3D/Graph/LWExpCertBS0.lean:564:0: 'RBM.Graph.LWCert.cert_FF'' depends on axioms: [propext, Classical.choice, Quot.sound]
$ BS1 pre: other lean/lake procs before: 0 ; vm_stat free+inactive+spec+purgeable GB: 11.3 ; Swapouts 36585306 ; memory free 63% ; 08:52:53 UTC
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertBS1        08:52:53-09:21:40 UTC
Build completed successfully (3885 jobs).
     1726.30 real      1671.85 user        67.54 sys
          6133628928  maximum resident set size
exit 0   Swapouts after: 36585306 (+0)
info: RBM3D/Graph/LWExpCertBS1.lean:594:0: 'RBM.Graph.LWCert.cert_FT'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Graph/LWExpCertBS1.lean:595:0: 'RBM.Graph.LWCert.cert_all'' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE "ofReduceBool|trustCompiler|sorryAx|error:" B.log BS0.log BS1.log       0 / 0 / 0
$ monitor: lake/lean processes other than my own build PIDs during BS0 / BS1      0 / 0
```
vm_stat's reclaimable total was 11.3-11.4 GB (< 12 GB) before each certificate build, but no build was running, so there was nothing to
wait for (H118); neither build swapped (Swapouts +0), was killed, or was retried. Both are under the ticket limits (30 min, 8 GB):
BS0 25.2 min / 6.10 GB, BS1 28.8 min / 6.13 GB (prover 1469 s / 6.26 GB, 1770 s / 6.38 GB; repairer 1588 s, 1723 s).
```
$ grep -nE "sorry|admit|^axiom|native_decide|maxHeartbeats" RBM3D/Graph/LWExpCertB*.lean
(no output)
$ git diff main...t/T2319 --name-only   (frozen LWExpCert, LWExpCertS0/S1, LWExpSim: `git diff --stat` empty)
RBM3D/Graph/LWExpCertB.lean
RBM3D/Graph/LWExpCertBS0.lean
RBM3D/Graph/LWExpCertBS1.lean
$ lake build RBM3D.Test.Axioms; printf 'import RBM3D\nimport RBM3D.Graph.LWExpCertBS1\n#assert_rbm_axioms\n' > registry2.lean; lake env lean registry2.lean
exit 0
axiom audit: 9896 theorems, 2971 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: …
$ grep -cE "LWExpCertB|belowOf'|lwcertB_candGood|cert_all'|error" registry2.out
0
```
Name clashes (declarations outside `RBM3D/Graph/LWExpCertB*.lean`, `RBM3D/` tree):
```
belowOf':0 childrenB':0 goodB':0 rootInfo':0 rootAt':0 kids':0 kidsOk':0 kid':0 goodB'_succ_of:0 cert_all':0 cert_FF':0 cert_FT':0
lostOf:0 lostAt:0 lwCertB_cex:0 lwcertB_candGood:0 lwcertB_nokids:0 lwcertB_onekid:0 lwcertB_two:0 ; "LWExpCertB" in RBM3D.lean/RBM3D/: 0
```

## 5. Paper deltas
No new Lean/paper statement difference: the corrected flag follows `dot-def` (`7_8:217-218`, the b-edge rewrite `1_{α≠β} = 1 − 1_{α=β}`);
the kernel certificate ("verified by inspecting", `B:98`) is covered by the existing entry:
```
$ grep -n "T2288" docs/paper-deltas.md | cut -c1-60
1571:- **D612（T2288a–e）**：见 §107 (3)：`(eq:GGraisesord)`（`B:98-100`）…
```

## Observations (no RETURN)
- O1. Split helpers `lwcertB_candGood/nokids/onekid/two` are public with prefix `lwcertB_` rather than the literal file stem
  `LWExpCertB` (§3 (E)); 0 clashes. Optional rename or `private`.
- O2. The ticket says "no `Prop` definition"; `lwcertB_candGood : Prop` is a proof helper, not an interface hypothesis; registry lists nothing.
- O3. BS1 margin: 73.7 s under the 30 min limit in this run; a busier machine at merge could exceed it (prove report (d) raises it).
- O4. Prove report (b)-(c) still name `goodB_succ_of'` (commit `0ed1177`; its Repair section says so). O5. Long-line linter warnings in docstrings.
