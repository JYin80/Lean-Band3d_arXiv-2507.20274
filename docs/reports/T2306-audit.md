Auditor model: claude-opus-5-5

# T2306 audit (round 1) — LW-14e-1 `Graph/LWExpCert`, `LWExpCertS0`, `LWExpCertS1`

Written Wed Oct  7 06:27:52 UTC 2026 (`date -u`).  `t/T2306` at 533adf0 (merge-base 4db5994; main 1d19466); worktree `RBM3D-wt/T2306-audit1`.

**Verdict: PASS** (target `cert_all` with `cert_FF`, `cert_FT`, `goodB_succ_of`, `inner_node_one`, `root_F?_shape`, instances (2)-(3)).

## 1. Statement against the ticket's pin / the probe at 5f3d37f

The ticket pins `cert_all` (Target) and instances (2)-(3) by text; the definitions and the other theorems are pinned as "the
probe's `:224-433`, `:653-662`, `:664-1211` verbatim up to the namespace" (only the `Cand` docstring may drop `LWG5Cand`).
```
$ for n in cert_all lwCert_root0_nonleaf lwCert_roots_below; do <ticket text `n : …`> vs <Lean statement>, whitespace-normalised; done
cert_all: ticket text == Lean (whitespace-normalised)
lwCert_root0_nonleaf: ticket text == Lean (whitespace-normalised)
lwCert_roots_below: ticket text == Lean (whitespace-normalised)
$ for n in cert_all cert_FF cert_FT goodB_succ_of inner_node_one root_FF_shape root_FT_shape; do diff <probe stmt> <branch stmt>; done
## cert_all identical / ## cert_FF identical / ## cert_FT identical / ## goodB_succ_of identical / ## inner_node_one identical / ## root_FF_shape identical / ## root_FT_shape identical
```
Whole-body copy check (probe `:224-433`, `:653-662`, `:664-1211` vs the three files after `namespace RBM.Graph.LWCert`;
blank, `#print`, `end`, `namespace`, `open`, `import`, `set_option`, `noncomputable section`, `/-! ##` lines removed):
```
$ wc -l p.txt o.txt ; diff p.txt o.txt
     724 p.txt
     742 o.txt
0a1,6
> A model node is a real `LGraph (Fin (a+1)) (Fin b)` (external vertices `0..a`, internal `a+1..`) with the images of `x`, `y`;
> ... (5 more lines: the section-3 docstring, = probe :215-223, sliced off by the :224 start; verbatim)
50c56
< /-- A candidate of a model node (the data of `LWG5Cand` / `oe2x_graph_E`). -/
---
> /-- A candidate of a model node (the data of `oe2x_graph_E`). -/
184a191,202
> theorem lwCert_root0_nonleaf : ...   (instance (2), ticket text)
> theorem lwCert_roots_below : ...     (instance (3), ticket text)
diff-exit 1
```
Only allowed differences.  Imports exactly as Route; `open RBM.Gauss.Sizes` only; options = probe `:34-39` plus
`linter.style.whitespace false` (linter switch only).  The root is the merged `LWG5Graph`
(`rootInfo k s := belowOf (a := 1) (b := 3) (LWG5Graph k s) ![0, 1]`, `LWExpCert.lean:204`; `LWG5Graph` at
`LWExpTerm3.lean:54`, not redefined).  Counts (`grep -c "^theorem <p>"`): `ch_FF_` 78, `ch_FT_` 78, `chs_FF_` 6, `chs_FT_` 6, `root_FF_[0-9]` 11, `root_FT_[0-9]` 11.
Scope: `cert_all` is about the computable model; its link to `LGraph.partition`/`LWG5Expand'` is tickets 3-4, per the ticket.

## 2. Hidden hypotheses, vacuity, cycles

- No premises: all targets except `goodB_succ_of` are closed `Bool` facts; `goodB_succ_of` (assembly) has explicit hypotheses only.
- No `Prop` definition (`grep -c ": Prop"`: 0 / 0 / 0); structures `MNode`, `Cand` are data (no proof fields).
- Non-vacuity: `root_F?_shape` gives `rootInfo.2.length = 11` (the `.all` in `cert_all` is over 11 terms, not `[]`);
  instance (3) shows none of them is a leaf (so `goodB 3` is not discharged by `leaf`); instance (2) shows root term 0 has
  `ord 3 < tgt 4`, `b = 2`, 2 candidates; `goodB (n+1)` requires `!(cands N.g).isEmpty` (`:199`).
- Dependencies: only merged upstream modules; S1 imports S0 only for `cert_FF`; no cycle.  No external hypothesis.

## 3. Compiled nonempty instances (in `LWExpCert.lean`, all `decide +kernel`, concrete data `(k,s,i) = (false,false,0)` and both `s`)
```
theorem inner_node_one : goodB 3 (rootAt false false 0) = true := by            -- :259 (1)
theorem root_FF_shape : (rootInfo false false).1 = true ∧ (rootInfo false false).2.length = 11 := by decide +kernel   -- :267 (4)
theorem root_FT_shape : (rootInfo false true).1 = true ∧ (rootInfo false true).2.length = 11 := by decide +kernel     -- :268 (4)
theorem lwCert_root0_nonleaf :                                                   -- :272 (2)
    leaf (rootAt false false 0) = false ∧ (rootAt false false 0).g.scalingOrder = 3 ∧
      tgt (rootAt false false 0) = 4 ∧ (rootAt false false 0).b = 2 ∧
      (cands (rootAt false false 0).g).length = 2 := by
theorem lwCert_roots_below :                                                     -- :279 (3)
    (rootInfo false false).2.all (fun N => !leaf N) = true ∧
      (rootInfo false true).2.all (fun N => !leaf N) = true := by
```
Scratch application of the target (after the S1 build):
```
$ cat ex.lean
import RBM3D.Graph.LWExpCertS1
open RBM.Graph.LWCert
example : ∀ s, (rootInfo false s).1 = true ∧ (rootInfo false s).2.all (goodB 3) = true := cert_all
example : goodB 3 (rootAt false false 0) = true := inner_node_one
#print axioms cert_all
$ lake env lean ex.lean; echo exit $?
'RBM.Graph.LWCert.cert_all' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

## 4. Build and axioms (audit worktree; CONTROL H101 / §105 (4): one module per invocation, nothing else running)
```
$ date -u; lake build RBM3D.Graph.LWExpTerm3 RBM3D.Graph.LWGGExp RBM3D.Graph.LWWeightExp RBM3D.Graph.LWStein RBM3D.Graph.LWVocab
Wed Oct  7 06:06:01 UTC 2026 ... Build completed successfully (3881 jobs).
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCert          # 06:06:04 -> 06:06:13 UTC, exit 0
⚠ [3882/3882] Built RBM3D.Graph.LWExpCert (5.6s)
info: RBM3D/Graph/LWExpCert.lean:284:0: 'RBM.Graph.LWCert.goodB_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:285:0: 'RBM.Graph.LWCert.inner_node_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:286:0: 'RBM.Graph.LWCert.root_FF_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:287:0: 'RBM.Graph.LWCert.root_FT_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:288:0: 'RBM.Graph.LWCert.lwCert_root0_nonleaf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: …:289:0: 'RBM.Graph.LWCert.lwCert_roots_below' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3882 jobs).
        8.35 real         5.12 user         4.82 sys
          3726262272  maximum resident set size
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertS0        # 06:06:18 -> 06:15:42 UTC, exit 0
⚠ [3883/3883] Built RBM3D.Graph.LWExpCertS0 (561s)
info: RBM3D/Graph/LWExpCertS0.lean:296:0: 'RBM.Graph.LWCert.cert_FF' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3883 jobs).
      563.87 real       542.20 user        18.33 sys
          6990626816  maximum resident set size
                   0  swaps
```
Before S1: `pgrep` showed a main-worktree `lake build` and `vm_stat` free+inactive+speculative = 159125+474586+50996
pages of 16 KiB (≈10.4 GiB < 12 GB); waited until `pgrep -f "bin/lake|bin/lean"` was empty (06:17:06 UTC), then:
```
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpCertS1        # 06:17:09 -> 06:27:30 UTC, exit 0
⚠ [3884/3884] Built RBM3D.Graph.LWExpCertS1 (618s)
info: RBM3D/Graph/LWExpCertS1.lean:308:0: 'RBM.Graph.LWCert.cert_FT' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Graph/LWExpCertS1.lean:309:0: 'RBM.Graph.LWCert.cert_all' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3884 jobs).
      621.19 real       596.26 user        20.87 sys
          7014023168  maximum resident set size
                   0  swaps
$ grep -c "ofReduceBool\|trustCompiler\|sorryAx" b0.log b1.log b2.log ; grep -c error b0.log b1.log b2.log
0 0 0 ; 0 0 0
$ grep -nwE "sorry|admit|native_decide|axiom|ofReduceBool|implemented_by|extern" RBM3D/Graph/LWExpCert*.lean | grep -v "#print axioms"; echo $?
1
$ git diff --name-only main...t/T2306
RBM3D/Graph/LWExpCert.lean
RBM3D/Graph/LWExpCertS0.lean
RBM3D/Graph/LWExpCertS1.lean
```
No build killed, no swap, no retry.  Limits (ticket: ≤ 30 min, ≤ 8 GB per module): 8.4 s / 3.73 GB;
563.9 s / 6.99 GB; 621.2 s / 7.01 GB — all within; consistent with the prover's 561.3 s / 7.09 GB and 615.6 s / 6.87 GB and
the probe's 1148.6 s / 7.43 GB for both halves.  No frozen signature touched (all three files new; `RBM3D.lean`,
`RBM3D/Test/Axioms.lean` untouched); full `lake build` is the hub's.

Name clash (main 1d19466, ticket's `git grep -nwE` pattern, `Probe/` excluded, 36 names + chunk patterns):
```
HIT kids: 1
main:RBM3D/Graph/LWExpTerm5.lean:147:def RCand.kids {P : PGraph (Fin 2)} (c : RCand P) : List ((ℕ × ℕ) × PGraph (Fin 2)) :=
(theorem|lemma|def) +(ch_F[FT]_|chs_F[FT]_|root_F[FT]_) : 0 ;  "namespace RBM.Graph.LWCert" on main: 0
```
`RBM.Gauss.Sizes.RCand.kids` vs `RBM.Graph.LWCert.kids`: different full names, no clash.

## 5. Paper deltas
```
$ grep -n "T2288[a-e]" docs/paper-deltas.md
1571:- **D612（T2288a–e）**：... 叶界为有限内核证书（`B:98`「检查」）（LW-14e-D 设计，4686e08）。
```
The only Lean/paper difference (the leaf bound of `B:98` "verified by inspecting" is a finite kernel certificate on a
computable model) is covered by D612 (T2288e).  Prove report (d): no new candidate; agreed.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
1. Prove (b) profiler: per-declaration time inferred from cumulative values (18 s); modules are 564 s / 621 s in total, so every
   declaration is far below 5 min regardless.  2. `longLine` linter warnings only (the `⚠` on the build lines).

## Verdict per target
`cert_all`, `cert_FF`, `cert_FT`, `goodB_succ_of`, `inner_node_one`, `root_FF_shape`, `root_FT_shape`, `lwCert_root0_nonleaf`,
`lwCert_roots_below`: PASS.  No dispatcher sign-off needed.
