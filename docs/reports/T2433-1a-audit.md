Auditor model: claude-opus-5-5

# T2433 1a-audit, round 2 (design gate, generic half only), Mon Oct 12 09:05:06 UTC 2026 (`date -u`)

Scope (binding): Amend 1 (`docs/tickets/T2433-amend-1.md`), CONTROL H234, H235 (Q3-C1, Q3-C2). The work under review is the generic half:
`BACtx`, the GG-with-context Lemma for both charges with its `kids` form, `BAselStar`, `BAG5LeafProps`, `BAG5Attached`, for any root list.
Dropped: the `baG5Graph` table, target 4, and any closure claim for the true roots. Round-1 RETURN items 1 (concrete route) and 2 (file-2 line
plan), and minor item 3 (the D §3.4 reconciliation), are answered by the scope cut (Amend 1 item 3), so they are not re-judged here.
Reviewed: sections (a), (a″) and (a⁗) of `docs/reports/T2433-prove.md`, and the probe `RBM3D/Probe/T2433Pins.lean` on `t/T2433` at `f275032`.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2433-1a-audit2` (detached at `f275032`; `main` = `ec795c5` build cache by `cp -c`).

## 1. Probe recompile in my own detached worktree (deliverable (iv))
```
$ lake build RBM3D.Graph.BAExpandId RBM3D.Graph.LWExpSound RBM3D.Graph.LWExpTerm6     # deps of the probe, at f275032
Build completed successfully (3947 jobs).
$ /usr/bin/time -l lake env lean RBM3D/Probe/T2433Pins.lean > aud2_probe.out      # 08:53:34 .. 08:53:41 UTC
EXIT=0          6.57 real   3561717760 maximum resident set size
$ wc -l < aud2_probe.out; grep -ciE "error|warning" aud2_probe.out; git status --short | wc -l; git grep -nE "sorry|admit|native_decide|^axiom" -- RBM3D/Probe/T2433Pins.lean | wc -l
      72
0
       0
       0
$ sed -n 7,16p aud2_probe.out
@BACtx : {P : BAPGraph (Fin 2)} → BARCand P → Prop
BAselStar : BASel
BAG5Fuel : ℕ
def RBM.Graph.BAG5CtxLemma : Prop :=
∀ (P : BAPGraph (Fin 2)) (c : BARCand P),
  BACtx c →
    (∀ T ∈ BAExpandId_ggL2 c.σ P.g c.p c.q, ↑(P.scalingOrder + 1) ≤ T.scalingOrderG) ∧
      ∀ T ∈ BAExpandId_ggL4 c.σ P.g c.p c.q, ↑(P.scalingOrder + 1) ≤ T.scalingOrderG
def RBM.Graph.BAG5CtxKids : Prop :=
∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c → ∀ r ∈ c.kids, P.scalingOrder + 1 ≤ r.2.scalingOrder
$ git diff --stat main...t/T2433
 RBM3D/Probe/T2433Pins.lean | 246 +++++   1 file changed      # probe ≤ 400 lines; sole writable file; never merged
$ for n in BACtx BAG5CtxLemma BAG5CtxKids BAselStar BAG5LeafProps BAG5Attached BAG5Tgt BAG5Leaf BAG5Expand baG5CtxLemma_holds baG5CtxKids_holds; do grep -rlw $n RBM3D RBM3D.lean | grep -v Probe/ | wc -l; done   # main worktree
BACtx 0; BAG5CtxLemma 0; BAG5CtxKids 0; BAselStar 0; BAG5LeafProps 0; BAG5Attached 0; BAG5Tgt 0; BAG5Leaf 0; BAG5Expand 0; baG5CtxLemma_holds 0; baG5CtxKids_holds 0;
```
The output lines match (a″) lines 88-112 (same 72 lines, exit 0). Generic-half statements vs the ticket and Amend 1:
- `BACtx c` = `Normal` ∧ (H1) `atom v` internal and exactly 2 solid edges meet it ∧ (H2) `atom v`, `atom y`, `atom y'` pairwise distinct ∧
  (H3) `atom y'` or `atom y` internal (probe 73-79). This is T2398-design §3.3 verbatim in content. It is a `Prop` on the `BARCand` data,
  so no hypothesis is hidden in a structure field: `BARCand`'s fields (`BAExpandId.lean:348-360`) are the pair data only.
- The Lemma is pinned for both charges (`c.σ` free) at the graph level (`BAG5CtxLemma`) and in the `kids` form (`BAG5CtxKids`), for all `P`
  and `c`, as target 2 asks. Dispatcher note (5) does not apply because the pin keeps both charges.
- `BAG5Attached` is the twin of `LWAttached` over `mol`. `BAG5LeafProps` = `Normal ∧ nM ≤ 1 ∧ 2 ≤ nW ∧ BAG5Attached ∧ BAG5Tgt`, the order of
  `LWG5LeafProps`. `BAG5Tgt` and `BAG5Leaf` are verbatim from T2398 probe 158-166 (round 1: diff empty) and are not weakened.
- Nondegenerate instances that compile: `baAllM` is a leaf with all five properties and `BAselStar = none` there. `BACtx instCand ∧ BACtx
  instCandRed` (`decide +kernel`) holds, and both Lemma pins specialise at that blue/red pair. `BAG5Attached instP` holds, and fails when one
  edge is removed. `BAselStar instP ≠ none`. The only remaining hypotheses are `hL`/`hK`, the 1b targets themselves.

## 2. H235 conditions, checked on the probe
```
$ git show t/T2433:RBM3D/Probe/T2433Pins.lean | grep -n "if h : ∃ c : BARCand P\|^def BAG5Fuel\|^def BAG5Expand'\|#check (BAG5LeafProps (BAexpandRoot\|^example (h : BAG5LeafProps\|design's closure table says"
64:def BAG5Expand' (d : ℕ) : Prop :=
93:design's closure table says does not happen at a non-leaf of the tree: report (a), rows 4-5). -/
96:  if BAG5Leaf P then none else if h : ∃ c : BARCand P, c.σ = true ∧ BACtx c then some h.choose else none
100:def BAG5Fuel : ℕ := 2
118:#check (BAG5LeafProps (BAexpandRoot BAselStar BAG5Fuel) : Prop)
239:example (h : BAG5LeafProps (BAexpandRoot BAselStar BAG5Fuel)) : (∀ d, BAG5Expand' d) ∧ BAG5Expand (BAexpandRoot BAselStar BAG5Fuel) := by
```
- **Q3-C2: met.** `BAselStar` (line 96) picks only from `{c | c.σ = true ∧ BACtx c}`, a subset of the `BACtx` candidates (H1-H3). It is not
  widened to V2 or V3. H234 lets 1b add red `BACtx` candidates; that still stays inside `BACtx`, and the Lemma covers both charges.
- **Q3-C1: no completeness statement is asserted.** The generic pins (`BACtx`, `BAG5CtxLemma`, `BAG5CtxKids`, `BAG5Attached`, `BAG5LeafProps` as
  a predicate) say nothing about which leaves a tree ends in. `BAselStar` returns `none` when no `BACtx` candidate exists, so a stuck node
  stays expressible. That leaves room for an extra leaf class (a new list predicate whose per-graph body is `(… ∧ BAG5Tgt q) ∨ Extra q`) or
  an extra step type (another selector).
  Several probe items are completeness-shaped or about `baG5Graph`, all outside the scope of 1b (Amend 1, H234, H235): `BAG5Expand'` (64),
  `BAG5Fuel` (100), the `BAexpandRoot` `#check`s (118-121), the identity example (232) and the conditional example (239), plus the planned
  `baG5LeafProps_holds` and `baG5Expand'_holds` ((a″) Note 2). These are probe-only text, not proved claims. See §6 for the conditions on 1b.

## 3. The Lemma (deliverable (ii)): rerun, plus the auditor's own random families
```
$ cd scratchpad/T2433 && python3 rnd_all.py 42 16000 | diff rnd_all_42.out -      # 1:19.64 total
10a11  > python3 rnd_all.py 42 16000  77.42s user ...          # (the time line only: content EMPTY diff)
  H1,H2,H3 = (1, 1, 1) cands 2154 violations(min Δord<1) 0     # every other H-pattern has violations, e.g. (1,1,0) 259/259, (1,0,1) 1431/935, (0,1,1) 10332/8009
$ python3 -I aud2/rnd_aud.py 907 12000 two .     # my script: fresh seed, 3-9 internals, 0-4 waved, 0-5 M edges, both charges
seed 907 mode two graphs 12000 {'cands': 28483, 'BACtx blue': 1193, 'kids': 148559, 'viol(min dord<1)': 0, 'BACtx red': 536} min dord 1
$ python3 -I aud2/rnd_aud.py 908 12000 one .     # only E(0) used: x = y identified (P.E' of size 1, allowed by BAPGraph (Fin 2))
seed 908 mode one graphs 12000 {'cands': 33323, 'BACtx red': 571, 'kids': 143821, 'viol(min dord<1)': 0, 'BACtx blue': 1144} min dord 1
$ python3 report.py | diff report.out -  (time lines dropped): EMPTY
  instP=baG5Circ: ord 3 nS 5 nW 2 nA 3 nM 1; v=inr0 y=('i', 1) y'=('e', 0)
  H1 atom(v) internal: True, solid edges at atom(v): 2 (=2); H2 distinct atoms: True; H3 internal y: True; BACtx: True
  63 kids: Δord histogram {1: 14, 2: 27, 3: 18, 4: 4}; leaves among them 49, nonleaf 14 (ord 4, x~y no)
$ cd l4s3 && python3 lemma_totals.py      # the S3 trees of (a⁗): another family of parents
Lemma over the 8 (root, s) trees: BACtx steps 148, kids 10284, min Δord 1, kids with Δord < 1: 0
$ cd RBM3D-wt/T2433-1a-audit2 && /usr/bin/time -l lake env lean aud2/t1.lean   # decide +kernel: ∀ T ∈ instP.g.gg2 instCand.p instCand.q, ∀ Q ∈ T.splitG, ord+1 ≤ ord Q
       18.37 real   6104023040 maximum resident set size   EXIT=0     # 09:04:25 .. 09:04:43 UTC
```
The Lemma holds in every family tried: the tree, 2 × 16,000 + 2 × 12,000 random graphs, the one-external case and the S3 trees. On the Lean
side, the gg2 half at `instCand` holds by kernel evaluation. H1, H2 and H3 are each necessary. The mirror leaves out Ψ-dotted and ×-dotted
edges. `atomAdj` (`BAVocab.lean:92-96`) joins atoms by Ψ edges exactly as by `M` edges. ×-dotted edges touch neither atoms nor `nS, nW, nA`,
and `ord = nS + 2(nW − nA)` (`ba.py:43`), so this coverage is enough for a pin over all `P`. (a) row 7 is right that the `+1` for A4-BD needs
the merge count `κ′ ≥ j/2` and is not a corollary of `gg_scalingOrderG`, and it prices this. **(ii): met. The Lemma is not false at any parent
tested, so there is no stop.**

## 4. Lean route of the generic half (deliverable (iii), restricted) and the line plan (vi)
- Route ((a) row 10, (a″) Note 5). Counters through `packMerge` use `BAGraph.partition_of_normal` and the private
  `BAWeightOp_packMerge_counters`. Atoms through `merge` need a new lemma from the private `BAVocab_merge_atomAdj`, `_adj`,
  `BAVocab_closure_equiv` and `_vmap_injective` (about 80 lines). The per-term counters come from `gg_counters`, `gg_raw`,
  `gg_scalingOrderG`, `BAGGOp_kappa`, `le_scalingOrderG_iff`. The red charge goes through `BAExpandId_flip`. All 11 inputs elaborate in the
  probe (output lines 26-72 of my run, identical to (a″)). No `decide` over kids is needed for an abstract lemma over all `P`. The concrete
  `decide` and relabelling route that round 1 returned belonged to the closure table, which is now dropped.
- Lines ((a) row 14): `BAG5Leaf.lean` 1,300 central (900-1,900). That is the Lemma for blue at 900 (atom-merge count 350, 9 term kinds 450,
  kids form 80), red at 150, and pins, `BACtx`, selector and docs at 250. The Lemma is priced separately, as asked. The high estimate of
  1,900 is under the 2,000 binding line. `BAG5Leaf2.lean` (Amend 1: "may stay unused") absorbs overflow, for example the red half and the
  kids form, so neither file reaches the stop line. **(iii), (vi): met for the generic half.**

## 5. (a⁗) L4S3-L1 as evidence; consumers; paper deltas
```
$ cd l4s3 && python3 table.py | diff <(sed -n 214,222p T2433-prove.md) -         → EMPTY  (T3C-tr_k: 7 stuck each charge; D1X, D2X: 0 stuck, 109 leaves)
$ python3 widened.py | diff <(sed -n 237,240p T2433-prove.md) -                   → EMPTY  (V1 = BACtx leaves #0, #2 of T3C-tr open; V2/V3 close s=1 only)
$ python3 stuck_cmp.py
T3C-tr_0 and T3C-tr_1: s=1 has 7 stuck nodes, s=0 has 7; s=0 list == s=1 list with Gc(y,x) -> Gbarc(x,y): True (both lines)
```
(a⁗) reproduces exactly. Its outcome (NOT LIFTED) was answered by H234 ("T2433 resumes now … generic half only") and does not touch the generic
half. The stuck nodes have no `BACtx` candidate, and the Lemma is not false at any of them: 148 steps, 0 violations. The run is the reason for
Q3-C1 and Q3-C2. It is not a reason to widen `BAselStar`, and it is not used here for that.
Consumers (v): under the S3 HOLD (DECISIONS §254) L4g and L4c1 do not start. The generic outputs are predicates and the Lemma; REQ-0805-S3A
(iii), on whether `BAG5LeafProps`/`BAG5Tgt` need an interface for an averaged leaf class, is open with the supervisor. H236: "no change to
the running tickets". Q3-C1 already keeps that room open, so this is not BLOCKED.
Paper deltas: T2398a (corrected target, inside `BAG5Tgt`) and T2398b (Lemma needs H1-H3; necessity shown in §3) are carried. T2433b (the
uncovered T3C-tr configuration, B:102-108) is proposed in (a⁗); DECISIONS §254 records it as L4S3-F2. Coverage of the generic statements'
differences from the paper is complete.

## 6. Conditions carried to stage 1b (from Amend 1, H234, H235; not defects of (a))
1. Pin and prove only: `BACtx`, `BAG5CtxLemma` + `BAG5CtxKids` (both charges) with the instances at `instCand`/`instCandRed`, `BAselStar`
   (inside `BACtx`; red allowed), `BAG5Attached`, `BAG5LeafProps` (with `BAG5Tgt`, `BAG5Leaf` as needed). `BAG5Expand` may stay only as a
   definition.
2. Do not carry from the probe: `BAG5Expand'`, `BAG5Fuel`, the `BAexpandRoot` checks and examples (lines 118-121, 232, 239),
   `baG5LeafProps_holds`, `baG5Expand'_holds`, `BAexpandRoot … ≠ []`, or any theorem whose conclusion is `BAG5LeafProps`/`BAG5Expand` of a
   tree (Q3-C1). Also leave out the docstring claim at probe 92-93 ("does not happen at a non-leaf of the tree").
3. T2433a (attachment by Even + Connected) belonged to the dropped closure. 1b proves no attachment theorem, so (d) should mark it as not
   proved by this row.

## 7. Observation (no RETURN)
O1. (a″) Note 2 and the probe docstrings still describe targets 3 and 4 in their pre-Amend form. The report has no (a′) restating the
generic-half target list; Amend 1 and H234 give that list directly, so no statement is affected.

## Verdict
| deliverable (generic half) | verdict |
|---|---|
| (ii) `BACtx` (H1-H3) and the Lemma, both charges, kids form; Δord table; H1-H3 each necessary | PASS (rerun + 2 new random families, 0 violations) |
| (iii) Lean route of the Lemma (merged inputs named, all elaborate) | PASS |
| (iv) statements compiled in the probe (recompiled here, EXIT 0, nondegenerate instances) | PASS |
| (v) consumers, C1 (combinatorial), paper deltas | PASS |
| (vi) lines per file, Lemma priced: file 1 1,300 (high 1,900) < 2,000; file 2 spare | PASS |
| H235 Q3-C1 (no completeness statement), Q3-C2 (`BAselStar` ⊆ `BACtx`) | PASS (conditions §6 for 1b) |
| stop rules: false pin, missing input, Lemma false at a Lean parent | none hit |

**Overall: PASS** for the generic half (Amend 1 scope). No dispatcher sign-off is needed. Stage 1b `prover-max` may start under §6.
