Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 12:31:43 UTC 2026

Verdict (details at the end): T1 matching of band-tagged outputs PASS (per step, except `gg`: per output, two selectors); T2 `BAsim`: the literal form is true but not derivable from T1 (macro outputs), `BAsim'` PASS; T3 per step or per output: per output for `gg` only; T4 Lemma E PASS (exhaustive); T5 fallback: no band shape needs a twin. Two scope findings F1, F2 below.
Model: own Python transcription (scratchpad `T2423/model.py`, no Lean) of `BAWeightOp.lean:68-79`, `BAGGOp.lean:73-100`, `BAExpandW.lean:122-146`, `t/T2395` probe 154-195 (`withinOuts`, `splitOuts`), the band terms `LWWeightExp.lean:656-700`, `LWEdgeExp`, `LWGGExp.lean:484-535`, `LocStep` `LWLvl1.lean:3260-3290`, `LGraph.partition` `LWVocab.lean:1013-1140`, and R0's `img` (`BAAtomic.lean`, merged `1dc7516`). Graph equality = canonical form of the graph (solid edges with `σ,circ,ends`; waved with `col,σ`, ends unordered; `×`-dot set; coefficient ignored).

### (i) Exponent table (the quantities the matching and `BAsim` depend on)
`BAFrameStep` kinds and their band partners at `img P` (selector `(c,t)`; `nat = (0,0)`, `swap = (0,1)` with `p' := q`, `LocStep.gg` hyps `hp,hq,hp1,hq1` at `lwSymmTwistS 0 1`). Δ = of the all-circled output at a generic parent (`raw.py`); "min Δord" = minimum over every coincidence pattern, split by extra / not extra (`slack.py`; `—` = no extra output exists):

| BA term | band partner | (ΔnS,ΔnW,ΔnA) | Δord | min Δord not extra | min Δord extra |
|---|---|---|---|---|---|
| `lw2.leaf`, `lw2.D` | owxT1, owxT3 | (1,1,1) | 1 | 1, 0 | —, 0 |
| `lw4.leaf`, `lw4.D` (`M⁺S⁺`) | owxT2, owxT4 | (1,2,2) | 1 | 1, 1 | —, 2 |
| `L1` (lanlw), `LD` | owxT1; D, P5, P3, P6, P4 | (1,1,1) | 1 | 1, 0 | 2, 1 |
| `A1` (S1) | R2 `(δ,m)` | (−2,1,−1) | 2 | **0** | **0** |
| `A2`, `A3` (S2a, S2b) | R2 `(×,edge)`: `A3` nat, `A2` swap | (−1,1,0) | 1 | 1, 1 | —, — |
| `A4`, `A5`, `AD` (sum 3, `W=1`) | R3/R5, R5, R7 | (1,1,1) | 1 | 1, 1, **0** | 2, 1, 0 |
| `B1`, `B2`, `BD` (sum 3, `W−1`) | R4, R6, R8 | (1,2,2) | 1 | 1, 1, 1 | —, 1, 1 |
| macro (a) `W.first`, `W.D` | owxT1, owxT3 | (1,1,1) | 1 | 1, 0 | —, 0 |
| macro (b) stage 1 `X.L1`, `X.LD`, `X.d1` | R3/R5, R7, R5 | (1,1,1) | 1 | 1, 0, 1 | 2, 0, 1 |
| macro (b) `X.d2`, `X.d3`, `X.d4` | none at `img P` as graphs | (−1,1,−1), (−1,1,−1), (−2,1,−2) | 3, 3, 4 | 1, 1, **0** | 3, 3, 2 |
| macro stage 2 | band step at `img(tr)`, `tr` = transfer graph | `inv(img tr) = inv P` (300/300) | — | — | — |

Slack 0 (equal order) occurs exactly at `lw2.D, LD, A1, AD, X.LD, X.d4, W.D`: no better constant than `Δord ≥ 0`. Statement constants: 17 band shapes (`LocStep` 4 + 6 + 7); tags used `band, e1, e2, macroA, macroB` (`s1` never needed: `A1` is the band's R2 `(δ,m)`; F1); selectors per output: `nat` for all kinds, `swap` only for `A2` (below).
**Lemma E at graph level** (extra := `Q` merges two atoms of `P` joined by a solid edge of `P`; claim `ord Q > ord P` or `nExt Q < nExt P`; also `BAstepMono`: ord up, `n_M`, `n_A−n_W`, `nExt` not up). Exhaustive over all vertex identifications × atom merges × external flags × edge colour of the consumed edges, real term builders incl. `lw4`, `gg4`, sum 3:
```
$ cd $SP/T2423 && python3 lemE.py
weight parents 86 outputs 1516 extras 160 W-violations 0 E-violations 0
within parents 122 outputs 1082 extras 160 W-violations 0 E-violations 0
edge parents 114 outputs 1124 extras 354 W-violations 0 E-violations 0
gg parents 680 outputs 20952 extras 1752 W-violations 0 E-violations 0
ggSplit parents 848 outputs 21136 extras 4628 W-violations 0 E-violations 0
$ python3 mut.py; python3 mut2.py     # sensitivity: S+ edge of lw4 dropped / waved edge of A1 dropped
mutant (S+ edge of lw4 dropped): outputs 1516 W-violations 254 E-violations 0
mutant (waved edge of A1 dropped): outputs 20952 W-violations 263 E-violations 246
```
**Matching** (random normal BA parents with a frame step, 600 per kind; tag rule: stage-2 outputs of macro (a)/(b) and `X.d2-d4` → `macroA/B`; else extra → `e1` (`L1` with its `M`-split) / `e2`; else `band`):
```
$ python3 full.py 101 600 > ev/full.out
tag ('edge','band') 8603 | ('gg','band') 9772 | ('ggSplit','band') 3221 | ('weight','band') 24226 | ('within','band') 12216
tag e1 600, e2 (edge 3197, gg 1180, ggSplit 803, weight 3630, within 1800), macroA 28032, macroB 11648
band-tagged outputs with no match in any option: 0
per-step options matching ALL band-tagged outputs ('gg', ('nat','swap')) 399 | ('gg', ('nat',)) 38 | ('gg', ()) 163
  (edge, weight: ('nat',) 600/600; within ('nat',) 540 + ('nat','t') 60; ggSplit ('nat',) 39 + ('nat','swap') 561)
$ python3 ggsel.py   # band-tagged gg outputs: nat-only / swap-only / both
('A','both') 4366 | ('A','nat-only') 173 | ('A','swap-only') 173 | ('AD','nat-only') 379 | ('B','both') 3556 | ('BD','nat-only') 727
```
Per step fails only for `gg` (163 of 600 steps): `A3` needs `nat`, its mirror `A2` needs `swap`. Routes of every output (`full2.py 31 300`, 0 `NONE`, 0 monotonicity violations): band-tagged → graph at `img P` (28,491 outputs); `macroA` → graph at `img(tr)` 13,948 / ord rises 236; `macroB` → graph at `img(tr)` 4,606, tuple at `img P` 1,194, graph at `img P` 52, ord rises 6, nExt falls 6; `e1/e2` → ord rises or nExt falls (extras violating both: 0). Literal `BAsim` (invariant tuple among outputs of a band step at `img P`, or ord up, or nExt down): 53,624 outputs, 0 FAILS (`python3 literal.py`).
**Statement forms (pseudo-Lean; compiled by the probe step)**
```
BAEquiv R S  := ∃ eE eI, solid R ~perm S.relabel ∧ waved R ~perm (rev-or-not) ∧ xdots as sets ∧ ext compatible   -- coeff ignored
BAFrameStepT : BAPGraph E → List (BAShape × BAPGraph E) → Prop        -- tag by (term, mask); untag BAFrameStepT = BAFrameStep
baSim_band  : BAFrameStepT P LT → P.g.Normal → (band,Q)∈LT → ∃ L', LocStep m P.img L' ∧ ∃ R∈L', BAEquiv R Q.img   -- per output (L' = nat or swap)
baSim_extra : (e1|e2,Q)∈LT → P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt                        -- Lemma E
BAsim' m    : BAFrameStep P outs → P.g.Normal → ∀ Q∈outs, (∃ G', G' normal ∧ inv G' = inv P.img ∧ ∃ L', LocStep m G' L' ∧ ∃ Q0∈L', inv Q0 = inv Q)
                ∨ P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt    -- G' = img P, or img of the transfer graph (macro)
```
No external hypothesis (the `m` of `LocStep m` is free: `partition m` puts `m` in the coefficient only), so no limit computation applies.

### (ii) One concrete nondegenerate instance
`P_A`: `E = {0,1}`, `I = {2,3,4}`; blue circled solid `2→1`, `0→2`, `1→0`; waved `S_{4,3}`; `M`-dot `{2,3}`; atoms `{0},{1},{2,3},{4}`; `(ord,n_M,n_A−n_W,loops,n_S,pairs,nExt) = (1,1,1,0,3,1,2)`; step `gg` at `p = (2→1)`, `q = (0→2)`, `m = i` (any). `P_B` (macro (a)): solid `2→3` (inside the atom), `0→2`, `1→4`, same waved and `M`-dot; `P_C` (macro (b)): solid `2→1`, `0→3`, `1→0`, same waved and `M`-dot (`p = 2→1`, `q = 0→3`, `2,3` one atom).
```
$ cd $SP/T2423 && python3 inst.py
== A: GG (Step 3), band selectors nat and swap   [band outputs: nat 264, swap 264]
  BA outputs (after partition): 31 | tag band graph@P:nat 13 | band graph@P:nat/swap 9 | band graph@P:swap 1 | e2 no graph match 8
  outputs with no graph match, by invariant route (BAsim disjunct): {('e2','nExt falls'): 1, ('e2','tuple@P'): 5, ('e2','ord rises'): 2}
  Lemma E on the extras (e1/e2): {' nExt falls': 1, 'ord rises': 5, 'ord rises nExt falls': 2}  | weak monotonicity violations: 0
== B: within-atom edge (macro A)   transfer image invariants equal those of P: True
  BA outputs: 51 | band graph@P:nat 8 | nat/t 6 | e2 nat 2 | e2 nat/t 1 | macroA graph@tr:wt 34 | Lemma E {'ord rises': 3} | violations 0
== C: split pair (macro B)   transfer image invariants equal those of P: True
  BA outputs: 48 | band nat 4 | nat/swap 4 | e2 no graph match 6 | macroB graph@tr:gg 13, gg/gg_sw 9, gg_sw 1, no graph match 11
  no graph match by invariant route: {('e2','tuple@P'): 5, ('e2','ord rises'): 1, ('macroB','tuple@P'): 7, ('macroB','nExt falls'): 2, ('macroB','ord rises'): 2}
hyps A / C : BA Normal True | hwf True | hnb True | band Normal at img P True | band hwf True | band hnb True | x internal atom True | |V| 5, nExt 2
```
All hypotheses hold at once (nonempty `E`, `I`, solid edges, a non-trivial atom, `nExt = 2`, 31 / 51 / 48 outputs): BA-normal, `hwf`, `hint`, `hnb` of `BAFrameStep.gg/within/ggSplit`, and `LocStep.gg/weight` hyps (`hwf`, `hnb`, `hy`) at `img P`.

### Verdicts (reasons)
- **T1 PASS.** Every band-tagged output (58,038 sampled) equals, up to the relation `BAEquiv`, an output of the band `LocStep` at `img P`: `nat` for `weight`, `edge`, `within` stage 1, `ggSplit` stage 1; `gg` needs `nat` or `swap` per output (A2). The relation must identify waved edges up to reversal (`WEdge.transpose`, `LWSymm.lean:96`; `S, S⁺` symmetric; `scost` reads only `waved.length`, `LocalRegular6a.lean:308`; molecules read the symmetric `LGraph.adj`, `LWVocab.lean:157`) and ignore `×`-dot multiplicity and the coefficient. With plain relabelling (waved orientation kept) only the mirror `A2` fails: 56 of 3,159 band-tagged `gg` outputs, 0 of the other kinds (`python3 wrev.py`, `ev/wrev.out`). **T3 (per step or per output):** per step for `weight, edge, within, ggSplit`; per output for `gg` (one band step per selector), so `baStep_of_simC` is restated per output.
- **T2.** Literal `BAsim` (probe 263) holds as invariants (0 FAILS) but for macro outputs only by counting, not by T1: stage-2 outputs are band outputs at `img(tr)`, not at `img P`, and `X.d2-d4` have no graph partner at `img P` (the band takes Step 3 there, `LocStep.edge` is not constructible at degree 2, `hbad`). **`BAsim'` (with `G'`, `inv G' = inv img P`) PASS**; L3a4 re-proves `ba_lvl1StepGood_of_sim` at `G'` (T2397 audit obs. 2 accepts). Extras: Lemma E.
- **T4 PASS** (exhaustive, mutants caught). `ba_W_sub_one` enters only as the `gg4`/`lw4` term lists (graph level).
- **T5 fallback:** no band shape fails; no twin. Macro-tagged outputs are not a failing shape (BA-only by T2397 design; `BAShapeLL macroA/B` in T2426).
- **F1:** `BAShape.s1` is never assigned: `A1` (S1) is the band's R2 `(δ,m)` (nS falls by 2) when `[y] ≠ [y']` and not joined; with a parent edge between `[y],[y']` it is an extra. T2395 §1.5 "the band has no such term" fails at graph level in the model (paper-delta candidate `T2423a`; the probe must confirm that `LGraph.partition` merges two external vertices as `LWVocab.lean:1013-1140` reads); then `BAShapeLL s1` is vacuous.
- **F2 (scope):** `BAFrameStep`, `outsOf`, `withinOuts`, `splitOuts`, `BAShape`, `BTStep` are not on main `631b8f4` (`grep -rln` over `RBM3D/`, `RBM3D.lean`: no match; they exist only in the `t/T2395`, `t/T2397` probes); `BAGraph.twist`/`BALocStep` need T2425 (L3a1). R1 must define the frame vocabulary (T2426 also copies `BAShape`, `BTStep`: one of the two imports); the `BALocStep`-level corollary needs `img (twist) ≅ twist (img)` from L3a1.

## (a″) Probe compile — Sun Oct 11 13:20:45 UTC 2026 (stage 1a probe step, prover-max); compressed at 1b under Amend 1, O1: the pasted compile output and the listing of the pins are replaced by the commit that holds them

Probe `RBM3D/Probe/T2423Pins.lean`: 352 lines at `796a2dc` (`git show 796a2dc:RBM3D/Probe/T2423Pins.lean | wc -l`), branch `t/T2423`, commits `e5db4ba`, `796a2dc`, unchanged since (`git diff --stat 796a2dc HEAD -- RBM3D/Probe/T2423Pins.lean` is empty), never merged. Its pins are probe lines 150-195 (frame vocabulary 19-71, tags 72-139) and are diffed against the final files in (b). The compile output that stood here (`lake env lean` exit 0 at 13:18:27-13:18:59 UTC, the seven pinned declarations on `[propext, Classical.choice, Quot.sound]`, `grep -cE "sorry|admit|native_decide|^axiom"` = 0) is reproduced verbatim by the 1a-audit, `T2423-1a-audit.md` lines 10-30.

**What the probe pins (decisions of this step; probe lines in parentheses).**
- **Item 1, `BAMatch m` (172), frame level, per output.** For a `band`-tagged output `Q` of a `BAFrameStepT` at a normal `P`: some band `LocStep m P.img L'` has an output `R` with `R.BAEquiv Q.img`; `P' = P.img` itself (R0), no relabelled `P'`. Per output, not per step: on the exhaustive templates below `gg` has no single selector for 63 of 99 steps, every other kind is served by `nat` alone (T3). Frame level as `BAsim` (T2395 probe 263): the twisted `BALocStep` is this at the normal BA graph `P.twist c t` (L3a1, T2425, not merged), so the probe needs no twist.
- **`PGraph.BAEquiv` (150).** Bijections of `E'`, `I'` over `ext`; solid lists up to order; waved up to order and per-edge reversal; `×`-dots as sets; the coefficient is not read. It is what the consumers read: `LGraph.scost_perm` (`LocalRegular6a.lean:309`: solid up to order, only `waved.length`), `localReg2_cendsMS` has `Sym2` ends (`LocalRegular2.lean:603`, `_of_perm` `:752`), molecules use the symmetric `LGraph.adj` (`LWVocab.lean:157`): so what `BASimC` (cost) and `BASimP` (`PathInv2`) read is unchanged by solid reordering, waved reversal and `×`-dot multiplicity. Reflexivity is compiled (157).
- **Tags (`BAFrameStepT` 115, `extraB` 81).** Same five constructors and hypotheses as `BAFrameStep` (47); stage-1 outputs `e2` if the `M`-split merges two atoms of `P` joined by a solid edge of `P`, `e1` for those of `lanlwT1`, else `band`; `macroA` = stage 2 of macro (a); `macroB` = stage 2 and `d2, d3, d4` of macro (b). `s1` is never assigned (F1). The model of (a) labels the one extra output of `X.L1` at `P_C` `e2`, the probe `e1` (a label; Lemma E covers both). `BAFrameStepT_untag` (179) pins tagged = untagged. `BAShape`, `BTStep`, `untag` are T2397 probe 123-126 plus `deriving DecidableEq` (needed by `decide`); T2426 copies the same names: the second to merge imports.
- **Item 4, `BAExtraGood` (176): the `e1`, `e2` outputs have a higher order or fewer external atoms (Lemma E, T2395 audit O1).**
- **Item 2, `BAsim m` (183, verbatim) and `BAsim' m` (195):** the band step is at `T.img`, `T` a normal BA graph with `T.baInv = P.baInv` (`T = P`, or the transfer graph of a macro step); `BAsim m` is `T = P`, so `BAsim'` is no stronger (by unfolding). For the reduction, R0's `BAimg_holds` gives normality and the invariants of `T.img`.
- **Band side not compile-confirmed.** The image's vertex types are classical quotients and `LGraph.partitionTerms` filters by a classical `decide` (`LWVocab.lean:1295`), so `LocStep m P.img L'` and `BAEquiv` at the data are not reducible by `decide`: `BAMatch` stays a hypothesis of the examples (the T2395 pattern). Translating `hwf`, `hnb`, `hbad` of `LocStep` to the image needs `lvl1SolidAt (vmap v) = atEdges v`, R0's private `BAAtomic_solidAt` (`BAAtomic.lean:624`; the public `BAGraph.img_locStd_iff` `:661` does not give it): 1b proves its own.
**Compiled instances (all `example`s, 14 in the probe; pins stay hypotheses; every deterministic hypothesis by `decide` or an explicit membership term).** `BTStep` is `BAFrameStepT (Fin 2)` (226); `BAFrameStepT` at the five kinds: `gg` at `P_A` (227), `within` at `P_B` (229), `ggSplit` at `P_C` (230), `weight` at `P_W` (233), `edge` at `P_E` (235) (`P_A, P_B, P_C` = the data of (a) (ii): `E = Fin 2`, `I = Fin 3`, atom `{2,3}`, `M`-dot, waved edge). Kernel census of the tags equals the model of (a) (ii): `P_A` 31 outputs = 23 `band` + 8 `e2` (243); `P_B` 51 = 14 + 3 + 34 `macroA` (244); `P_C` 48 = 8 + 1 `e1` + 5 `e2` + 34 `macroB` (246; the model's 6 `e2` = 1 + 5). Lemma E by kernel evaluation at `P_A`: every `e2`-tagged `M`-split term `T'` of `gg2`, `gg4` (`BAGraph` level, before `packMerge`; no `=`-dotted edge to merge) has `ord P < ord T'` or `nExt T' < nExt P` (240). `BAMatch` at a `band` output and `BAExtraGood` at an `e2` output of `P_A` (251; both outputs exist: the census); `BAsim`, `BAFrameStepT_untag` at `gg`, `BAsim'` at `gg`, `within`, `ggSplit`, `BAMatch` at the other four kinds (262). **F1 confirmed on the band's own term:** the partition of `oe2xR2` (`LWGGExp.lean:485`, `m³ S⁺_{xy} G_{y'y} f`) at externals `y = 0`, `y' = 1` has an output with `ext 0 = ext 1` (295; `LGraph.aPairs` `LWVocab.lean:1061`, docstring `:720`): the band's `R2` `(δ, m)` option that (a) F1 matches with the BA `A1`. Axioms (scratch copy with every `example` renamed `theorem exN`): the 7 declarations printed above and the 13 proof examples depend on `[propext, Classical.choice, Quot.sound]` only.
**Finding on the evidence of (a), no verdict changes.** `lemE.py` (rows `gg` extras 1752, `ggSplit` outputs 21136, extras 4628 in (a)) passes `j = 0` for `gg`/`ggSplit`; `run.lw_pair` takes the original index of `q`, so with the extra edge `r` the partner `q` was `r` (off-spec: any colour and ends) and the `GGGamma` D-terms `AD`, `BD` consumed only the fixed edge `y'→x`. Scratchpad `T2423/`: `chk_q.py` (first line) and the repaired `lemE_fix.py` (`j = 1`, same templates, plus (E*): every output that merges two distinct atoms of `P`, whatever edge joins them, has `ord` up or `nExt` down); `match_exh.py` (matching T1 on the same templates, restricted to the hypotheses of the real step); `route_exh.py` (`BAsim'`, literal `BAsim`, macro stage 2 included). Result: 0 unmatched band-tagged outputs on all templates and in the fresh random run, 0 violations of (W), (E), (E*), no `BAsim'` route `NONE`, 0 fails of the literal `BAsim`: no failing band shape was found, so the per-shape fallback (ticket (iv)) is not triggered by these checks.
```
$ cd <scratchpad>/T2423; python3 chk_q.py | head -1
solid [(1, 1, 0, 1), (1, 1, 1, 0), (0, 1, 0, 1)]  i 0 j 0  => p (1, 1, 0, 1)  q (0, 1, 0, 1)  q.rest [(1, 1, 1, 0)]  jj -1
$ python3 lemE_fix.py
weight outputs 1516 extras 160 any-merge 304 W-viol 0 E-viol 0 E*-viol 0
within outputs 1082 extras 160 any-merge 304 W-viol 0 E-viol 0 E*-viol 0
edge outputs 1124 extras 354 any-merge 530 W-viol 0 E-viol 0 E*-viol 0
gg outputs 20952 extras 3032 any-merge 5540 W-viol 0 E-viol 0 E*-viol 0
ggSplit outputs 14352 extras 3012 any-merge 5004 W-viol 0 E-viol 0 E*-viol 0
$ python3 match_exh.py
weight  steps  86 (templates skipped by the step hypotheses   0) | band-tagged 1356, UNMATCHED 0 | selectors matching all band outputs of a step: {('nat', 't'): 2, ('nat',): 84}
within  steps 122 (templates skipped by the step hypotheses   0) | band-tagged  922, UNMATCHED 0 | selectors matching all band outputs of a step: {('nat', 't'): 38, ('nat',): 84}
edge    steps  82 (templates skipped by the step hypotheses  32) | band-tagged  482, UNMATCHED 0 | selectors matching all band outputs of a step: {('nat',): 82}
gg      steps  99 (templates skipped by the step hypotheses 581) | band-tagged 2456, UNMATCHED 0 | selectors matching all band outputs of a step: {('nat', 'swap'): 8, (): 63, ('nat',): 28}
ggSplit steps  99 (templates skipped by the step hypotheses 749) | band-tagged  937, UNMATCHED 0 | selectors matching all band outputs of a step: {('nat', 'swap'): 17, ('nat',): 82}
$ python3 route_exh.py
weight  BAsim' routes {'tuple@P': 1516} | literal BAsim (T = P) fails: 0 | inv tr == inv P: {}
within  BAsim' routes {'tuple@P': 3246} | literal BAsim (T = P) fails: 0 | inv tr == inv P: {True: 122}
edge    BAsim' routes {'ord rises': 202, 'tuple@P': 602} | literal BAsim (T = P) fails: 0 | inv tr == inv P: {}
gg      BAsim' routes {'nExt falls': 16, 'ord rises': 32, 'tuple@P': 2941} | literal BAsim (T = P) fails: 0 | inv tr == inv P: {}
ggSplit BAsim' routes {'nExt falls': 32, 'ord rises': 48, 'tuple@P': 4552} | literal BAsim (T = P) fails: 0 | inv tr == inv P: {True: 99}
$ python3 full.py 20261011 3000 | grep -E "no match|'gg', \(\)|^steps"   # fresh seed, 3000 random steps per kind (the (a) run: seed 101, 600)
steps {'weight': 3000, 'within': 3000, 'edge': 3000, 'gg': 3000, 'ggSplit': 3000}
band-tagged outputs with no match in any option: 0
per-step options matching ALL band-tagged outputs ('gg', ()) 795
```

## (a′) Preflight corrections — Sun Oct 11 14:05:38 UTC 2026

Repair of `T2423-1a-audit.md` (RETURN): its six "Required for resubmission" items, in order. Mathematics and pseudo-Lean only; scripts in `<scratchpad>/T2423/`. **No compiled statement of the probe (796a2dc) changes, no recompile.** Names added at 1b, not pinned: `PGraph.BAEquivC` (as `BAEquiv`, waved edges compared by their ends only), `BAPGraph.twist` (`{P with g := P.g.twist c t}`, T2395 probe 157). Corrections to (a)/(a″): (c1) (a″) "1b proves its own `lvl1SolidAt (vmap v) = atEdges v`" is replaced by `open private BAAtomic_solidAt BAAtomic_charge BAAtomic_fm from RBM3D.Graph.BAAtomic` (the three are private at `BAAtomic.lean:624, 633, 559`; idiom `BAGGOp.lean:47, 55`; own ≈ 15-line copies if `open private` does not take the private `def`). (c2) the lemma proved for item 4 of the ticket is E* (any identification of two P-atoms, item 2 below), which implies the pinned `BAExtraGood`.

### 1. (v) predicted lines per file (audit item 1)
```
$ python3 lines.py     # estimates (the 1a's design, section by section); basis = a counted line range of a merged analogue
BASim   B1 frame vocabulary, tags, BAEquiv, pins, BAFrameStepT_untag                                   220   basis probe T2423Pins 19-198                       180
BASim   B2 BAEquiv API (refl, trans, lvl1Comp, baInv_eq)                                               130   basis BAAtomic 435-599 (s6-7)                      165
BASim   B3 LemQ: classes of a vertex map give eE, eI, BAEquiv                                          250   basis LWExpSim 686-797 + BAAtomic 713-880          280
BASim   B4 LocStep hypotheses at P.img (weight, edge, gg nat/swap)                                     230   basis BAAtomic 600-712 (s8, one kind)              113
BASim   B5 mask S -> dot choice c(S): consistent, loops, aPairs                                        400   basis LWExpSim 798-1090                            293
BASim   B6 11 shapes: lw2 x2, lw4 x2, L1, LD, W.first, W.D (+ T-terms)                                 310   basis BAGGOp 938-1117 (6 terms)                    180
BASim   B7 compiled instances of BAMatch (weight, within, edge)                                        140   basis probe T2423Pins 226-352                      127
BASim2  C1 GG terms A1-A5, AD, B1, B2, BD + swap selector                                              330   basis BAGGOp 938-1117 (6 terms)                    180
BASim2  C2 ggSplit stage 1 (X.L1, X.LD, X.d1); transfer graph tr: normal, baInv, frame step (a), (b)   305   basis BAGGOp 1118-1305 (A1-A3)                     188
BASim2  C3 Lemma E: counter calculus, packMerge passage, 8 families                                    615   basis BAWeightOp 1353-1641 + BAGGOp 1306-1729      713
BASim2  C4 BAMatch assembly, BAsim' (tags, X.d2-d4, BAEquivC), BAsim                                   400   basis BAAtomic 600-712 (s8)                        113
BASim2  C5 compiled instances (gg, ggSplit, BAsim', BAExtraGood)                                       120   basis BAGGOp 1730-1852                             123
BASim   total predicted  1680   stop line 2000   margin  320 (16%)   +30% would be  2184
BASim2  total predicted  1770   stop line 2000   margin  230 (12%)   +30% would be  2301
both files 3450  (ticket expects 2,000-2,400; T2395 row R1 central 1,170; landed/central measured: R0 1.39 = 1247/900, L2c1 2.04 = 1941/950)
split if a file exceeds: Lemma E (C3 615) and the BAsim' assembly (C4 400) to a third file Graph/BASim3.lean (1,015): BASim 1680 / BASim2 755 / BASim3 1015
```
At the central estimate neither file reaches the 2,000 stop line (margins 16%, 12%); at +30% both would. The total is above the ticket's 2,000-2,400 and the T2395 row R1 (1,170 central; measured landed/central 1.39 for R0 and 2.04 for L2c1): this is a bottom-up count that already takes credit for `lwExpSim_equivs` (`LWExpSim.lean:691`), `LGraph.counters_relabel_equiv` (`LWVocab.lean:2114`), `lwSplit_map` (`LWExpSim.lean:60`), `lvl1_split_last` (`LWLvl1.lean:4220`), the merged `lw_*`/`gg_*`/`lanlw_*` counters and `open private`. **Split if a file passes 1,700 at 1b mid-way:** Lemma E and the `BAsim'` assembly (C3 + C4, 1,015) to `Graph/BASim3.lean`; it is not a sole writable file today, so the dispatcher decides (recommended: name it now). Not a BLOCKED.

### 2. (iii) Lemma E, proof plan (audit item 2)
**Proved form E\*:** for a stage-1 output Q = T'_S of a term T at a normal P (every term except macro stage 2), if Q identifies two distinct atoms of P then `ord P < ord Q ∨ nExt Q < nExt P`. `BAExtraGood` follows: `extraB T'` (a solid edge of P between two atoms of P whose ends T' puts in one atom) is an identification.
- **(E1) counter calculus (one generic lemma).** T0 = T with every edge circled, S ⊆ uncircled edges (j = |S|). `nS Q = nS T0 − j`, `nW Q = nW T0`, the atoms of Q are those of T0 plus the M-dots of S, `#atoms = nExt + nA` (`BAWeightOp_nExt_add_nA`), a merge loses one atom: `nA Q = nA T0 − κ`, `nExt Q = nExt T0 − λ`, `κ + λ` = rank of S in the atom graph of T0. Hence `ord Q = ord P + raw(T) − j + 2κ` (`raw = ord T0 − ord P`; the formula of the `lanlw_scalingOrderG` docstring), `nExt Q = nExt T0 − λ`.
- **(E2) merged inputs:** `raw` = `lw_counters` (1), `gg_counters`/`gg_raw` (1; `A1`: `2κ_f`), `lanlw_ord` (1); `nExt T0 ≤ nExt P` = `lw_mono`, `gg_mono` (`BAGGOp_Mono`), and for `L1` the same `BAWeightOp_mono_aux` (new, ≈ 30 lines).
- **(E3) through `packMerge`/`outsT`:** T' ∈ `splitG T` is normal (every solid edge circled, no `=`-dot: `BAWeightOp_ext_normal`), so `Q.g = T'.merge` has the counters of T' (`BAWeightOp_packMerge_counters`, private, `open private`); new (≈ 50 lines): the classes of the empty `=` relation are points, so `Q.g.nExt = T'.nExt` and the atoms of Q are those of T'; this also gives the vertex equivalence used in item 3.
- **(E4) where an identification comes from.** The fixed M-dots join two old vertices only in `A1` (and `X.d4`, tag macroB, not in E); every other identification is made by an M-split edge (output below: columns `fixed`, `split`).
- **(E5) arithmetic per family** (omega on `j, κ, λ`; `jmax` = number of uncircled edges): `L1, A4, X.L1` (jmax 1) and `lw4.D` have min Δord 2, `A5, B2, X.d1` (jmax 2) and `BD` min 1: ord rises. Derivative terms with α in the atom of x (`lanlwD` = `LD`, `X.LD`, `W.D`, `lw2.D`; `AD`) have three uncircled edges `G_{uβ}, G_{αv}, G_{βy}`: 8 masks (pattern of `BAWeightOp_split3`, `BAWeightOp_D4_split`); j = 2 merges β's singleton (κ ≥ 1, as in `lanlw_scalingOrderG`, `gg_scalingOrderG`): Δord ≥ 1; the only equality cases are listed below and all have λ ≥ 1 (nExt falls). `A1`: `ord A1 = ord P + 2κ_f` (`gg_raw`); κ_f = 0 with two distinct atoms means both external, so nExt falls (`BAGGOp_kappa`, `BAGGOp_addM_cnt_all`, new ≈ 25 lines).
- **(E6) the `W − 1` terms (`lw4`, `gg4`).** `ba_W_sub_one` is not used, only the term lists: their new atoms {y2, α} / {w, α} are not x's atom (`BAWeightOp.lean:71-76`, `BAGGOp.lean:85-92`), the min Δord over identifications is 2 (`lw4.D`), 1 (`B2`), 1 (`BD`): ord rises, no nExt route.
```
$ python3 lemE_summary.py     # exhaustive templates of lemE.py (all coincidences x atom merges x external flags x edge colour); only the rows with an identification
family          outputs     id  merge fixed split jmax minraw mindord(split) E*viol
edge:L1              228     228    114     0   114    1      1             2      0
edge:LD              896     896    416     0   416    3      1             0      0
gg:A1                680     680    420   420     0    0      0             -      0
gg:A4               1360    1360    680     0   680    1      1             2      0
gg:A5               2720    2720    420     0   420    2      1             1      0
gg:AD               5376    5376   2608     0  2608    3      1             0      0
gg:B2               2720    2720    420     0   420    2      1             1      0
gg:BD               5376    5376    992     0   992    3      1             1      0
ggSplit:X.L1        1696    1696    848     0   848    1      1             2      0
ggSplit:X.LD        6720    6720   3124     0  3124    3      1             0      0
ggSplit:X.d1        3392    3392    516     0   516    2      1             1      0
ggSplit:X.d4         848     848    516   516     0    0      0             -      0
weight:lw2.D         672     672    256     0   256    3      1             0      0
weight:lw4.D         672     672     48     0    48    3      1             2      0
within:W.D           960     960    304     0   304    3      1             0      0
no identification of P-atoms at all (merge = 0): gg:A2, gg:A3, gg:B1, ggSplit:X.d2, ggSplit:X.d3, weight:lw2.leaf, weight:lw4.leaf, within:W.first; E*viol total 0
$ python3 lemE_eq.py          # equality cases ord Q = ord P with an identification by split edges
equality cases (j, kappa, lambda): count {(1, 0, 1): 26, (3, 1, 1): 92, (3, 1, 2): 4} | min lambda 1 | families ['AD', 'LD', 'W.D', 'X.LD', 'lw2.D']
```
`id` = identity of (E1) and `nExt T0 ≤ nExt P` on all outputs; `E*viol` = identifications with `ord Q ≤ ord P` and `nExt Q ≥ nExt P`: 0 in every family (mutants caught: `mut.py`, `mut2.py` of (a)).

### 3. (ii) relabelling per term kind (audit item 3)
**Common proof (one lemma + one rule).** *LemQ (B3):* T' = T_S, Hc = the band term at P.img with the dot choice c, φ the collapse of the vertices of T onto those of the band term (old v ↦ `vmap v`, new vertices as in the table). If (a) the solid, waved and ×-dot lists of Hc are the φ-images of those of T' and of img P (up to order, circles read as "is a loop") and (b) `φu ~_Hc φv ⟺ u ~_atom(T') v`, then ψ = `Hc.vmap ∘ φ` has the atom classes as fibres and `lwExpSim_equivs` (`LWExpSim.lean:691`, generalized from `Fin A ⊕ Fin B` to the band's `ExtCls ⊕ IntCls`) gives `eE, eI`; the list clauses of `BAEquiv` are `simp`, as in `img95_equiv_gen` (`BAAtomic.lean:805`). *Choice rule (B5):* `c(S)` = `=` on exactly the `aPairs` whose two ends lie in one atom of T'_S, `×` on the others, `(1,[])` on every `bEdge` (the ×-dot of a consumed edge), then `lwSplitLoops`: a loop edge not in S keeps its circle, an edge of S becomes the coefficient m. A non-extra output gives a consistent term (an inconsistency is an identification of the ends of a ×-dot of img P, i.e. of two atoms of P joined by a P-edge); so the band has the output, and `BAMatch` is the inclusion BA → band (the band has more terms: its `=` branch has no BA twin). **Selector rule (per output, exhaustive):** `A2` uses `swap` = (c,t) = (0,1) with p' := q, every other term `nat` = (0,0) (kinds other than `gg`: `match_exh.py` of (a″), `nat` is in every selector set of every step):
```
$ python3 selrule.py      # exhaustive gg templates with the step hypotheses
band-tagged outputs matched by the rule step / band-tagged, per term: A1 59/59  A2 99/99  A3 99/99  A4 99/99  A5 356/356  AD 482/482  B1 198/198  B2 356/356  BD 708/708
$ python3 partner.py | python3 partner_cond.py    # band term matching the non-extra outputs, by frequency (seed 77, 250 parents per kind)
edge     L1>E.T1  LD>E.D/E.P5/E.P3/E.P4/E.P6
gg       A1>R2  A2>R2  A3>R2  A4>R3/R5  A5>R5/R3/R7  AD>R7/R5  B1>R4/R6/R8  B2>R6/R4/R8  BD>R8/R4/R6
ggSplit  X.L1>R3/R5  X.LD>R7  X.d1>R5/R3/R7  X.d2>R5  X.d3>R5/R7
weight   lw2.D>T3  lw2.leaf>T1  lw4.D>T4  lw4.leaf>T2
within   W.D>T3  W.first>T1
```
| BA term | band term at P.img (selector) | φ on the new vertices (x̄ = vmap x, n_i = i-th new band vertex) |
|---|---|---|
| lw2.leaf, lw2.D, W.first, W.D (weight, within stage 1) | owxT1, owxT3(q̄) (nat) | α ↦ x̄, β ↦ n0 |
| lw4.leaf, lw4.D | owxT2, owxT4(q̄) (nat) | z ↦ x̄, y2 and α ↦ n0, β ↦ n1 |
| L1, LD (edge) | `lwSymmOe1xOwx` = owxT1 at the frame; `Oe1xDs`: D, or P5/P3 (q̄ red out-edge at x̄), P6/P4 (q̄ blue in-edge at x̄) (nat) | α ↦ x̄, β ↦ n0 |
| A1; A3 / A2 | R2, `=` branch of {ȳ', ȳ} with the loop dropped (m) (nat); R2, × branch (nat / swap) | u ↦ x̄, β ↦ ȳ = ȳ'; β ↦ ȳ / ȳ' |
| A4, A5, AD | R3 (or R5), R5 (or R3, R7), R7 (or R5) (nat) | α ↦ x̄, β ↦ n0 |
| B1, B2, BD | R4, R6, R8 (or the others at coincidences) (nat) | u ↦ x̄, w and α ↦ n0, β ↦ n1 |
| X.L1, X.LD, X.d1 (ggSplit stage 1, x̄ = class of a = class of a') | R3 or R5, R7, R5 (nat) | α ↦ x̄, β ↦ n0 |

**Band hypotheses at P.img (B4), from the BA hypotheses of the constructor;** `P.img.g = P.g.img.g`, `BAAtomic_img_solid` (`BAAtomic.lean:269`), `lwSplit_map` for `hp, hq`, `BAAtomic_vmap_eq_iff`/`BAAtomic_promoteC_vmap_eq_sameAtom` for equalities of images, and `lvl1SolidAt (vmap v) = (atEdges v).map BAAtomic_fm` (`BAAtomic_solidAt`), `lvl1ChargeAt (vmap v) = atCharge v` (`BAAtomic_charge`), `BAAtomic_exists_inr_vmap` (every internal class is `vmap (inr b)`):
- weight, within → `LocStep.weight`: `hx` from `p.1 = ⟨true,true,x,y⟩` with `sameAtom x y` (image edge `⟨true, true && true, x̄, x̄⟩`); `x ≠ y` is allowed.
- edge → `LocStep.edge`: `x'` from `intAtom x` (`BAAtomic_vmap_isRight_iff`), `hv` from `hv`, `hwf` from `hwf` (every image edge has distinct ends), `hbad` from `hbad` through `solidAt`/`charge`.
- gg, ggSplit → `LocStep.gg`: `hy` from `hwf`, `hp1, hq1` at (0,0) (at (0,1) for `A2`: `lwSymmTwistS 0 1` is the transpose), `hnb` from `hnb`; ggSplit with `vmap a = vmap a'` (`sameAtom`).

### 4. Item 2: `BAsim'` from `BAMatch` + `BAExtraGood` (audit item 4)
Case on the tag of `Q` (`BAFrameStepT_untag`): `band` → `BAMatch`, T := P, `Q0 := R`, `Q0.baInv = Q.img.baInv = Q.baInv` by L-inv and `BAimg_holds`; `e1`, `e2` → `BAExtraGood`; `macroA`, `macroB` stage 2 → via the transfer graph; `X.d2`–`X.d4` → below. Lemmas (all new, in `BASim2`): **(M1)** `T_tr := ⟨P.E', P.I' ⊕ Fin 2, P.ext, P.ext_surj, tr⟩`; `P.outsT g Ts = T_tr.outsT g Ts` by `rfl` (`outsT` reads only `E'` and `ext`); the stage-2 outputs are those of `BAFrameStepT.weight T_tr pp` (macro a) or `.gg T_tr p2 q2` (macro b): `pp ∈ lwSplit T_tr.g.solid` and `p2`, `q2` by `lvl1_split_last` (`tr.solid = rest ++ [e]`, `owxExt` appends), `hwf, hint, hnb` at `T_tr` from those of P (consumed `p, q` leave the atom of a with no edge; `β` is a singleton with two edges, charge 0). **(M2)** `T_tr.g.Normal` (`BAWeightOp_ext_normal`). **(M3)** `T_tr.baInv = P.baInv` (counters as `lw_counters`; nExt, loops, pairs). **(M4)** `BAMatch`/`BAExtraGood` at `T_tr` then give the first disjunct with T := T_tr, or the others since `ord`, `nExt` of `T_tr` are those of P. **(L-inv)** `R.BAEquiv S → R.baInv = S.baInv` (`LGraph.counters_relabel_equiv`, loops/pairs/`nM` under `Equiv`: reads only counts, `adj`); same for `BAEquivC`.
```
$ python3 trhyp.py        # exhaustive templates, steps with the real hypotheses
within   steps 122 | M1 frame step at tr 122 | M2 tr normal 122 | M3 baInv(tr)=baInv(P) 122
ggSplit  steps  99 | M1 frame step at tr  99 | M2 tr normal  99 | M3 baInv(tr)=baInv(P)  99
$ python3 d4check.py      # X.d2, X.d3, X.d4 of ggSplit, same templates
X.d2 848 outputs, ord rises 848 | X.d3 848 outputs, ord rises 848
X.d4 848 outputs = ord rises 387 + (ord equal, nExt falls) 129 + (ord equal, nExt equal) 332 ; of the last: [y]=[y'] same atom 332, inv(Q) = inv of a band R2 output at img P 332
min Delta ord: {('X.d2',): 1, ('X.d3',): 1, ('X.d4',): 0}
```
**`X.d2`, `X.d3`:** ΔnS = −1, ΔnW = +1, ΔnA ≤ 0 (no new atom) ⇒ `ord Q ≥ ord P + 1` (nA bound as `BAWeightOp_nA_le`). **`X.d4`** = `A1` with `S` in place of `S⁺` (the ends a, a' of one atom in place of x, x): `ord Q = ord P + 2κ`, κ = `BAGGOp_kappa Γ y' y`; κ ≥ 1: ord rises; κ = 0 and `[y] ≠ [y']`: both external, nExt falls; κ = 0, `[y] = [y']`: `inv Q` is that of a band R2 output (A1's partner; waved colour `S` against `S⁺`, so `BAEquivC` or direct counters, not `BAEquiv`): 332 of 848, all matched.

### 5. Item 1 at the `BALocStep` level (audit item 5)
**R1 delivers the frame level only**, as probed: the twisted `BALocStep` is `BAMatch` at the normal graph `P.twist c t` (`ba_lvl1StepGood_of_sim` consumes `BAsim` at `P.twist c t`, T2395 probe 323). The level of `BASimC` (L3b4′), whose band step is at `img P` itself, belongs to the rows that own the twisted forms and the BA `LocStep` (T2395 §6: L3a2, L3a3), not to R1; its pin, to be compiled there against `main` (`BASymm1` merged):
```
def BAMatchTw (m : ℂ) : Prop := ∀ {E} (c t : Bool) (P : BAPGraph E) LT, BAFrameStepT (P.twist c t) LT → P.g.Normal →
  ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L', LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv (Q.twist c t).img      -- from BAMatch at P.twist c t
```
Needs: `BAGraph.img_twist` (`(Γ.twist c t).img` and `lwSymmTwistG c t Γ.img` are `BAEquiv` after relabelling; atoms are `BASymm1_twist_atom`), `BAEquiv.twist` (map of a perm; waved reversal is inside `sameRev`), and the band's `LocStep m P' L'` at selector (c,t) = twist-back of the (0,0) step at `twist P'`, which needs `LGraph.partition (twist Γ) ≅ (partition Γ).map twist`; neither is on `main` (the row owner is the dispatcher's decision; the ticket's item 1, "for each step `BALocStep P outs`", is met at the frame level only):
```
$ cd RBM3D && git rev-parse --short HEAD && grep -rln "partition_twist\|BAPGraph.twist\|BALocStep\|img_twist" RBM3D RBM3D.lean; echo "grep exit=$? (1 = no match)"
46120c3
grep exit=1 (1 = no match)
```

### 6. Item 3: per output, `BASimC` and `baStep_of_simC` (audit item 6)
Pseudo-Lean (T2397 probe 137 with `∃ L'` moved inside `∀ Q`; `P'` stays per step, for `gg` the band step is per output):
```
def BASimC' (m : ℂ) (T : BTStep) : Prop := ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), P'.g.Normal ∧ LGraph.CircIffLoop P'.g ∧
  (∀ far k, locCostGeA far k P → P'.LocCostGe far k) ∧ ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L', LocStep m P' L' ∧ ∃ R ∈ L',
    ∀ far k, R.LocCostGe far k → locCostGeA far k Q
-- baStep_of_simC': the proof of T2397 probe 137 with `obtain ⟨L', hst, R, hR', hRQ⟩ := hR Q hmem`; the rest is unchanged
```
From R1: `P' := P.img` (`BAGraph.img_normal`, `BAAtomic.lean:308`), the `∃ L', ∃ R` is `BAMatch` (per output; for `weight, within, edge, ggSplit` one `nat` step serves every output); `BAEquiv` is what `LGraph.scost_perm` (`LocalRegular6a.lean:309`) and `scost_relabel` read (L3b4′).

**Verdict (a′):** items 1-6 addressed; no probe statement changes. T1 `BAMatch`, T2 `BAsim'`, T3 per output for `gg` (`A2` swap), T4 Lemma E: PASS. Decisions for the dispatcher (not BLOCKED): a third file `Graph/BASim3.lean` (predicted total 3,450 vs ticket 2,000-2,400; both named files fit at central), and the owner row of `BAMatchTw` (item 5).

## (b) Script output — stage 1b, rule (H) rerun under Amend 1 — Mon Oct 12 03:55:49 UTC 2026

**Result (the ticket's first line).** Matching **per output**: `baMatch_holds : BAMatch m` gives every `band`-tagged output `Q` of a `BAFrameStepT` at a normal `P` a band step `LocStep m P.img L'` and `R ∈ L'` with `R.BAEquiv Q.img` (`∃ L'` inside `∀ Q`; at `gg` the mirror term `A2` needs the swapped selector: `BASim_matchLT_gg` uses `hnat` and `hswap`). Simulation: **`BAsim' m`** (`baSim'_holds`), not the literal `BAsim m` ((a) T2: macro outputs are matched at the image of the transfer graph). **No failing band shape**: `baMatch_holds` covers all five constructors of `BAFrameStepT`. Item 1 at frame level; `BAMatchTw` → L3b4′ (Amend 1). **Lines per file: BASim 1,979 · BASim2 1,928 · BASim3 1,962** (total 5,869; stop line 2,000 per file, none over).

```
$ date -u; cd RBM3D-wt/T2423; git log -1 --format="%h %s"; git status --short | wc -l; git diff --stat 796a2dc HEAD -- RBM3D/Probe/T2423Pins.lean | wc -l; git diff --stat main...t/T2423 | cat
Mon Oct 12 03:55:49 UTC 2026
eac746f T2423: unpinned helpers carry the stem BASim_ (rule E); baMatch_holds and baExtraGood_holds instances at within, weight, edge
       0
       0
 RBM3D/Graph/BASim.lean     | 1979 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BASim2.lean    | 1928 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BASim3.lean    | 1962 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2423Pins.lean |  352 ++++++++
 4 files changed, 6221 insertions(+)
$ wc -l RBM3D/Graph/BASim{,2,3}.lean; per file: grep -cE "sorry|admit|native_decide|^axiom"; grep -c "RBM2D\|RBM1D" (ports); grep -c "decide +kernel"
    1979 RBM3D/Graph/BASim.lean
    1928 RBM3D/Graph/BASim2.lean
    1962 RBM3D/Graph/BASim3.lean
    5869 total
BASim: sorry-like 0, RBM1D/RBM2D mentions 0, decide +kernel 1
BASim2: sorry-like 0, RBM1D/RBM2D mentions 0, decide +kernel 0
BASim3: sorry-like 0, RBM1D/RBM2D mentions 0, decide +kernel 12
$ grep -nE "Built RBM3D.Graph.BASim|Build completed" build2.out   # first `lake build RBM3D.Graph.BASim RBM3D.Graph.BASim2 RBM3D.Graph.BASim3` after the last source change, started 03:19:58 UTC
1258:✔ [3819/3821] Built RBM3D.Graph.BASim (8.7s)
1259:✔ [3820/3821] Built RBM3D.Graph.BASim2 (9.2s)
1260:✔ [3821/3821] Built RBM3D.Graph.BASim3 (34s)
1261:Build completed successfully (3821 jobs).
$ lake build RBM3D.Graph.BASim RBM3D.Graph.BASim2 RBM3D.Graph.BASim3 2>&1 | tail -1   # re-run, up to date
Build completed successfully (3821 jobs).
$ lake build 2>&1 | tail -1   # full library on the branch, 03:26:50-03:27:56 UTC, exit 0; RBM3D.lean is untouched, so the audit inside it does not see the three modules (next blocks)
Build completed successfully (4242 jobs).
$ lake env lean docs/tickets/checks/T2423-check.lean > check.out 2>&1; echo exit=$?; grep -ci error check.out   # the ticket check file, on the branch
exit=0
0
$ lake env lean axioms3.lean   # #print axioms of the 4 targets and the 2 pins of Amend 1 O4, then every declaration of the three modules, private ones included
'RBM.Graph.baFrameStepT_untag_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baMatch_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baExtraGood_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baSim'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.PGraph.BAEquivC' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAPGraph.twist' depends on axioms: [propext, Classical.choice, Quot.sound]
declarations (incl. private) in BASim, BASim2, BASim3: 551 (theorems 358); with an axiom outside propext/Classical.choice/Quot.sound: 0 []
$ lake env lean exax.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"   # the 5 `example`s of the files, copied as ex1..ex5
5
```
```
$ python3 extract.py "BAMatch,BAExtraGood,BAFrameStepT_untag,BAsim',baFrameStepT_untag_holds,baMatch_holds,baExtraGood_holds,baSim'_holds" RBM3D/Graph/BASim.lean RBM3D/Graph/BASim3.lean   # statements, extracted from the files
BASim.lean:199
def BAMatch (m : ℂ) : Prop := ∀ {E : Type} (P : BAPGraph E) (LT : List (BAShape × BAPGraph E)), BAFrameStepT P LT → P.g.Normal → ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L' : List
    (PGraph E), LocStep m P.img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img
BASim.lean:203
def BAExtraGood : Prop := ∀ {E : Type} (P : BAPGraph E) (LT : List (BAShape × BAPGraph E)), BAFrameStepT P LT → P.g.Normal → ∀ Q, (BAShape.e1, Q) ∈ LT ∨ (BAShape.e2, Q) ∈ LT →
    P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt
BASim.lean:206
def BAFrameStepT_untag : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs ↔ ∃ LT, BAFrameStepT P LT ∧ outs = LT.map Prod.snd
BASim.lean:222
def BAsim' (m : ℂ) : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal → ∀ Q ∈ outs, (∃ (T : BAPGraph E) (L' : List (PGraph
    E)), T.g.Normal ∧ T.baInv = P.baInv ∧ LocStep m T.img L' ∧ ∃ Q0 ∈ L', Q0.baInv = Q.baInv) ∨ P.g.scalingOrder < Q.g.scalingOrder ∨ Q.g.nExt < P.g.nExt
BASim.lean:281
theorem baFrameStepT_untag_holds : BAFrameStepT_untag := by ...
BASim3.lean:218
theorem baMatch_holds (m : ℂ) : BAMatch m := by ...
BASim3.lean:658
theorem baExtraGood_holds : BAExtraGood := by ...
BASim3.lean:1830
theorem baSim'_holds (m : ℂ) : BAsim' m := by ...
$ python3 pindiff.py RBM3D/Probe/T2423Pins.lean RBM3D/Graph/BASim.lean RBM3D/Graph/BAScost.lean | grep -E "^(BAShape|BTStep|untag) |^identical [0-9]"   # the 24 pinned declarations of the probe against the final files (whitespace-normalized text); BAShape, BTStep, untag are the merged ones (BAScost.lean:163-169, O2)
BAShape                  probe  74 | BAScost.lean:163   identical-after-whitespace-normalization: True
BTStep                   probe  76 | BAScost.lean:167   identical-after-whitespace-normalization: True
untag                    probe  77 | BAScost.lean:169   identical-after-whitespace-normalization: True
identical 24 of 24
$ python3 t2395diff.py   # BAFrameStep, outsOf, withinOuts, splitOuts, BAsim, BAPGraph.twist of BASim.lean against t/T2395:RBM3D/Probe/T2395Pins.lean (the design pins), line numbers there
identical 6 of 6 BAPGraph.outsOf 154 BAPGraph.withinOuts 160 BAPGraph.splitOuts 168 BAFrameStep 182 BAsim 263 BAPGraph.twist 157
$ python3 examples.py RBM3D/Graph/BASim{,2,3}.lean | cut -c1-200   # the compiled instances: first line of each `example` (BASim3.lean:1938 has no stated type: its text follows)
BASim.lean:1971: 4 lines
  example : BAFrameStep (baPG baPA) ggF ∧ ggF.length = 31 ∧ ∃ LT, BAFrameStepT (baPG baPA) LT ∧ ggF = LT.map Prod.snd
BASim3.lean:1910: 4 lines
  example : ((ggFT.map Prod.fst).count BAShape.band = 23 ∧ (ggFT.map Prod.fst).count BAShape.e2 = 8 ∧ ggFT.length = 31) ∧ ((((baPG baPC).splitOutsT pC qC 0).map Prod.fst).count
BASim3.lean:1915: 11 lines
  example (m : ℂ) : (∃ Q, (BAShape.band, Q) ∈ ggFT ∧ ∃ L' : List (PGraph (Fin 2)), LocStep m (baPG baPA).img L' ∧ ∃ R ∈ L', R.BAEquiv Q.img) ∧ (∃ Q, (BAShape.e2, Q) ∈ ggFT ∧
BASim3.lean:1927: 9 lines
  theorem inst_match_extra (m : ℂ) {E : Type} (P : BAPGraph E) (LT : List (BAShape × BAPGraph E)) (h : BAFrameStepT P LT) (hN : P.g.Normal) (hb : BAShape.band ∈ LT.map Prod.fst)
BASim3.lean:1938: 3 lines
  example (m : ℂ)
BASim3.lean:1942: 16 lines
  example (m : ℂ) : (∃ Q ∈ ggF, BASim_Goal m (baPG baPA) Q) ∧ (∃ Q ∈ (baPG baPB).withinOuts pB, BASim_Goal m (baPG baPB) Q) ∧ (∃ Q ∈ (baPG baPC).splitOuts pC qC 0, BASim_Goal m
example (m : ℂ) := And.intro (inst_match_extra m _ _ hTB (by decide) (by decide +kernel) (Or.inr (by decide +kernel)))
  (And.intro (inst_match_extra m _ _ hTW (by decide) (by decide +kernel) (Or.inr (by decide +kernel)))
    (inst_match_extra m _ _ hTE (by decide) (by decide +kernel) (Or.inl (by decide +kernel))))
```
```
$ git rev-parse --short main; python3 clash.py main   # the 382 public declarations of the three files against the declaration lines of main
4b3bb8a
ref main: declaration lines scanned 25707; new public declarations 382; same declared (dotted) name on main: 0
same final component on main (informational): 6
$ python3 names.py RBM3D/Graph/BASim{,2,3}.lean > names.tsv; python3 stem.py names.tsv   # rule (E), unpinned helpers carry the stem
public declarations 382: stem (BASim*, namespace BASimInst) 355; pins of the probe 21; pins of Amend 1 O4 2; endpoint theorems 4; none of these 0 []
$ grep -c "BAShape\.s1\|\.s1\b" RBM3D/Graph/BASim{,2,3}.lean   # the tag s1 is never assigned (a) F1
RBM3D/Graph/BASim.lean:0
RBM3D/Graph/BASim2.lean:0
RBM3D/Graph/BASim3.lean:0
$ for b in $(git branch --no-merged main --list "t/*"); do git grep -l -E "(def|theorem|inductive|abbrev|structure) (BAPGraph.twist|PGraph.BAEquivC|PGraph.BAEquiv|BAMatch|BAExtraGood|BAFrameStep|BAFrameStepT|BAsim|BAsim'|BAPGraph.baInv|PGraph.baInv|BAPGraph.outsOf|BAPGraph.outsT|WEdge.sameRev|DEdge.sameU|BAPGraph.outOf|WEdge.sameEnds)( |$)" $b -- RBM3D ":!RBM3D/Probe" ":!RBM3D/Graph/BASim*.lean"; done
branches scanned: 391; branches with a match: 0
$ merge simulation: cp -c -R <main>/.lake/build/lib/lean combo2/lib; cp -c <worktree>/.lake/build/lib/lean/RBM3D/Graph/BASim{,2,3}.olean combo2/lib/RBM3D/Graph/; LEAN_PATH=combo2/lib:<packages> lean merge_sim.lean   # merge_sim.lean = import RBM3D; import RBM3D.Graph.BASim3; #assert_rbm_axioms   (main 4b3bb8a: RBM3D.olean built 20:33:42 PDT, TwistAvgB.olean present; run 03:37:27-03:38:22 UTC)
exit=0   (merge_sim2.out: 0 lines with 'error')
axiom audit: 12733 theorems, 4007 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
```

**Narrative** (facts from the files and the outputs above)
- **Where.** `baFrameStepT_untag_holds` `BASim.lean:281`; `baMatch_holds` `BASim3.lean:218` (engine `BASim_match` `BASim.lean:1330`; kinds `BASim_matchLT_weight/_within/_edge/_gg` `BASim2.lean:220/281/755/1583`, `BASim_matchLT_ggSplit` `BASim3.lean:168`); `baExtraGood_holds` `BASim3.lean:658` (`BASim_extra_E` `:334`, families `BASim_fam_*` `:490-:634`); `baSim'_holds` `BASim3.lean:1830` (`BASim_goal_of_step` `:1661`, `BASim_macroA` `:1688`, `BASim_macroB1` `:1786` (terms `d2, d3, d4`), `BASim_macroB2` `:1704` (stage 2)). Pins of Amend 1 O4: `PGraph.BAEquivC` `BASim.lean:234`, `BAPGraph.twist` `:249`, link `PGraph.BASim_BAEquiv_toC` `:245`.
- **Layout** (`grep -n "^section "`). BASim: frame vocabulary and tags 49-163, pins 166-252, untag 254-316, matching engine (classes of the image, flags, lists, `BASim_match`, `BASimExt`) 319-1583, weight step at the image and invariants 1584-1959, instance 1961. BASim2: weight, within, edge 41-783, gg 785-1625, atom lemmas 1626-1928. BASim3: ggSplit stage 1 and `baMatch_holds` 48-228, Lemma E 229-706, conservative extensions, transfer-graph invariants, `d`-terms 707-1634, macro steps and `baSim'_holds` 1635-1876, instances 1877-1962. Landed total 5,869 against (a′) §1 predicted 3,450 (BASim 1,680 / BASim2 755 / BASim3 1,015) and the ticket's 2,000-2,400; margins to the stop line 21 / 72 / 38 lines.
- **Lemma E** is proved for the pin `BAExtraGood` (extra = `BAGraph.extraB`: a solid edge of `P` joins two atoms of `P` that `T'` puts in one atom), by one generic lemma, not by the counter calculus of (a′) §2: `BASim_extra_E` joins the two atoms by an `M`-dot (`Γ̃ = Γ.addM d`), takes the merged order bounds at `Γ̃` as `hmono` (`lw_scalingOrderG`, `lanlw_scalingOrderG`, `gg_scalingOrderG`, `BAExpandWOrd_ext_ge`), and concludes `ord` rises if one of the two atoms is internal, `nExt` falls if both contain an external vertex. The `(M⁺S⁺)` parts and the `W − 1` terms are the families `BASim_fam_lw4` `:506`, `BASim_fam_gg4` `:556`. **E\*** of (a′) §2 (every identification of two atoms of `P`, whatever joins them) is not a Lean statement here.
- **`BAsim'`.** Tags `band`/`e1`/`e2` at `P` itself (`BASim_goal_of_step`, `T = P`); stage 2 of macro (a) and (b) at the transfer graph `T = BASim_Ttr P g`, `g` = `BAGraph.BAScost_trA`/`trB` of the merged `Graph/BAScost.lean`, with `T.baInv = P.baInv` (`BASim_inv_trA` `:939`, `BASim_trB_facts` `:1036`); the terms `d2, d3, d4` by `BASim_ord_d23` `:1446`, `BASim_d4` `:1491`, `BASim_inv_d4_A1` `:1587`. In the `band` cases the invariants of `Q0 = R` come from `BASim_baInv_of_equiv` and `BASim_img_baInv` (`BASim.lean:1903`, `:1946`), which uses R0's `BAimg_holds`.
- **Merged vocabulary (O2).** `BAShape`, `BTStep`, `untag` are imported from `Graph/BAScost.lean:163-169`; script above: identical to the probe's, so there is no difference to list. `BAFrameStep`, `outsOf`, `withinOuts`, `splitOuts`, the tags and `BAFrameStepT` are defined in `BASim.lean` (not on `main`); the probe's 24 pins are identical to the final text.
- **Rule (E).** Of 382 public declarations 355 carry the stem (`BASim*`, namespace `BASimInst`), 21 are pins of the probe, 2 of Amend 1 O4, 4 are the endpoint theorems, 0 others; the API lemmas around the pinned definitions (`BASim_sameRev_refl`, `BASim_sameU_refl`, `BASim_BAEquiv_refl`, `BASim_sameRev_sameEnds`, `BASim_BAEquiv_toC`, `BAPGraph.BASim_outsT_map_snd`, `..._outsOf_append`, `..._outsT_append`, `..._withinOutsT_map_snd`, `..._splitOutsT_map_snd`, `BAPGraph.BASim_outOf`, `WEdge.BASim_sameEnds`) carry the stem.
- **Instances.** Every target has a compiled nonempty instance with all deterministic hypotheses discharged by `decide`/`decide +kernel` and explicit membership terms: `baFrameStepT_untag_holds` at the `gg` step at `P_A` (`BASim.lean:1971`); `baMatch_holds` and `baExtraGood_holds` at `gg` (`P_A`) and `ggSplit` (`P_C`) `BASim3.lean:1915`, at `within` (`P_B`), `weight` (`P_W`), `edge` (`P_E`) `:1938` via `inst_match_extra` `:1927`; `baSim'_holds` at all five kinds `:1942`; `P_A`, `P_B`, `P_C` are the data of (a) (ii) (`E = Fin 2`, `I = Fin 3`, `|V| = 5`, `nExt = 2`, atom `{2,3}` with an `M`-dot and a waved edge); `P_W` (`E = Fin 1`, `I = Fin 2`: a self-loop at an internal vertex) and `P_E` (`E = Fin 2`, `I = Fin 1`: an internal vertex of degree 3) are new here. The census `BASim3.lean:1910` (kernel evaluation): `gg` at `P_A` has 31 outputs = 23 `band` + 8 `e2`; `ggSplit` at `P_C` has 48 = 8 `band` + 1 `e1` + 5 `e2` + 34 `macroB`. No hypothesis is left open: the targets carry no external pin.
- **Not touched.** `RBM3D.lean` (the hub adds `import RBM3D.Graph.BASim`, `BASim2`, `BASim3` after the last `import` line at merge, §3 (A) 4); the probe `RBM3D/Probe/T2423Pins.lean` stays on the branch, unchanged since `796a2dc`, and is not merged. No port from RBM1D/RBM2D (the mentions count above is 0 in each file).

## (c) Verified Mathlib/core names used
Script `resolve.lean`: every qualified token written in the three sources, resolved with `Environment.contains` under the namespaces `RBM` and `RBM.Graph`: 175 resolve to Mathlib/core (listed), 134 to RBM3D, 320 are local variables, fields or generated names. None needed to be shown absent.
List.{Forall₂, Forall₂.cons, Forall₂.nil, Perm, Perm.cons, Perm.countP_eq, Perm.of_eq, Perm.refl, Perm.swap, Perm.trans, any_append, any_cons, any_eq_false, any_eq_true, append_assoc, append_nil, cons_append, countP_append, countP_cons, countP_map, count_append, eraseIdx_cons_succ, eraseIdx_cons_zero, eraseIdx_map,
exists_mem_of_length_pos, filter, filterMap_append, filterMap_congr, filterMap_cons, filterMap_map, filter_append, filter_congr, filter_cons, filter_eq_nil_iff, filter_map, filter_nil, flatMap, flatMap_append, flatMap_cons, flatMap_map, flatMap_nil, forall₂_cons, forall₂_map_left_iff, forall₂_map_right_iff, getElem?_cons_succ,
getElem?_cons_zero, getElem?_map, length, length_append, length_cons, length_eq_zero_iff, length_map, length_nil, length_pos_of_mem, length_singleton, map_append, map_congr_left, map_cons, map_filterMap, map_flatMap, map_id, map_id', map_id'', map_map, map_nil, map_subset, mem_append, mem_append_left, mem_append_right, mem_cons,
mem_cons_of_mem, mem_cons_self, mem_filter, mem_flatMap, mem_map, mem_map_of_mem, mem_nil_iff, mem_of_getElem?, mem_of_mem_eraseIdx, mem_of_mem_filter, mem_replicate, mem_singleton, mem_singleton_self, nil_append, not_mem_nil, of_mem_zip, perm_append_comm, perm_append_singleton, perm_iff_count, prod_eq_one, rel_append,
replicate, sum, sum_append, sum_cons, sum_eq_zero, sum_map_add, sum_nil, zip_append, zip_cons_cons, zip_map_left}; Bool.{and_eq_true, and_false, and_self, and_true, cond_false, cond_true, eq_iff_iff, false_and, false_eq_true, false_or, noConfusion, not_eq_true', or_eq_true, true_and, true_eq_false}; Finset.{card_erase_of_mem,
card_image_le, card_image_of_injective, card_le_card, ext, image, image_image, image_injective, image_subset_image, mem_filter, mem_image, mem_image_of_mem, mem_univ}; Sum.{inl, inl.inj, inr, inr.inj, isRight, map, map_id_id, map_inl, map_inr}; Relation.{EqvGen, EqvGen.rel, ReflTransGen, ReflTransGen.cases_head,
ReflTransGen.lift, ReflTransGen.mono, ReflTransGen.refl, ReflTransGen.single}; Equiv.{coe_refl, ofBijective, refl, subtypeEquiv, sumCongr}; Function.{Injective, Surjective, comp_apply, comp_def, injective_id}; Prod.{fst, map, mk.injEq, snd}; Option.{map_eq_some_iff, map_some, some.injEq}; Quotient.{exact, exists_rep, sound};
Classical.{choose, choose_spec}; Fintype.{card, card_congr}; Or.{inl, inr}; And.{intro}; Iff.{rfl}; Subtype.{ext}

## (d) Open issues and paper-delta candidates
**Open issues.**
1. `BAMatchTw` and its three bridges (`BAGraph.img_twist`, `BAEquiv.twist`, `LGraph.partition (twist Γ) ≅ (partition Γ).map twist`) are not in R1 (Amend 1 S1; pseudo-Lean in (a′) §5). L3b4′ states in its 1a whether it consumes `BAMatchTw`, proves it from `BAMatch` at `P.twist c t` and `Graph/BASymm1.lean`, or drops it. `PGraph.BAEquivC` and `BAPGraph.twist` are pinned for it.
2. L3a4 re-proves `ba_lvl1StepGood_of_sim` from `lvl1_step_good` at `T.img` with `BAsim'` (T2397 audit observation 2); `BASim_img_baInv` and R0's `BAimg_holds` give `T.img` its normality and invariants.
3. Only the pin `BAExtraGood` is proved; E\* of (a′) §2 is not. The ticket and Amend 1 do not mention E\*.
4. Margins to the 2,000-line stop line are 21 (BASim), 72 (BASim2), 38 (BASim3); a repair round that adds more needs a fourth file or a move of lines (dispatcher).
5. Merge: the hub adds three `import` lines to `RBM3D.lean`; the simulation above loads `main`'s library and the three modules in one environment (no duplicate name) and passes `#assert_rbm_axioms`; the hub's full `lake build` is the real test.

**Paper-delta candidates** (Lean/paper or Lean/design differences; the dispatcher numbers them).
- `T2423a` (F1 of (a), 1a-audit O3): `BAShape.s1` is never assigned by `BAFrameStepT` (the grep in (b) finds no occurrence in the three files). The BA first sum of `GGGamma` (`A1`) is matched with the band's `R2` `(δ, m)` branch (`BASim_R2_ff`, `BASim2.lean:975`; `BASim_matchLT_gg`); per (a) F1 it is an `e2` output when a parent edge joins the atoms of its two ends. T2395 §1.5 ("the band has no such term") fails at graph level, and `BAShapeLL s1` (`BAScost.lean:174`) read at `T = BAFrameStepT` has no `s1`-tagged output to constrain.
- `T2423b`: the simulation delivered is `BAsim'` (`BASim.lean:222`): the band step is at `T.img` for a normal `T` with `T.baInv = P.baInv` (`T = P`, or the transfer graph of a macro step); T2395 probe 263 `BAsim` (at `P.img`) is not derived (macro outputs).
- `T2423c`: the matching is per output (`BAMatch`: `∃ L'` inside `∀ Q`); `baStep_of_simC` (T2397 probe 137) is restated per output at L3b4′.
- `T2423d`: the relation is `PGraph.BAEquiv` (`BASim.lean:177`: bijections of `E'`, `I'` over `ext`; solid lists up to order; waved up to order and per-edge reversal; `×`-dots as sets; the coefficient is not read) and `PGraph.BAEquivC` (`:234`: also the waved colour not read; its docstring: for L3b4′, where `X.d4` has a waved edge `S` against the band's `S⁺`); the literal equality of packed graphs `BAImgSim` stays withdrawn (T2397 audit D1).
