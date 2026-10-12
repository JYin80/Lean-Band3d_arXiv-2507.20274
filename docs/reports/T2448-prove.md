Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 10:58:35 UTC 2026

### (i) Exponent table (target 5 instance data; the other rows are thresholds the targets read)
| quantity | value | constraint | slack |
|---|---|---|---|
| `p` | `2` (even) | start terms `(BAGraph.ofLGraph (fxyPowGraph p)).partition`; `fxyPowGraph_counters`: `n_S = 3p, n_W = p` | 16 start terms (`BAScost:1513`), script below |
| `c`, `K0`, `d`, `D` | `1/4`, `2`, `3`, `10` | `0 < c` (target 4); `lvl1Cutoff c K0 d D G = ⌈(D + K0·nM(G) + d·(nA-nW)⁺(G))/c⌉` (`LWLvl1:3981`) | `c = 1/4 > 0` |
| cutoff `K` per start term `G = P0` | `40` (nM=0, nA-nW=0), `60` (nM=1, nA-nW=1), `80` (nM=2, nA-nW=2) | `ord P0 < K` (`BAReach` steps only below `K`) | `K - ord P0 ∈ [36, 78]` (script) |
| size exponent (`lvl1_size_le` via `baLvl1LemmaSize_holds`) | `c·K = 10, 15, 20` | `c·K ≥ D + K0·nM + d·(nA-nW)⁺ = 10, 15, 20` | `0` (the ceiling is exact); numeric log2 slack `0, 2.245, 4.49` (script) |
| window | `W = 16, L = 6, d = 3` | `L^d ≤ W^K0`: `216 ≤ 256`; `W^(-d/2) = 1/64 ≤ Ψ ≤ W^(-c) = 1/2` | `256/216`; window nonempty (`d/2 - c = 5/4`) |
| flow point of the identity | `d = 3, L = 4, W = 2`, `(g0P, EP, t0P, m0P)` | `3 ≤ L`; `flowP_data : 0 < t0P ∧ t0P < 1 ∧ BASelf 3 4 g0P EP m0P` (`CouplingWindow:869`) | `L - 3 = 1`; `t0P` interior to `(0,1)` |
| (6) thresholds at `LocStd` outputs | `2p = 4`; `3p = 6` if the external atoms differ | read from `baLocReg6_reach p P0 hP0 hX K Q hQ` (`BAStepS:413`) `.2`, any `K` | outputs have `ord ≥ 4 / 6` (not pinned to `K`), no exponent to close |
| black waved edges | start terms: exactly `p = 2` (script); step: `Δ ≥ 0` | target 4 `p ≤ n_{W,black}`; `ba_nWS_ge` along `BAReach` | `Δ = 0` only for the first three `gg2` terms (new edge `S⁺`, col `true`); `+1` elsewhere |
Black = `col = false` (`!e.col`); `WEdge.map`, `WEdge.transpose` and `WEdge.conj` keep `col` (`LWSymm:93-96`, `LWVocab:415`); the appended coloured (`col = true`) edges are the `bpW true` ones.

### (ii) Nondegenerate instance, black-waved-edge table, consumers
Instance: `p = 2, c = 1/4, K0 = 2, d = 3, D = 10`, data `d = 3, L = 4, W = 2`, `(g0P, EP, t0P, m0P)`, labelling `ℓ0`; start list has 16 terms, none `LocStd`, all with 2 black waved edges. Targets 1, 3, 4 hold at it by the merged names (`baLvl1LemmaSize_holds`, `baLocReg6_reach`, `val_eq_partition`); no `N = 0`, empty list or collapsed window. The only unproved input is the O2R-C3 binder (below), a hypothesis of the instance, not an external limit hypothesis (`BASelf`, `0 < t0P < 1` are `flowP_data`).
Black waved edges, the `waved` list of each output as a map of the input's plus appended edges (`BAGraph.ext` = `owxExt`: `Γ.waved.map (WEdge.map emb) ++ w`, `BAWeightOp:56-59`; `lanlwExt` the same, `BAExpandW:114-118`):
| step / operation | `waved` of the output | new black | lemma |
|---|---|---|---|
| `weight`: `lw2` (leaf, `lanlwD`), `lw4` (leaf, `D`) | mapped parent `++ [bpW false ..]` (`lw4`: `[bpW true .., bpW false ..]`) | +1 | new: `ext`/`lanlwExt` waved, count `≥` (`countP_append`, `countP_map`) |
| `within`: `first`, `lanlwD`, `tr.lw2`, `tr.lw4` | mapped parent `++ [bpW false ..]`; `tr` is an `ext`, `lw2/lw4` on `tr` extend again | +1 | same, composed twice (count `≥` for `tr`, then for `lw2 tr`) |
| `edge`: `lanlwT1`, `lanlwD` | `lanlwExt`: mapped `++ [⟨false,true,α,β⟩]` | +1 | same |
| `gg`: `gg2` terms 1-3 (model `A1..A3`) / terms 4-5 and `lwSplit` terms (`A4, A5, AD`), `gg4` | terms 1-3: mapped `++ [bpW true ..]`; others `++ [bpW false ..]` | 0 / +1 | same (terms 1-3 are the `Δ = 0` row) |
| `ggSplit`: `lanlwT1/D`, `dq` (4), `tr.gg2`, `tr.gg4` | `dq` = `ext`, mapped `++ [bpW false ..]`; `tr.gg2/gg4` extend `tr` | +1 | same |
| `BAPGraph.outsOf` = `partition`: `splitG` | `Δ.waved = Γ.waved` (`splitG_edges`, `BAVocab:697`), `Δ.nW = Γ.nW` | 0 | merged (equality of the list: `rfl` in `splitG`) |
| `packMerge` / `merge` | `Γ.waved.map (WEdge.map vmap)` (`LGraph.merge`, `LWVocab:780`) | 0 | new: `col`-keeping map |
| twist `BAGraph.twist c t` (= `lwSymmTwistG` on the graph) | `waved` mapped by `conj` / `transpose` (col kept) | 0 | band `lwEngine_col_conj`, `_transpose` (public, `LWEngine:475-478`); macro `lwEngine_nws` (`:484`) copied under the stem |
| `BALocStep P outs`: twist, frame step, twist back | composite of the rows above | `≥ 0` | `baStep_nWS`, then `ba_nWS_ge` by `ba_lvl1_induction` |
| start term: `ofLGraph` waved `= fxyPowGraph p` waved, `p` edges `⟨false,true,α_i,β_i⟩` | `splitG`, `merge` keep col | `= p` | `baStart_nWS`: `simp` as `lwEngine_fxy_nWS` |
Scripts (Python, no Lean; model files are copies of `/private/tmp/.../scratchpad/T2446/{model,run,inv,strategy}.py`, the T2423/T2442/T2446 BA model: `lw2/lw4`, `lanlw`, `gg2/gg4`, `withinOuts`, `splitOuts`, `ba_partition`, twists; `black.py` adds `fxy p` and the black count):
```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2448 && python3 black.py
start terms p=2: 16 | black waved edges of each start term: [2] | ord: [(2, 4), (3, 8), (4, 4)]
p=1: start terms 4, black counts [1]
p=2: start terms 16, black counts [2]
p=3: start terms 64, black counts [3]
p=4: start terms 256, black counts [4]
16 runs, K = ord+2 in {4,5,6}: any start LocStd: False | truncated at cap: False | nodes per run min/max: 149 1419 | per-run violations: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
strategy steps by kind over the 16 runs: {'weight': 108, 'gg': 32, 'within': 20}
TOTAL over 16 starts: nodes 10832 checks 10900 violations 0
every BAFrameStep at all 4 twists of random normal parents: steps by kind {'weight': 100290, 'within': 50276, 'edge': 18581, 'gg': 656, 'ggSplit': 62} | violations 0
  edge      term L     min(black(out)-black(parent)) = 1 over 37162 partitioned outputs
  edge      term LD    min(black(out)-black(parent)) = 1 over 359576 partitioned outputs
  gg        term A     min(black(out)-black(parent)) = 0 over 5904 partitioned outputs
  gg        term AD    min(black(out)-black(parent)) = 1 over 2480 partitioned outputs
  gg        term B     min(black(out)-black(parent)) = 1 over 3936 partitioned outputs
  gg        term BD    min(black(out)-black(parent)) = 1 over 2480 partitioned outputs
  ggSplit   term X     min(black(out)-black(parent)) = 1 over 1536 partitioned outputs
  weight    term lw2.D min(black(out)-black(parent)) = 1 over 2294576 partitioned outputs
  weight    term lw2.leaf min(black(out)-black(parent)) = 1 over 100290 partitioned outputs
  weight    term lw4.D min(black(out)-black(parent)) = 1 over 2294576 partitioned outputs
  weight    term lw4.leaf min(black(out)-black(parent)) = 1 over 100290 partitioned outputs
  within    term W     min(black(out)-black(parent)) = 1 over 3601404 partitioned outputs
$ python3 step1.py   # one strategy step from three non-LocStd start terms at p = 2
start  0: LocStd=False black=2 -> case 1a kind weight: 82 outputs, black counts of outputs {3: 82}
start  7: LocStd=False black=2 -> case 1a kind weight: 34 outputs, black counts of outputs {3: 34}
start 15: LocStd=False black=2 -> case 1a kind weight: 18 outputs, black counts of outputs {3: 18}
$ python3 inst.py    # target 4 cutoffs and the size bound on the counters of the 16 start terms (W=16, L=6, d=3, c=1/4, K0=2, D=10)
window: L^d = 216 <= W^K0 = 256 : True | W^(-d/2) = 0.015625 <= Psi <= W^(-c) = 0.5 | 4 <= L: L=6, NeZero ok
  1 start term(s): ord=2 req=D+K0*nM+d*(nA-nW)+=10 K=40 c*K>=req:True ord<K:True log2-slack(size vs W^-D)=0.0
  2 start term(s): ord=2 req=D+K0*nM+d*(nA-nW)+=15 K=60 c*K>=req:True ord<K:True log2-slack(size vs W^-D)=2.245
  1 start term(s): ord=2 req=D+K0*nM+d*(nA-nW)+=20 K=80 c*K>=req:True ord<K:True log2-slack(size vs W^-D)=4.49
  4 start term(s): ord=3 req=D+K0*nM+d*(nA-nW)+=10 K=40 c*K>=req:True ord<K:True log2-slack(size vs W^-D)=0.0
  4 start term(s): ord=3 req=D+K0*nM+d*(nA-nW)+=15 K=60 c*K>=req:True ord<K:True log2-slack(size vs W^-D)=2.245
  4 start term(s): ord=4 req=D+K0*nM+d*(nA-nW)+=10 K=40 c*K>=req:True ord<K:True log2-slack(size vs W^-D)=0.0
counters (nS,nW,nA,nM) seen: [(2, 2, 2, 0), (3, 2, 2, 0), (4, 2, 2, 0), (4, 2, 3, 1), (5, 2, 3, 1), (6, 2, 4, 2)]
min log2 slack over the 16 start terms: 0.000
```

Reading of the script output: all 16 start terms have 2 black waved edges and none is `LocStd`; the strategy from each start to `K = ord P0 + 2` (10,832 nodes, 10,900 output-vs-parent comparisons, kinds `weight`, `within`, `gg`) has 0 violations; every `BAFrameStep` of every kind (including `edge` and `ggSplit`, 62 `ggSplit` steps) at all four twists of random normal parents has 0 violations; the minimum increase is 0 (first three `gg2` terms) and 1 elsewhere. The model checks the `waved` lists only; the Lean statement is the monotonicity of `countP` under the maps and appends of the table.

**Target 3, `obtain` steps (route, no exponent):** (a) `LocStd`, `scalingOrder` from the hypothesis on `fo P0`; `2p ≤ ord`, `3p ≤ ord` by `baLocReg6_reach p P0 hP0 hX K Q hQ` `.2` with `hQ` from conjunct (c); (b) from the hypothesis on `fe P0`; (c) `List.mem_flatMap`; (d) `BAGraph.val_eq_partition` (pathwise), `BALvl1C_integral_comb` (private, copy under the stem) for the partition list and for each `fo P0 ++ fe P0`, per-term identity, and `lvl1_sum_flatMap` (`LWLvl1:3433`) twice with `List.sum_append`. Target 4: `lvl1_choose_list` (`LWLvl1:3811`) on `baLvl1LemmaSize_holds d c hc K0 D P0 (BAGraph.partition_normal _ P0 hP0)`, then target 3; `p ≤ n_{W,black}` by `ba_nWS_ge` (target 2) from the `BAReach` of conjunct (c) and `baStart_nWS`.

**Findings for the dispatcher (none changes a pin):**
1. *Band conjuncts read by the consumers* (stop-rule question of DECISIONS §260 (b)). `LWLocRegConcl` has 5 conjuncts. `lwMoment_expand` reads only conjunct 4, the identity (`LWMoment:273`). `lwMoment_prec_far_r` reads `⟨-, hc2, hc3, -, hc5⟩` (`:1275`): conjunct 2 (error size), conjunct 3 for `Normal` and `Q.g.nM ≤` (`:1281`), conjunct 5 for `LocReg345` and `LocReg6` (`:1288`); conjunct 1, `LocReg1`, `LocReg2` and the `3p` clause of conjunct 5 are not read there. `lw_localregularXP` reads conjunct 3 (`LWProv:1693`). So the consumers do read `LocReg345` of the outputs (items (3)-(5) of the (1)-(5) group). At BA these come from L3b1/L3b2 as `BAReach`-invariants at `Q` reached from `P0 ∈ start`, which conjunct (c) of `BALocRegConcl` supplies (with `P0.g.nM ≤ p`, owed to L3b1); no consumer contract needs them inside `BALocRegConcl`, so I do not read the stop rule as triggered. If the dispatcher reads it otherwise, this is BLOCKED on that decision.
2. *Premise scan (`Test/Axioms.lean:425`) and target 3.* `scanPremises` collects every Prop-valued `RBM` def occurring in the binder types of a public theorem and requires a theorem concluding it. Target 3 as pinned (`T2448_Assemble`, expanded) has `Q.g.LocStd` inside a hypothesis. `BAGraph.LocStd` (`BAAtomic:70`) occurs in no public theorem binder in `RBM3D/Graph/BA*.lean` on `main` (grep: only conclusions, `BAReach`'s constructor, defs and `example`s) and no theorem concludes it, so the scan would list it and `#assert_rbm_axioms` of the full build would fail. Not run (no Lean in 1a). Remedy inside the sole writable file, no pin change: a public instance theorem whose conclusion head is `BAGraph.LocStd` (band precedent `localReg2_inst_Q_locStd`, `LocalRegular2:1941`, `by decide`), checked by `import RBM3D` + `#assert_rbm_axioms` before the merge. `Normal`, `BAReach`, `BAShapeLL` already have producers per the ticket (`partition_normal`, `BALvl1A_reach_refl`, `baShapeLL_s1_tn`).
3. *Binder status (O2R-C3).* `docs/queue/T2447.state` is `proving`; `git log -1 t/T2447` is `1fec089` (= `main` at its release, no commit), so T2447 is not merged now: targets 3, 4 and the target-4 instance carry `T2448_Binder` as first hypothesis; the 1b re-decides at its start.
4. *L4d (T2419) is unread*: `grep -c "BAExpandId|BAG5Identity|baExpandIdentity"` gives 0 in `BALvl1C.lean` and `BAStepS.lean`, 3 in `BALvl1A.lean` (all docstrings, `:35, :97, :230`); the route above names no `BAExpandId` declaration. Drop it from the inputs.
5. Section map (iii) and line prediction (vi) of the ticket are not part of section (a) (CLAUDE.md §4 step 1: exactly (i)-(ii), no size estimates); the 1b report carries them.

### Verdicts
- Target 1 `BALocRegConcl` (def): PASS. Conjuncts (a)-(d) are satisfiable at the instance (start list nonempty, `ord P0 < K`, cutoff exponent closed with slack 0 / 2.245 / 4.49 log2).
- Target 2 `baStep_nWS`, `ba_nWS_ge`, `baStart_nWS`: PASS. No BA frame step, the twist, `splitG` or `merge` lowers the black count (table; 0 violations in the script); a nondegenerate step exists (`weight`, 82 / 34 / 18 outputs, each with 3 black edges).
- Target 3 `baEngine_assemble` (under `T2448_Binder`): PASS, with finding 2 for the 1b (premise scan).
- Target 4 `ba_localregularX` (under `T2448_Binder`): PASS, at `p = 2, c = 1/4, K0 = 2, d = 3, D = 10` and the flow point.
- Target 5 instances: PASS (data above; the binder stays a hypothesis of the target-4 instance while T2447 is unmerged).

## (b) Script output (stage 1b, claude-sonnet-5-5, started Mon Oct 12 10:59:48 UTC 2026)

### Size and binder decision
```
$ wc -l RBM3D/Graph/BAEngine.lean        # stop line 2,000 per file; split threshold 1,500; BAEngine2 not used
     506 RBM3D/Graph/BAEngine.lean
wc -l at the section commits (tool log): 215 (§1), 313 (§2-3), 349 (§4), 487 (§5 instances), 506 (premise producer)
$ cat docs/queue/T2447.state | head -1; git log -1 --format=%h t/T2447; git log -1 --format=%h main     # at 10:59:48 UTC (tool log)
state: proving  |  1fec089 (= main when T2447 was released)  |  main 20917ed;  grep baLocReg6_holds RBM3D: no match
$ same at 11:17:27 UTC:  state: proving | t/T2447 = 9694b7d (unmerged) | main = adb4a19;  git grep baLocReg6_holds main -- RBM3D: no match
```
Binder decision (made once, at the start): **T2447 is not merged**, so targets 3, 4 and the target-4 instance take `(∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN)` as first hypothesis, verbatim from `BAStepS.lean:100` (no new `Prop`, no owed registry line).

### Section map (iii) `LWEngine.lean` -> `RBM3D/Graph/BAEngine.lean` (506 lines; line numbers of the file) and the black-waved-edge table (ii) as written
| `LWEngine` | `BAEngine` |
|---|---|
| `:54-77` `lwEvX`, `LWLocRegConcl` | `lwEvX` dropped (no `m`-tags, `BAExpandId:86-88`); `BALocRegConcl` :220 (band conjunct 5 = (1)-(5) left out, DECISIONS §260 (b); (6) is conjunct (a)) |
| `:79-463` tag algebra, `partitionX` scaling, 13 linearity lemmas, `X`-generators, `LocStepX` | dropped: no BA content |
| `:465-491` `lwEngine_nWS`, `_col_conj`, `_col_transpose`, macro `lwEngine_nws` | `BAEngine_col_conj` :57, `_col_transpose` :60 (re-proved; `LWEngine` not imported), `_twist_nWS` :63; the macro is a `simp` call per lemma |
| `:493-551` `lwEngine_T1..R8_nWS`, `_Ds_nWS` | `_ext_ge` :88, `_lanlwExt_ge` :93, `_lanlwD_ge` :98, `_lanlwT1_ge` :102, `_lanlwD_map_ge` :106, `_lw2_ge` :112, `_lw4_ge` :120, `_gg2_ge` :126, `_gg4_ge` :132, `_lanlwTerms_ge` :138 |
| `:554` `lwEngine_part_nWS` | `_partition_nWS` :70, `_outsOf_nWS` :78 |
| `:560-603` `lwEngine_locStep_nWS`; `:605` `lw_nWS_ge` | `_frame_nWS` :147 (five kinds), `baStep_nWS` :190; `ba_nWS_ge` :201 |
| `:612-723` `lwEngine_exists` (§6 recursion) | dropped: `baLvl1Lemma_holds`, `baLvl1LemmaSize_holds` (L3a5, merged) |
| `:725-762` `lwEngine_assemble`; `:765` `lwEngine_fxy_nWS`; `:771-788` `lw_localregularX` | `baEngine_assemble` :268 (+ `_integrable_pval` :240, `_integral_comb` :255, copies of the private `BALvl1C_*`), `baStart_nWS` :208, `ba_localregularX` :335 (+ `_Spec` :314, `_lists` :326) |
| `:792-934` instances | `BAEngineInst` :417-502; helpers :349-415 (`BAEngine_pL_locStd` :413 = premise producer) |

Table (ii), `waved` of each output = mapped parent `++` appended (colour kept); all lemmas new, `BAEngine_` prefix: `weight` (`lw2`, `lw4`): `_lw2_ge`, `_lw4_ge` over `_ext_ge`, `_lanlwD_ge`; `within` (`first`, `lanlwD`, `tr.lw2`, `tr.lw4`): `_frame_nWS` within case (`_ext_ge` then `_lw2_ge`/`_lw4_ge`); `edge`: `_lanlwTerms_ge`; `gg`: `_gg2_ge`, `_gg4_ge`; `ggSplit` (`lanlwT1/D`, 4 `dq`, `tr.gg2/gg4`): `_frame_nWS` ggSplit case; `splitG` (`Δ.waved = T.waved`, `rfl`), `merge` (`waved.map (WEdge.map vmap)`): `_partition_nWS`; twist (`conj`, `transpose`): `_twist_nWS`.

### Statements of targets 1-4 (extracted from the file by `extract.py`)
```
190: theorem baStep_nWS : ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs →
191:     ∀ Q ∈ outs, P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col) := by
201: theorem ba_nWS_ge : ∀ {E : Type} {K : ℤ} {P Q : BAPGraph E}, BAReach K P Q →
202:     P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col) := by
208: theorem baStart_nWS : ∀ (p : ℕ), ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P0.g.waved.countP (fun e => !e.col) = p := by
220: def BALocRegConcl (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))) : Prop :=
221:   (∀ Q ∈ outs, Q.g.LocStd ∧ 2 * (p : ℤ) ≤ Q.scalingOrder ∧
222:     (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder)) ∧
223:   (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
224:     (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
225:   (∀ Q ∈ outs ++ errs, ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition,
226:     BAReach (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 Q ∧ Q.g.Normal ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder ∧
227:       Q.g.nM ≤ P0.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P0.g.nA : ℤ) - P0.g.nW) ∧
228:   ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
229:     ∀ ℓe : Fin 2 → Idx d L W,
230:       ∫ ω, (BAGraph.ofLGraph (fxyPowGraph p)).val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
231:         ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
268: theorem baEngine_assemble : (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) →
269:   ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (fo fe : BAPGraph (Fin 2) → List (BAPGraph (Fin 2))),
270:     (∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition,
271:       (∀ Q ∈ fo P0, Q.g.LocStd ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder) ∧
272:       (∀ Q ∈ fe P0, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
273:         (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
274:       (∀ Q ∈ fo P0 ++ fe P0, BAReach (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 Q ∧ Q.g.Normal ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder ∧
275:         Q.g.nM ≤ P0.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P0.g.nA : ℤ) - P0.g.nW) ∧
276:       ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
277:         ∀ ℓe : Fin 2 → Idx d L W,
278:           ∫ ω, P0.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
279:             ∫ ω, BAComb.val (fo P0 ++ fe P0) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) →
280:     BALocRegConcl p c K0 d D (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fo)
281:       (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fe) := by
335: theorem ba_localregularX : (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) →
336:   ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
337:     BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col) := by
```

### Pins, builds, axioms, instances
```
$ python3 stmtdiff.py     # pins T2448_* of docs/tickets/checks/T2448-check.lean vs the file, whitespace-normalised, binder expanded, T2448_LocRegConcl renamed
1 BALocRegConcl (signature)        IDENTICAL up to the name
1 BALocRegConcl (body)             IDENTICAL up to the name
2 baStep_nWS                       IDENTICAL up to the name
2 ba_nWS_ge                        IDENTICAL up to the name
2 baStart_nWS                      IDENTICAL up to the name
3 baEngine_assemble                IDENTICAL up to the name
4 ba_localregularX                 IDENTICAL up to the name
$ lake env lean docs/tickets/checks/T2448-check.lean; echo exit $?        -> exit 0
$ lake env lean checkbranch.lean; echo exit $?   # check file + import RBM3D.Graph.BAEngine + 6 examples: T2448_LocRegConcl p c K0 d D outs errs = BALocRegConcl ... := rfl;
#   T2448_StepNWS := baStep_nWS; T2448_NWSGe := ba_nWS_ge; T2448_StartNWS := baStart_nWS; T2448_Binder -> T2448_Assemble := baEngine_assemble; T2448_Binder -> T2448_LocRegX := ba_localregularX
exit 0
```
```
$ lake build RBM3D.Graph.BAEngine 2>&1 | tail -1                      (Mon Oct 12 11:20:23 UTC 2026)
Build completed successfully (3829 jobs).
$ lake env lean RBM3D/Graph/BAEngine.lean 2>&1 | wc -l                -> 0   (no warning, no error)
$ lake build      # whole library with the root import line added locally, 11:20:43 UTC (not committed; the hub adds it at merge, §3 (A) step 4)
exit code 0 | RBM3D.lean:506:0: axiom audit: 13141 theorems, 4131 definitions, 0 axioms in `RBM` | Build completed successfully (4274 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom " RBM3D/Graph/BAEngine.lean | wc -l       -> 0
$ git diff --stat main...t/T2448:  RBM3D/Graph/BAEngine.lean | 506 +++  (1 file changed, 506 insertions(+))
```
```
$ #print axioms (lake env lean ax2.lean)
'RBM.Graph.BALocRegConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baStep_nWS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_nWS_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baStart_nWS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baEngine_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAEngine_pL_locStd' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Compiled nonempty instances (statements, `BAEngineInst`; hypothesis `hX` = the O2R-C3 binder; proofs in the file):
```
430: example : ((BAGraph.ofLGraph (fxyPowGraph 2)).partition).length = 16 ∧
431:     (∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ¬ P0.g.LocStd) ∧
432:     ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, P0.g.waved.countP (fun e => !e.col) = 2 := by
439: example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ¬ P0.g.LocStd ∧
440:     ∃ outs, BALocStep P0 outs ∧ outs ≠ [] ∧ ∀ Q ∈ outs, 2 ≤ Q.g.waved.countP (fun e => !e.col) := by
452: example : ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ Q : BAPGraph (Fin 2), BAReach (P0.g.scalingOrder + 1) P0 Q ∧
453:     2 ≤ Q.g.waved.countP (fun e => !e.col) := by
470: example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) :
471:     ∃ fo fe : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)), ((BAGraph.ofLGraph (fxyPowGraph 2)).partition).length = 16 ∧
472:       BALocRegConcl 2 (1 / 4) 2 3 10 (((BAGraph.ofLGraph (fxyPowGraph 2)).partition).flatMap fo)
473:         (((BAGraph.ofLGraph (fxyPowGraph 2)).partition).flatMap fe) := by
483: example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) :
484:     ((BAGraph.ofLGraph (fxyPowGraph 2)).partition).length = 16 ∧ ∃ outs errs : List (BAPGraph (Fin 2)),
485:       BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧ (∀ Q ∈ outs, Q.g.LocStd ∧ 4 ≤ Q.scalingOrder) ∧
486:       (∀ Q ∈ errs, Q.g.scalingSize (1 / 4) 4 3 2 ≤ (4 : ℝ) ^ (-(10 : ℝ))) ∧
487:       (∀ Q ∈ outs ++ errs, 2 ≤ Q.g.waved.countP (fun e => !e.col)) ∧
488:       ∫ ω, (BAGraph.ofLGraph (fxyPowGraph 2)).val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
489:         ∫ ω, BAComb.val (outs ++ errs) (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) := by
```
```
$ name-clash grep -E "BALocRegConcl|baStep_nWS|ba_nWS_ge|baStart_nWS|baEngine_assemble|ba_localregularX|BAEngine_pL|BAEngineInst|BAEngine_" in RBM3D RBM3D.lean
main, t/T2433, t/T2441, t/T2445, t/T2446, t/T2447: 0 matches each; this worktree outside BAEngine.lean: 0
$ ports: none (no file of ../RBM1D or ../RBM2D read or copied); L4d unread: BAEngine.lean imports only BALvl1C, BAStepS; `BAExpandId` occurs once, in the module docstring
```

### Narrative
- Route, target 2: every output of the five `BAFrameStep` kinds is the partition of a term built by `BAGraph.ext` / `lanlwExt` on the twisted parent (waved edges mapped, colour kept, new ones appended); `splitG` keeps `waved`, `merge` maps it, the twist maps it by `conj` / `transpose`. `ba_nWS_ge` is `ba_lvl1_induction` on `baStep_nWS`; `baStart_nWS` is the partition count plus `simp` on `fxyPowGraph`.
- Target 3: (a) `LocStd` and the order from the hypothesis on `fo P0`; `2p ≤ ord` and `3p ≤ ord` from `baLocReg6_reach p P0 hP0 hX K Q hQ` at the `BAReach` of the third hypothesis; (b), (c) by `List.mem_flatMap`; (d) `BAGraph.val_eq_partition` (pathwise), the integral of a list sum (copies of the private `BALvl1C_integrable_pval`, `_integral_comb`), the per-start-term identity, `lvl1_sum_flatMap`. Target 4: `lvl1_choose_list` on `baLvl1LemmaSize_holds` per start term (`BAEngine_lists`), then target 3; `p ≤ n_{W,black}` by `ba_nWS_ge` and `baStart_nWS`.
- Instances: at `p = 2` every start term has a solid loop edge `e.src = e.dst` (`decide +kernel` on `splitG`), which survives `merge`, so none is `LocStd`; the step is from `baLvl1ExistsStep_holds`, its outputs are nonempty (`BAEngine_frame_ne_nil`, `baSplitSolid` never empty) and keep 2 black waved edges; targets 3-4 at `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10`, the identity at the flow point (`flowP_data`), with `hX` the only hypothesis.
- Premise scan (finding 2 of (a) confirmed): the first `lake build RBM3D` with the root import added locally failed in `RBM3D.lean:506:0` with "axiom audit: 1 premise(s) that no theorem of this development proves ... [RBM.Graph.BAGraph.LocStd]" (`baEngine_assemble` carries `LocStd` inside a hypothesis). Fix inside the file: `BAEngine_pL_locStd : BAEngine_pL.LocStd := by decide` (band precedent `localReg2_inst_Q_locStd`); the build above passes.
- L4d (T2419) is unread: no import, no declaration used; drop it from the inputs. No port from RBM1D/RBM2D; no `LWEngine` import. No correction to (a), so no (a′).
- Stop rules: file 506 < 2,000; no step lowers the count; pins equal up to the name; no new `inductive`, `Test/Axioms.lean` unchanged; the only unproved `Prop` premise is the binder; the consumer question is (d) 1. The root import line is not committed (as `git diff --stat main...t/T2446` shows for that branch); the hub adds it at merge.

## (c) Verified Mathlib names (`#check` of each, `names.lean`, exit 0; none absent)
`List.mem_flatMap`, `List.mem_map`, `List.map_map`, `List.countP_append`, `List.countP_map`, `List.exists_mem_of_ne_nil`, `List.flatMap_eq_nil_iff`, `List.map_eq_nil_iff`, `List.append_eq_nil_iff`, `List.mem_singleton`, `List.mem_cons`, `List.mem_append`, `List.map_append`, `List.sum_append`, `List.sum_map_add`, `List.map_congr_left`, `List.length_map`, `List.cons_ne_nil`, `Int.lt_succ`, `Real.rpow_neg_one`, `Real.rpow_le_rpow_of_exponent_le`, `MeasureTheory.integrable_zero`, `Bool.eq_false_iff`, `Function.comp_def`.

## (d) Open issues and paper-delta candidates
1. **Consumers of (1)-(5) (DECISIONS §260 (b), the ticket's last stop rule).** Re-checked: `lwMoment_prec_far_r` destructures `⟨-, hc2, hc3, -, hc5⟩` (`LWMoment:1275`) and reads `LocReg345`, `LocReg6` from conjunct 5 (`:1288`); `lw_localregularXP` reads conjunct 3 (`LWProv:1693`); `lwMoment_expand` reads the identity. `BALocRegConcl` has (6) in conjunct (a) and the identity in (d); `LocReg345` of the outputs is not inside it, as pinned, and must come from L3b1/L3b2 along the `BAReach` of conjunct (c). I read the stop rule as not triggered (no BA consumer contract exists yet); if the L3d2/L3d4 contract needs (1)-(5) inside the conclusion, the dispatcher amends the pin.
2. **`BAGraph.LocStd` producer.** `BAEngine_pL_locStd` is a concrete instance, a certificate-like producer, not a proof for arbitrary graphs; `BAGraph.LocStd` is a defining predicate (cf. `structuralProps`, `Test/Axioms.lean:250-260`). A registry line would be the honest classification (dispatcher; `Test/Axioms.lean` is not writable here, ticket: "Registry: none").
3. `P0.g.nM ≤ p` at the start terms is not in `BALocRegConcl` (owed to L3b1, DECISIONS §260 (c)).
4. T2448a: Lean `BALocRegConcl` has the four conjuncts (a)-(d); the paper's items (1)-(5) of `lem:localregular` are not in it, and the far half of (6) holds only at distinct external atoms (0951 L4-C4 (b)). T2448b: targets 3-4 are conditional on the three shape inputs of T2426 audit O2 (special-case caveat, not the unconditional lemma) until T2447 merges and a consumer discharges them.
