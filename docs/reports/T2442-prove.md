Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 06:37:00 UTC 2026

No analytic exponent enters (no `d`, `L`, `W`, `κ` of the paper, no data hypothesis: C1). The quantities are integer counters `(nS, nW, nA, nM)`, `ord = nS + 2(nW − nA)` (`BAVocab`: `counters`, `scalingOrder`), `nExt`, and the line budget. Source lines are those of the worktree at `4a0b23b` (= `main`).

### (i) Exponent table
Per output group of a `BAFrameStep`: raw change `(ΔnS, ΔnW, ΔnA, ΔnM)` of the term `T` against `Γ = P.g`, `Δord = ΔnS + 2(ΔnW − ΔnA)`, constraint `ord Q ≥ ord P` (slack = `Δord`), and the line of the merged fact.

| group (term `T` of `P.outsOf`) | `(ΔnS, ΔnW, ΔnA, ΔnM)` | `Δord` = slack | merged fact | status |
|---|---|---|---|---|
| `lw2` | (+1, +1, +1, 0) | +1 | `lw_counters` BAWeightOp:1680-1684 | merged |
| `lw4` | (+1, +2, +2, 0) | +1 | same | merged |
| `lanlw` T1, `lanlwD` | (+1, +1, +1, 0) | +1 | `lanlwT1_counters` BAExpandWOrd:757, `lanlwD_counters` :769 | merged |
| `gg2` A1 | (−2, +1, −κ, ≤0), κ ≥ 0 | 2κ (0 iff κ = 0) | `gg_counters` BAGGOp:1621, `gg_raw` | merged |
| `gg2` A2, A3 | (−1, +1, 0, ≤0) | +1 | same | merged |
| `gg2` A4, A5, AD; `gg4` | (+1, +1, +1, 0); (+1, +2, +2, 0) | +1 | same | merged |
| M-split of a term (`splitG`) | `ord Δs = ord T° − |ms| + 2κ` | min over `splitG` ≥ 0 | `lw_scalingOrderG` BAWeightOp:1731, `gg_scalingOrderG` BAGGOp:1666, `lanlw_scalingOrderG` BAExpandWOrd:803 (via `BASim_fam_*.hmono`, BASim3:445-634) | merged |
| macro (a) `W.first` (`BASim_Fwithin`) | (+1, +1, +1, 0) | +1 | order: `BASim_fam_within` BASim3:588; counters: none | **new** |
| macro (a) transfer `tr` | (0, +1, +1, 0): invariants of `P` | 0 | `BASim_inv_trA` BASim3:939 | merged |
| `tr.lw2`, `tr.lw4` | as `lw2`, `lw4` at `tr` | +1 over `tr` | `lw_mono` BAWeightOp:1815, `BASim_fam_lw2/4` | merged |
| macro (b) `X.d1` (`BASim_Fd1`) | (+1, +1, +1, 0) | +1 | order: `BASim_fam_d1` BASim3:634; counters: none | **new** |
| macro (b) `X.d2`, `X.d3` | (−1, +1, 0, ≤0) | +1 (strict) | `BASim_ord_d2/d3` BASim3:1550, 1568; counters: none | order merged, counters **new** |
| macro (b) `X.d4`, `[y] ≠ [y']` | (−2, +1, −κ′, ≤0), κ′ ≥ 0 | 2κ′ ≥ 0 | R1 has only `BASim_d4` :1491 (`>` or `nExt` falls) | **new** |
| macro (b) `X.d4`, `[y] = [y']` | invariants of `A1` | 2κ | `BASim_inv_d4_A1` :1587 | merged |
| macro (b) transfer `tr` | invariants of `P` | 0 | `BASim_trB_facts` :1036 (needs `hRa` from `BASim_Ra` :1286) | merged |
| `tr.gg2`, `tr.gg4` | as `gg2`, `gg4` at `tr` | +1 over `tr` | `gg_mono` BAGGOp:1702, `BASim_fam_gg2/4` | merged |

Other rows. `nExt`: `BASim_nExt_le` BASim2:1756 at `Δ ∈ T.splitG` (`BASim_Ext_split` :247, `BASim_Ext_atomAdj` :256), slack ≥ 0, no counter needed. Normal: `BAGraph.partition_normal` BAVocab:930, no hypothesis. `nM`, `nA − nW` of `Δ ∈ T.splitG` against `T°`: `Δ.nW = T°.nW` (`splitG_edges` BAVocab:697), `Δ.atomAdj ⊇ T°.atomAdj`, `Δ.adj ⊇ T°.adj` (`LGraph.adj` reads waved and `=`-dotted only, LWVocab:157), so `nA`, `nM` do not grow: `BAWeightOp_nA_le` (BAWeightOp:888, private: copy) and an `nM` twin (**new**, via `BAGraph.mem_mol_iff` BAVocab:394). The terms `d2, d3, d4` are fully circled, so `splitG = [T]` and no coarsening enters. `m` of `BAsim' m` is free (`baSim'_holds` BASim3:1830).

| constant | value | constraint | slack |
|---|---|---|---|
| stop line, each file | 2,000 | lines ≤ 2,000 | file 1 predicted ≈ 900 (700-1,100): slack ≈ 1,100; file 2 ≈ 600 (400-800): slack ≈ 1,400 |
| estimate T2395 §6 / R1-adjusted | 940 / 1,120 / 1,960; 800-1,600 | total ≈ 1,500 | inside the ticket's range |
| order slack at equality | `Δord` = 0 at `A1` with κ = 0 (`gg_raw`); in (ii) `ord =` outputs: 1 (`P_A`), 1 (`P_B`), 2 (`P_C`), 4 (`P_E`) | `Δord ≥ 0` | 0 at those outputs: the merged `*_scalingOrderG` (weak `≤`) must be used, a strict version is false |

### (ii) One concrete nondegenerate instance
Data: R1's `P_A` (`gg`), `P_B` (`within`), `P_C` (`ggSplit`), `P_W` (`weight`), `P_E` (`edge`) (`BASim3.lean:1876-1892`, `BASim.lean:1964`; compiled `BAFrameStep` terms `BALvl1AInst.hFA hFB hFC hFW hFE` BALvl1A:563-572, `locStepB/C`, `normalB/C` :642-650). `P_B`: `E = {0,1}`, `I = {2,3,4}`, solid `2→3` (inside the atom `{2,3}`), `0→2`, `1→4`, waved `S_{4,3}`, `M`-dot `{2,3}`. `P_C`: solid `2→1`, `0→3`, `1→0`, the pair `p = 2→1`, `q = 0→3` at the atom `{2,3}`. The script (Python model of the T2423 scratchpad, unchanged copies of `model.py run.py inv.py full.py diag.py`) builds every output of the step (term list, `ba_partition` = `splitG`) and tests the five conjuncts of `BAstepMono`: every solid edge circled (`Normal`), `ord Q ≥ ord P`, `nM Q ≤ nM P`, `nA − nW` not larger, `nExt Q ≤ nExt P`.
```
$ cd <scratchpad>/T2442 && python3 inst2.py
instance  kind     step-in-frame_steps  inv(ord,nM,nA-nW,loops,nS,pairs,nExt)  #outs  #violations  ord>  ord=  nExt<  groups
P_A gg True (1, 1, 1, 0, 3, 1, 2) 31 0 30 1 3 {'A1': 1, 'A2': 1, 'A3': 1, 'A4': 2, 'A5': 4, 'AD0': 8, 'B1': 2, 'B2': 4, 'BD0': 8}
P_B within True (1, 1, 1, 1, 3, 0, 2) 51 0 50 1 0 {'W': 17, 'W.tr2': 17, 'W.tr4': 17}
P_C ggSplit True (1, 1, 1, 0, 3, 1, 2) 48 0 46 2 5 {'X': 17, 'X.tr2': 17, 'X.tr4': 14}
P_W weight True (-2, 2, 2, 1, 2, 0, 1) 18 0 18 0 0 {'lw2': 9, 'lw4': 9}
P_E edge True (2, 1, 1, 0, 4, 3, 2) 26 0 22 4 4 {'L1': 2, 'LD0': 8, 'LD1': 8, 'LD2': 8}
random sweep (seed 101, 300 parents): outputs per kind {'within': 6120, 'weight': 8434, 'edge': 584, 'gg': 62, 'ggSplit': 24} | total 15224 | violations 0
```
All hypotheses hold at once: nonempty `E`, `I`, solid edges, a non-trivial atom, `nExt = 2`; `step-in-frame_steps` = True means the constructor hypotheses (`hwf`, `hint`, `hnb`, `sameAtom`) hold; `P_A` gives 31, `P_B` 51, `P_C` 48 outputs (31 = `ggF.length` in `BASim.lean:1971`; 51 and 48 as T2423 (a)(ii)). `P_C` has the outputs with `ord =` (2) and `nExt <` (5). No external hypothesis: no limit computation. Check file: `lake env lean docs/tickets/checks/T2442-check.lean` in the main worktree: exit 0, no output (`T2442_Reduction` with `BAsim'` elaborates).

### (i-iii) Section map (asked by the ticket, belongs to the table (i)) (file:line → planned declaration)
| source | planned (file 1 = `BALvl1B`, file 2 = `BALvl1B2`) | with / drop |
|---|---|---|
| `LWLvl1:989-992` `Lvl1Good` | `BALvl1Good` (probe 44-48, `nExt` after `ord`), `BALvl1GoodLit` (50-53) + two `Decidable` instances (54-55) | file 1; `nLoops`, `nPairs`, `nExt` from R0 imported |
| probe 259-272, 289-297 | `BAlvl1StepGood`, `BAstepMono`, `ba_good_of_lit` | file 1, proof copied |
| `LWLvl1:3290` `lvl1_step_good` | not copied: used at `T.img`; the BA counterpart is the reduction `ba_lvl1StepGood_of_sim'` | file 1 |
| probe 301-337 | `good_congr` (private), `lit_of_band` (public, on `baInv`; the only prover of `BALvl1GoodLit`, so that `#assert_rbm_axioms` finds it), reduction | file 1 |
| `LWLvl1:531-602` `lvl1_nM_le`, `lvl1_part_nM` | `BALvl1B_nM_le` (twin on `mol`, `Δ ∈ splitG` vs `T°`), `BALvl1B_nA_le` (copy of private `BAWeightOp_nA_le` :888 + `atom_subset`, `atom_eq_of_mem`, `self_mem_atom`), target 3 | file 1 |
| `LWLvl1:64-400, 603-937, 938-987` (dotted-edge partition counters `lvl1Split`, `lvl1_part_struct`, `lvl1_master`, `lvl1_k1/k2`, twist lemmas) | **dropped**: the BA measure comes from the band's `lvl1_step_good` at `T.img` (R1 `baSim'_holds`); the BA partition `splitG` has only `circ`/`M`-split, no `×`-dot counters | S′ |
| `LWLvl1:3181-3289` `LocStdDef`, `LocStep`, `Lvl1Reach` | already `BALocStep`, `BAReach` (T2440) | merged |
| private copies for cross-file use | `BALvl1B_circ_counters` (`BAWeightOp_circ_counters` :1652), `BALvl1B_ext_normal` (`BAWeightOp_ext_normal` :1665), `BALvl1B_packMerge_counters` (+ `splitG_of_circ`), `BALvl1B_cnt_le` (`BAGGOp_cnt_le` :1231 for the extension `nM`) | file 1, **public** with the stem, since file 2 imports them |
| target 3 + assembly lemma `BALvl1B_outs_mono` (term with `BASim_Ext`, `ord P ≤ ordG T`, `T°` counters → every `Q ∈ P.outsOf Ts`) | file 1; weight, edge, gg, `edge`'s `lanlw` | what R1 supplies: `BASim_Fam`, `BASim_outOf_baInv` :1340, `BASim_splitG_normal` :286, `BASim_nExt_le` |
| `BASim_Fwithin`/`d1`/`d2`/`d3`/`d4`, `tr` counters | file 2 (`within`, `ggSplit`, `baStepMono_holds`, `baLvl1StepGood_holds`, instances) | new counters lemma `BALvl1B_ext1_counters` (`BASim_counters_tr2` :921 with `y := x` + `BASim_counters_congr` BASim2:1687) |

### (i-iv) Target 2 at `obtain` level (`T2442_Reduction`), component map
`PGraph.baInv` (BASim:217) = (`ord counters`, `nM`, `nV − nW`, `lvl1NLoops`, `nS`, `lvl1NPairs`, `card E'`); `BAPGraph.baInv` (:215) = (`scalingOrder`, `nM`, `nA − nW`, `nLoops`, `nS`, `nPairs`, `nExt`). `Lvl1Good` reads components 1-6 (ord, nM, nV−nW, loops, nS, pairs); `BALvl1GoodLit` reads the same 1-6 of the BA graph; component 7 is `nExt`, treated by `BAstepMono` and `ba_good_of_lit`. `BAimg_holds` (BAAtomic:706): `T.g.img.g.counters = T.g.counters`, `lvl1NLoops = nLoops`, `lvl1NPairs = nPairs`, `card E' = nExt`, `Normal → Normal`; `T.img.g = T.g.img.g` (`PGraph.lvl1Comp` LWLvl1:3100, `BAPGraph.img` BAAtomic:111).
1. `rintro E P _ ⟨c, t, F, hF, rfl⟩ hP Q hQ` (`BALocStep` BALvl1A:65); `obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hQ`; `hPt := (ht c t P.g).1 hP`.
2. `obtain ⟨hN, ho, hnM, hAW, hx⟩ := hm _ _ hF hPt Q' hQ'` (`BAstepMono`).
3. `rcases hs _ _ hF hPt Q' hQ'` (`BAsim' m`, BASim:222) as `⟨T, L', hTN, hTinv, hst, Q0, hQ0, hQ0inv⟩ ∨ hlt ∨ hnx`.
4. first case: `obtain ⟨hc, hl, hp, -, hN', -⟩ := hi T.g`; `lvl1_step_good hst (hN' hTN) Q0 hQ0` gives `Lvl1Good T.img.g Q0.g`; `lit_of_band` (hypotheses: `hTinv`, `hQ0inv`, `hc hl hp`) gives `BALvl1GoodLit (P.twist c t).g Q'.g`; `ba_good_of_lit _ hx`. (Route check: `T.baInv = (P.twist c t).baInv` components 1-6 turn `ord`, `nM`, `nV−nW`, `loops`, `nS`, `pairs` of `T.img.g` into those of `P.twist c t` through `hc hl hp`; `Q0.baInv = Q'.baInv` does the same for the output. No step uses a `BAsim` premise.)
5. `hlt`, `hnx`: as probe 331-335 (order rises, or `nExt` falls and `ho` weak). 6. twist back: `ht c t P.g`, `ht c t Q'.g`, `ba_twist_counters` BASymm1:83, `good_congr`. Route verdict: closes.

### (i-v) `BAstepMono` per kind of `BAFrameStep` (BASim:76): lemma for each conjunct (N normal, O order, M `nM`, AW `nA−nW`, X `nExt`)
| kind, output group | N | O | M, AW | X |
|---|---|---|---|---|
| `weight` `lw2`, `lw4` | `partition_normal` (merged) | `BASim_fam_lw2/4.hmono` + `le_scalingOrderG_iff` (merged) | `lw_mono` + target 3 (new) | `BASim_nExt_le` (merged) |
| `edge` `lanlwTerms` | same | `BASim_fam_lanlw` (merged) | `lanlw*_counters` + `circ_counters` + target 3 (new) | same |
| `gg` `gg2`, `gg4` | same | `BASim_fam_gg2/4` (merged) | `gg_mono` + target 3 (new) | same |
| `within` `W.first`, `lanlwD` | same | `BASim_fam_within` (merged) | first term: `BALvl1B_ext1_counters` + target 3 (**new**); `lanlwD`: as `edge` | same |
| `within` `tr.lw2/4` | same | `lw_*`-family at `tr`, `ord tr = ord P` from `BASim_inv_trA` (merged) | `lw_mono` at `tr`, `baInv tr = baInv P` (merged) + `BALvl1B_ext_normal` (copy) | via `baInv tr` |
| `ggSplit` `X.L1`, `X.LD` (`eraseIdx`) | same | `BASim_fam_lanlw` (subset) | as `edge` | same |
| `ggSplit` `X.d1` | same | `BASim_fam_d1` (merged) | `BALvl1B_ext1_counters` + target 3 (**new**) | same |
| `ggSplit` `X.d2`, `X.d3` | same | `BASim_ord_d2/d3` (merged, strict) | `BALvl1B_cnt_le` for `nM` (**new**), `BASim_Cons.nA_le` BASim3:816 (merged) | `BASim_Cons.nExt` (merged) |
| `ggSplit` `X.d4` | same | `[y] ≠ [y']`: weak `ord` from the formula `ord = ord Γ + 2 (nA Γ − nA T)` with `BASim_Cons.nA_le` (**new**); `[y] = [y']`: `BASim_inv_d4_A1` + `gg_raw` | as `d2` (**new**); `A1` via `gg_mono` | as `d2` |
| `ggSplit` `tr.gg2/4` | same | `BASim_fam_gg2/4` at `tr`, `BASim_trB_facts` | `gg_mono` at `tr` + `baInv tr = baInv P` | via `baInv tr` |
Hypotheses of the lemmas at `tr` (`p′ ∈ lwSplit tr.solid`, `q′ ∈ lwSplit p′.2`) by `lvl1_split_last` LWLvl1:4220, as R1's `BASim_macroA/B2`; `Ttr` is `BASim_Ttr` BASim3:1644; outputs at `Ttr` are those of `P` by `BASim_macro_out` BASim3:1680. Cases use `baFrameStepT_untag_holds` (BASim:281) and `BASim_mem_outsT` (BASim:1825) to name `T`, `Δ`.

### (i-vi) Lines against the stop line and the boundary
File 1 `BALvl1B`: header/imports 60, target 1 defs and `ba_good_of_lit` 60, reduction with `good_congr`, `lit_of_band` 90, copied private helpers 120, `nM`/`nA` coarsening and extension lemmas 250, target 3 90, assembly lemma 80, `weight`/`edge`/`gg` cases 150, instances 40: ≈ 940 (limit 2,000). File 2 `BALvl1B2`: `ext1_counters` 40, `within` 150, `ggSplit` (d1-d4, `tr`) 250, `baStepMono_holds` 60, `baLvl1StepGood_holds` 15, instances 80: ≈ 600. Total ≈ 1,540, in the ticket's 800-1,600. Boundary as the ticket (import `BALvl1B → BALvl1B2`); every file-1 helper used by file 2 is public with stem `BALvl1B_` (private ones are invisible across files).

### Verdicts
- Target 1 (defs, `ba_good_of_lit`): PASS. Target 2 (reduction from `BAsim'`): PASS (route (i-iv) closes; check file exit 0).
- Target 3 (coarsening, `splitG` vs `T°`): PASS (new `nM` twin only). Target 4 (`baStepMono_holds`): PASS; new pieces are the `nM` twin, `ext1_counters`, `d2/d3/d4` counters, weak order of `d4` (all by the formulas of (i); 0 violations in (ii)).
- Target 5: PASS. Target 6 (instances at `hFA`-`hFE`, `locStepB/C`): PASS (the terms exist at BALvl1A:563-650). Target 7: PASS (no `inductive`, `lit_of_band` public).
- Findings for the dispatcher, none changes a verdict: R1's `BASim3.lean:29-40` takes ~16 private lemmas by `open private`; §247 forbids that here, so file 1 copies them (counted in (i-vi)). Names `BALvl1B*`, `BAstepMono`, `BAlvl1StepGood`, `BALvl1Good`, `ba_good_of_lit`, `baStepMono_holds`, `baLvl1StepGood_holds`, `ba_lvl1StepGood_of_sim'` are defined nowhere on `main` and the 44 `t/T24*` refs (`git grep` of `def`/`theorem` heads, `git ls-tree` for `Graph/BALvl1B`: `names.sh` prints only `refs scanned: 45`; the probe branch `t/T2395` is not in that set); `t/T2443` does not exist yet.

## (a′) Preflight corrections — Mon Oct 12 08:46:53 UTC 2026
- (a) says of the check file "exit 0, no output". Run in the worktree (block 1 below, last command): exit 0, 317 output lines (the `#check` results), 0 lines containing `error`. No verdict changes.
- (a) says "`t/T2443` does not exist yet". At the time of block 8 the ref exists and was scanned: no clash.
## (b) Script output — Mon Oct 12 08:46:53 UTC 2026; final commit 0b280c3 on `t/T2442`
### Block 1: size against the stop line, hygiene, diff, builds of the two modules, check file (`evidence.sh`, verbatim)
```
$ date -u
Mon Oct 12 08:42:56 UTC 2026
$ git log --oneline -1
0b280c3 T2442: BALvl1B: docstring of BALvl1B_adj_mono
$ wc -l RBM3D/Graph/BALvl1B.lean RBM3D/Graph/BALvl1B2.lean   # stop line 2000 per file
     491 RBM3D/Graph/BALvl1B.lean
     318 RBM3D/Graph/BALvl1B2.lean
     809 total
$ grep -c -E "sorry|admit|native_decide|axiom " <both files>   # per file
RBM3D/Graph/BALvl1B.lean:0
RBM3D/Graph/BALvl1B2.lean:0
$ grep -c -E "RBM1D|RBM2D|open private" <both files>   # ports from the sister projects: none
RBM3D/Graph/BALvl1B.lean:0
RBM3D/Graph/BALvl1B2.lean:0
$ git diff --stat main...t/T2442
 RBM3D/Graph/BALvl1B.lean  | 491 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BALvl1B2.lean | 318 ++++++++++++++++++++++++++++++
 2 files changed, 809 insertions(+)
$ lake build RBM3D.Graph.BALvl1B RBM3D.Graph.BALvl1B2 2>&1 | tail -1
Build completed successfully (3825 jobs).
$ lake env lean RBM3D/Graph/BALvl1B.lean 2>&1 | wc -l   # compiler messages of the file
       0
$ lake env lean RBM3D/Graph/BALvl1B2.lean 2>&1 | wc -l
       0
$ lake env lean docs/tickets/checks/T2442-check.lean > out 2>&1; echo "exit=$?"; wc -l < out; grep -c error out
exit=0
     317
0
```
### Block 2: section map (iii) as finally written (file 1 = `BALvl1B` = B, file 2 = `BALvl1B2` = B2; line numbers from `secmap.py`)
| source | declaration (file:line) | merged supplies / S′ drops |
|---|---|---|
| probe 44-55; `Lvl1Good` LWLvl1:989-992 | `BALvl1Good` B:63, `BALvl1GoodLit` B:70, two `Decidable` instances B:75-76 | verbatim (diff in block 4); `nExt`, `nLoops`, `nPairs`, `LocStd` (R0) imported |
| probe 259-272, 289-297 | `BAlvl1StepGood` B:91, `BAstepMono` B:96, `ba_good_of_lit` B:79 | verbatim; proof copied |
| probe 301-337; `lvl1_step_good` LWLvl1:3290 | private `BALvl1B_good_congr` B:107; public `BALvl1B_lit_of_band` B:119 (only prover of `BALvl1GoodLit`); `ba_lvl1StepGood_of_sim'` B:133 | `BAsim' m` in place of `BAsim m`; `lvl1_step_good` is used at `T.img`, not copied |
| LWLvl1:531-602 (`lvl1_nM_le`, `lvl1_part_nM`) | `BALvl1B_cnt_le` B:157, `_adj_mono` B:194, `_coarse` B:214, `_splitG_struct` B:234, `_part_struct` B:250 (target 3) | R1: `BASim_splitG_normal`, `BASim_outOf_baInv`, `BASim_nExt_le`, `BASim_Ext_split` |
| BAWeightOp:1652, 1665 (private) | `BALvl1B_circ_counters` B:271, `BALvl1B_ext_normal` B:277 | copies under the stem (no `open private`) |
| counters at the terms | B: `_mono_of_counters` 289, `_ext1` 300, `_mono_of_ref` 319, `_lanlw_mono` 335; B2: `_d_mono` 50, `_trB_inv` 62, `_ord_d4` 91, `_inv4` 142, `_within_mono` 150, `_dterms_ok` 160 | `lanlwT1_counters`, `lanlwD_counters`, `BASim_counters_tr2`, `BASim_cons_tr2` |
| assembly and cases | B: `BALvl1B_Mono` 350, `_mem_outsOf` 354, `_outs_mono` 365, `_outs_fam` 395, `_TermOk` 405, `_outs_ok` 410, `_weight` 419, `_edge` 430, `_gg` 436; B2: `_within` 200, `_ggSplit` 220, `baStepMono_holds` 252, `baLvl1StepGood_holds` 264 | `lw_mono`, `gg_mono`, `BASim_fam_*`, `BASim_inv_trA`, `BAGraph.partition_normal`, `BAGraph.le_scalingOrderG_iff` |
| LWLvl1:64-400, 603-987 (`×`-dot partition counters, `lvl1_master`, `lvl1_k1/k2`, twist lemmas) | dropped | S′: the measure half is the band's `lvl1_step_good` at `T.img` through `baSim'_holds` |
| instances | `BALvl1BInst`: B:450-487, B2:271-314 | R1 data `BASimInst`, steps and twisted steps `BALvl1AInst` |
### Block 3: table (v) as finally written. Every group: N = `BAGraph.partition_normal` (merged); X = `BALvl1B_part_struct` (new) with `BASim_nExt_le` (merged) and `nExt` of the base graph (`P`, or `tr` with `nExt tr = nExt P`); M, AW = column 3 + the coarsening of `BALvl1B_part_struct` (new)
| kind: group (base graph) | O: order | M, AW: counters at `T°` |
|---|---|---|
| weight: `lw2`, `lw4` (P) | `BASim_fam_lw2/4` (m) | `lw_mono` (m) |
| edge: `lanlwT1`, `lanlwD` (P) | `BASim_fam_lanlw` (m) | `BALvl1B_lanlw_mono` (new, from `lanlwT1_counters`, `lanlwD_counters` (m)) |
| gg: `gg2`, `gg4` (P) | `BASim_fam_gg2/4` (m) | `gg_mono` (m) |
| within: `W.first`, `lanlwD` (P) | `BASim_fam_within` (m) | `BALvl1B_within_mono` (new: `BALvl1B_d_mono`, `_lanlw_mono`) |
| within: `tr.lw2`, `tr.lw4` (`tr`; `BASim_inv_trA` (m)) | `BASim_fam_lw2/4` at `tr` (m) | `lw_mono` at `tr` (m) |
| ggSplit: `lanlwT1 :: lanlwD` minus `j` (P) | `BASim_fam_lanlw` (m) | `BALvl1B_lanlw_mono` (new) |
| ggSplit: `d1` (P) | `BASim_fam_d1` (m) | `BALvl1B_d_mono` (new) |
| ggSplit: `d2`, `d3` (P) | `BASim_ord_d2/d3` (m) + `BAGraph.scalingOrderG_of_normal` (m) | `BALvl1B_d_mono` (new) |
| ggSplit: `d4` (P) | `BALvl1B_ord_d4` (new; weak order, `[y] = [y']` and `≠` at once) | `BALvl1B_d_mono` (new) |
| ggSplit: `tr.gg2`, `tr.gg4` (`tr`; `BALvl1B_trB_inv` (new)) | `BASim_fam_gg2/4` at `tr` (m) | `gg_mono` at `tr` (m) |
(m = merged.) Cases by `cases` on `BAFrameStep` in `baStepMono_holds` (B2:252): `weight`, `within`, `edge`, `gg`, `ggSplit`.
### Block 4: the statements of targets 1, 2, 4, 5 extracted by script (`stmt_print.py`: file:line, whitespace normalized) and their script diff (`stmt_diff2.py`)
```
BALvl1B.lean:63: def BALvl1Good (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Prop := Γ.scalingOrder ≤ Q.scalingOrder ∧ Q.nM ≤ Γ.nM ∧ ((Q.nA : ℤ) - Q.nW ≤ (Γ.nA : ℤ) - Γ.nW) ∧ Q.nExt ≤ Γ.nExt ∧ (Γ.scalingOrder < Q.scalingOrder ∨ (Q.scalingOrder = Γ.scalingOrder ∧ (Q.nExt < Γ.nExt ∨ (Q.nExt = Γ.nExt ∧ (Q.nLoops < Γ.nLoops ∨ (Q.nLoops = Γ.nLoops ∧ (Q.nS < Γ.nS ∨ (Q.nS = Γ.nS ∧ Q.nPairs < Γ.nPairs))))))))
BALvl1B.lean:70: def BALvl1GoodLit (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Prop := Γ.scalingOrder ≤ Q.scalingOrder ∧ Q.nM ≤ Γ.nM ∧ ((Q.nA : ℤ) - Q.nW ≤ (Γ.nA : ℤ) - Γ.nW) ∧ (Γ.scalingOrder < Q.scalingOrder ∨ (Q.scalingOrder = Γ.scalingOrder ∧ (Q.nLoops < Γ.nLoops ∨ (Q.nLoops = Γ.nLoops ∧ (Q.nS < Γ.nS ∨ (Q.nS = Γ.nS ∧ Q.nPairs < Γ.nPairs))))))
BALvl1B.lean:91: def BAlvl1StepGood : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs → P.g.Normal → ∀ Q ∈ outs, Q.g.Normal ∧ BALvl1Good P.g Q.g
BALvl1B.lean:96: def BAstepMono : Prop := ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BAFrameStep P outs → P.g.Normal → ∀ Q ∈ outs, Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧ ((Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧ Q.g.nExt ≤ P.g.nExt
BALvl1B.lean:133: theorem ba_lvl1StepGood_of_sim' : ∀ m : ℂ, BAimg → BAsim' m → BAstepMono → BAtwistInv → BAlvl1StepGood
BALvl1B2.lean:252: theorem baStepMono_holds : BAstepMono
BALvl1B2.lean:264: theorem baLvl1StepGood_holds : BAlvl1StepGood := ba_lvl1StepGood_of_sim' 0 BAimg_holds (baSim'_holds 0) baStepMono_holds baTwistInv_holds
statement text (whitespace normalized), mine = BALvl1B.lean vs check file docs/tickets/checks/T2442-check.lean (T2442_* renamed) / vs probe t/T2395:RBM3D/Probe/T2395Pins.lean
BALvl1Good                   vs check file: EQUAL; vs probe: EQUAL
BALvl1GoodLit                vs check file: EQUAL; vs probe: EQUAL
BAlvl1StepGood               vs check file: EQUAL; vs probe: EQUAL
BAstepMono                   vs check file: EQUAL; vs probe: EQUAL
ba_lvl1StepGood_of_sim'      vs check file: EQUAL
ba_good_of_lit               vs probe, from `{Γ : BAGraph` on: EQUAL (the instance binders are `variable`s in BALvl1B.lean)
two Decidable instances      vs probe: EQUAL
```
### Block 5: the full library build with the two root imports added temporarily (`fullbuild.sh`, verbatim; `RBM3D.lean` restored afterwards)
```
$ date -u
Mon Oct 12 08:43:18 UTC 2026
$ git diff --stat -- RBM3D.lean   (temporary root imports)
 RBM3D.lean | 2 ++
 1 file changed, 2 insertions(+)
$ lake build   (full library, runs #assert_rbm_axioms)
lake build exit code: 0
info: RBM3D.lean:496:0: axiom audit: 12914 theorems, 4059 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4264 jobs).
$ git status --short   (RBM3D.lean restored)
```
### Block 6: axioms (`axioms_all.lean`: `#print axioms` of the 34 public theorems of both files)
```
theorems printed: 34; with exactly [propext, Classical.choice, Quot.sound]: 34; other lines: 0
'RBM.Graph.ba_good_of_lit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_lvl1StepGood_of_sim'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BALvl1B_part_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baStepMono_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLvl1StepGood_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### Block 7: compiled nonempty instances (`grep -n` of the `example`s; B:459 target 1, B:470 target 3, B:481 cases `weight`/`edge`/`gg`, B2:276 data invariants, B2:282 macro claims, B2:290 target 4, B2:300 target 5, B2:309 target 2)
```
RBM3D/Graph/BALvl1B.lean:455:def tW : BAGraph (Fin 1) (Fin 2 ⊕ Fin 2) := (baPW.lw2 pW).head (by simp [BAGraph.lw2])
RBM3D/Graph/BALvl1B.lean:459:example : (baPW.scalingOrder = -2 ∧ tW.scalingOrder = -1) ∧ BALvl1GoodLit baPW tW ∧ BALvl1Good baPW tW :=
RBM3D/Graph/BALvl1B.lean:463:def d1C : BAGraph (Fin 2) (Fin 3 ⊕ Fin 2) :=
RBM3D/Graph/BALvl1B.lean:467:theorem normalPC : baPC.Normal := by decide
RBM3D/Graph/BALvl1B.lean:470:example : d1C.splitG.length = 4 ∧ ∀ Δ ∈ d1C.splitG, Δ.Normal ∧ Δ.nW = (BAWeightOp_circ d1C).nW ∧ Δ.nA ≤ (BAWeightOp_circ d1C).nA ∧
RBM3D/Graph/BALvl1B.lean:477:def outsW : List (BAPGraph (Fin 1)) := (baPG baPW).outsOf (baPW.lw2 pW) ++ (baPG baPW).outsOf (baPW.lw4 pW)
RBM3D/Graph/BALvl1B.lean:478:def outsE : List (BAPGraph (Fin 2)) := (baPG baPE).outsOf (BAGraph.lanlwTerms baPE pE)
RBM3D/Graph/BALvl1B.lean:481:example : ((∀ Q ∈ outsW, BALvl1B_Mono (baPG baPW) Q) ∧ 0 < outsW.length) ∧ ((∀ Q ∈ outsE, BALvl1B_Mono (baPG baPE) Q) ∧ 0 < outsE.length) ∧
RBM3D/Graph/BALvl1B2.lean:276:example : BASim_inv baPA = (1, 1, 1, 0, 3, 1, 2) ∧ BASim_inv baPB = (1, 1, 1, 1, 3, 0, 2) ∧ BASim_inv baPC = (1, 1, 1, 0, 3, 1, 2) ∧
RBM3D/Graph/BALvl1B2.lean:282:example : ((∀ Q ∈ (baPG baPB).withinOuts pB, BALvl1B_Mono (baPG baPB) Q) ∧ 0 < ((baPG baPB).withinOuts pB).length) ∧
RBM3D/Graph/BALvl1B2.lean:290:example : ((∀ Q ∈ ggF, BALvl1B_Mono (baPG baPA) Q) ∧ 0 < ggF.length) ∧ ((∀ Q ∈ (baPG baPB).withinOuts pB, BALvl1B_Mono (baPG baPB) Q) ∧ 0 < ((baP
RBM3D/Graph/BALvl1B2.lean:300:example : ((∀ Q ∈ ((baPG baPB).withinOuts pB).map (BAPGraph.twist true true), Q.g.Normal ∧ BALvl1Good ((baPG baPB).twist true true).g Q.g) ∧
RBM3D/Graph/BALvl1B2.lean:309:example (m : ℂ) : (∀ Q ∈ ((baPG baPB).withinOuts pB).map (BAPGraph.twist true true), Q.g.Normal ∧ BALvl1Good ((baPG baPB).twist true true).g Q.g)
```
### Block 8: name-clash grep of the new public names (`clash.sh`: declaration heads on `main` and every other `refs/heads/t/*`, 442 refs)
```
t/T2325 RBM3D/Probe/T2325BAGen.lean: 139:BALvl1Good
t/T2395 RBM3D/Probe/T2395Pins.lean: 44:BALvl1Good, 50:BALvl1GoodLit, 259:BAlvl1StepGood, 269:BAstepMono, 289:ba_good_of_lit
refs scanned: 442 (main + every other refs/heads/t/*); refs with a declaration clash: 2; refs mentioning BALvl1BInst: 0
ref present: t/T2443
```
Ports: none (block 1: 0 mentions of `RBM1D`/`RBM2D`; the sources are the probe `t/T2395:RBM3D/Probe/T2395Pins.lean:44-55, 259-272, 289-297`, copied, and the private helpers of `BAWeightOp` (copied under the stem)).
### Narrative
1. Targets 1-7 are delivered on `t/T2442`; commits after the base 4a0b23b: 3a62098 (previous 1b run), bb8bfcd, d0b71a0, 86c4f34, 41061fc, 215afd7, 0b280c3 (this run). 809 lines in two files against the stop line 2,000 each (block 1). The statements of `BALvl1Good`, `BALvl1GoodLit`, `BAlvl1StepGood`, `BAstepMono` (target 1; the types of targets 5 and 4) and of the reduction (target 2) equal the check file's `T2442_*` up to the name (block 4). `Test/Axioms.lean`, the registry and `RBM3D.lean` are unchanged on the branch; no `inductive` (grep: 0). `BALvl1GoodLit`, assumed by `ba_good_of_lit`, is proved by the public `BALvl1B_lit_of_band`; the premise scan passes (block 5).
2. Target 4. One assembly lemma `BALvl1B_outs_mono` (B:365): an output of `P.outsOf Ts` is `P.BASim_outOf Δ` with `Δ ∈ T.splitG`; target 3 (`BALvl1B_part_struct`, B:250) gives `Δ` normal, `n_W` equal, `n_A`, `n_M`, `nExt` not larger than at `T°`; the order is `BASim_Fam.hmono` read through `le_scalingOrderG_iff` (`scalingOrderG_of_normal` for the circled `d2`-`d4`); the counters at `T°` are column 3 of block 3. The macro claims run the same assembly at the transfer graph `tr` (stage 2), whose order, `n_M`, `n_A - n_W`, `nExt` are those of `P` (`BASim_inv_trA`, `BALvl1B_trB_inv`).
3. Targets 2, 5. As (a)(iv): the first disjunct of `BAsim'` gives `T`, `Q0`; `lvl1_step_good` at `T.img`; `BALvl1B_lit_of_band` reads the first six components of `PGraph.baInv`, `BAPGraph.baInv`; `ba_good_of_lit` adds `nExt` from `BAstepMono`; the other two disjuncts are direct; twist back by `ba_twist_counters`, `BAtwistInv`. `baLvl1StepGood_holds` is this reduction at `0`, `BAimg_holds`, `baSim'_holds 0`, `baStepMono_holds`, `baTwistInv_holds`.
4. Differences from (a): 809 lines against about 1,540 predicted in (i-vi); the copies `BALvl1B_packMerge_counters` and `splitG_of_circ` of (a)'s map were not needed (R1's public `BASim_outOf_baInv` and `BAGraph.scalingOrderG_of_normal` serve); `BALvl1B_ord_d4` gives the weak order of `d4` for `[y] = [y']` and `[y] ≠ [y']` at once; `BASim_trB_facts` and `BASim_Ra` are not used (`BALvl1B_trB_inv` needs only `[a] = [a']`).
5. Instances are statement level. A packed output is noncomputable: `def q0 := ((baPG baPB).withinOuts pB).head _` fails to compile ("... because it depends on 'BAPGraph.withinOuts', which is 'noncomputable'") and `decide`, `decide +kernel` on `(baPG baPB).g.scalingOrder ≤ q0.g.scalingOrder` are stuck at the `Int` match. The five conjuncts at every output are therefore checked only by the (a)(ii) script (0 violations in its 15,224 random outputs); the Lean instances apply the theorems at R1's five data, and `BASim_inv` of the data equals the (a)(ii) table by `decide` (B2:276).
6. `RBM3D.lean` is not changed on the branch: the `t/T2439` branch touched only its two files (`git diff --name-only 98aab64...3ef3862`) and the hub merge commit dba665d added its two import lines (`git diff --stat dba665d^1 dba665d -- RBM3D.lean`: 2 insertions). Block 5 shows the full build and `#assert_rbm_axioms` pass with `import RBM3D.Graph.BALvl1B` and `import RBM3D.Graph.BALvl1B2` added after `import RBM3D.Graph.BALvl1A`.

## (c) Verified Mathlib/core names (`#check` in the worktree, 0 errors: scratchpad `mathlib_chk2.lean`, and `mathlib_chk.lean` on the 40 names extracted from the final files)
`List.mem_of_getElem?`, `List.mem_of_mem_eraseIdx`, `List.mem_flatMap`, `List.mem_map_of_mem`, `List.mem_singleton_self`, `WithTop.coe_le_coe`, `Relation.ReflTransGen.head`, `Relation.ReflTransGen.mono`, `Finset.card_le_card`, `Finset.image_subset_image`, `Prod.mk.injEq`; also `List.mem_append`, `List.mem_cons`, `List.mem_map`, `Bool.and_eq_true`, `Finset.mem_filter` and the rest of the 40. Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates
- `RBM3D.lean`: the hub adds `import RBM3D.Graph.BALvl1B` and `import RBM3D.Graph.BALvl1B2` at merge (block 5).
- Probe name clash (block 8): `t/T2325:RBM3D/Probe/T2325BAGen.lean:139` and `t/T2395:RBM3D/Probe/T2395Pins.lean` define `BALvl1Good` (both), `BALvl1GoodLit`, `BAlvl1StepGood`, `BAstepMono`, `ba_good_of_lit` (T2395 only). Neither file is on `main` (no `main` hit); the ticket's sibling scan names only `t/T2395`. Merging either probe file would clash with the library names.
- Paper-delta candidate `T2442a`: `BALvl1Good` has `Q.nExt ≤ Γ.nExt` and puts `nExt` between `ord` and `nLoops`; the band's `Lvl1Good` (LWLvl1:989-992, read by `BALvl1GoodLit`) has neither. The paper asserts an analogue of `lvl1 lemma` for the block Anderson model without a measure (`paper/tex/B_graphical_lemmas.tex:407`), so `BAlvl1StepGood` has no paper statement to compare with.
- `BAsim` (literal, BASim:210) is still proved by no theorem; `ba_lvl1StepGood_of_sim'` takes `BAsim' m` as the ticket says. Not a paper statement: no delta candidate.
