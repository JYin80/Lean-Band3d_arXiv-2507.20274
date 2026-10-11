**Verdict on (6) at BA (gate G2): it HOLDS on both branches, by one cost invariant written on the atomic image of the BA graph (brute-force verified; the Lean proofs are the rows).** Under S′ (T2395, merged `d859e60`; S literally fails, T2395 F1-F5): the band step lemma is used through a simulation up to relabelling (`BASimC`), and five BA-only `ScostLL` lemmas are new (`S1` with `y`, `y'` in two atoms, `E1`, `E2`, the macro (a)/(b) intermediates: 9,248,933 checks, 0 violations, E13); G2's rows L3b3′ + L3b4′ are 845 / 1,190 / 2,083 (T2395 priced 590 central, §6). Without S: the same invariant written at atoms, rows twinned (10,569 central, 8 rows after splits). No missing mathematical step, no question to Jun.

# T2397 (BA-L3b3, G2) design: property (6) of `lem:localregular` at the block Anderson model

Prover `claude-sonnet-5-5` (prover-max, design only); repair of audit round 1 by `claude-opus-5-5` (§8). Branch `t/T2397` (base `19fc8cf`; the T2395 merge `d859e60` is not in the base, its report is read on `main`), probe `RBM3D/Probe/T2397Pins.lean` (385 lines, limit 400), commits `17853aa`, `17295e2`, `329703b`, `f32f904`, `0e2bb41`, `416232c`, `005474a` (repair, probe) and the commit of this text. Last edit: Sun Oct 11 02:39:14 UTC 2026 (`date -u`).
Citations: `B:N`, `7:N` = lines of `paper/tex/B_graphical_lemmas.tex`, `7_8_light_weight.tex`; `6a:N` ... `6d:N` = `RBM3D/Graph/LocalRegular6a.lean` ... `6d`; `LR:N`, `LR2:N` = `LocalRegular.lean`, `LocalRegular2.lean`; `BV:N` = `Graph/BAVocab.lean`; `probe N` = the probe; `T2387:N` = `docs/reports/T2387-design.md`; `(a) row k`, `E0`-`E12`, `L1`, `L3`-`L5` = rows and blocks of `docs/reports/T2397-prove.md` (a), (b) (script output; scripts in the scratchpad `T2397/`, not in the repository). `Φ^all`, `Φ^far` = the minimum of the band cost over merges (far: the atoms of `x`, `y` kept apart). `T2395:N` = lines of `docs/reports/T2395-design.md` on `main`; `E13`, `E14` = §8 (repair; scripts `r_shapes.py`, `r_rows.py`, same scratchpad).

## 0. The answer

| item | answer | where |
|---|---|---|
| P1 band route | cost `c_s = #kept + 2 n_W - 2 #intCls + #elemCls` over merges `s`; invariant `Φ^all ≥ 2p`, `Φ^far ≥ 3p` along `strat_local`; five statements carry it; the TeX step `B:275-277` fails at the 2-cycle collapse (E0) | §1 |
| P2 under S′ | the map is the atomic image `img` (probe 32-48; K1 of T2395 = `promoteC` keeps inside-atom edges): `ord`, `n_M` preserved, cost = band cost on the image; the step of T2395's `BALocStep` (at atoms) is matched, **up to relabelling**, with a band `LocStep` (`BASimC` probe 129, `BASimP` 170); its BA-only outputs `s1`, `e1`, `e2`, `macroA`, `macroB` (probe 123) carry new `ScostLL` lemmas (`BAShapeLL` 134; E13); one theorem `ba_ord_ge_of_simC` (148), instance at the band lift with every hypothesis discharged (364); the literal `BAImgSim` (equality of packed graphs) is withdrawn; `(eq:MolVW)` must count atoms | §2 |
| P3 without S | write `scostA` (probe 40): initial values sharp at BA (E5), step lemma 0 violations in 3.5e7 checks (E2, E3), final step `#elem = 0` (E7), end to end `p = 2` exhaustive to `ord 5` (E8); constants `2p`, `3p` only; **no stop** | §3 |
| P4 pins | 19 Prop pins (with the target predicate `BALocReg`), 30 theorems, 64 declarations compiled (probe 50-188, 278-377); instances at `p = 2` (probe 313-377) | §4 |
| C1 / L5 | (6) is counting: no `g`, `κ`, `c`, `ρ`; the constants of the layer are checked at `g = 1/64, 1, 10` in (a) rows 6-12 | §5 |
| rows | S′, G2's rows L3b3′ + L3b4′: 845 / 1,190 / 2,083; twin: 7,927 / 10,569 / 18,918, split into 8 rows; the first version's S rows (3,766) and its "S'" (renamed S+GG) are withdrawn | §6 |

## 1. P1: the band route as merged (T2184 / T2195 / T2203 / T2216)

- **Why a new route.** The TeX tracks `ord + n_dv + n_lw` (`B:200-278`) and asserts the step (`B:275-277`): removing a distinguished vertex raises `ord` by at least 1/2; "the worst case occurs in a GG expansion involving two distinguished vertices: ... the scaling order increases by 1". It fails (DECISIONS §47: `2·ord + n_dv` falls from 9 to at most 8). The merged route (DECISIONS §55) minimises a local cost over merges.
- **The cost** (6a:157): `scost Γ s = #kept + 2(n_W - #internal classes) + #elementary internal classes` for a setoid `s` on the vertices; kept = circled or joining two classes; internal = no external member; elementary = half-edge pattern `(b-in, b-out, r-in, r-out)` of the kept edges at the class in `{(1,1,0,0), (0,0,1,1)}` (a loop counts both halves). `Φ(Q) = min_s scost`. At the trivial merge `scost ⊥ = ord + #elem` on a normal graph (6a:560).
- **Five statements carry the route** (file:line):
  1. the invariant `PGraph.LocReg6Inv` 6a:182 = `Normal ∧ CircIffLoop` (6a:162) `∧ LocCostGe false 2p ∧ LocCostGe true 3p` (6a:177);
  2. the initial values `fxyPowGraph_locCostGe` 6a:927 (sharp: `Φ^all(Γ_p) = 2p`, `Φ^far(Γ_p) = 3p`, (a) row 2);
  3. the local lemma `LGraph.ScostLL` 6a:168 and its seven primitives `scostLL_loop` 6b:621, `_addLoop` 6b:633, `_moveLoop` 6b:638, `_contract` 6b:1391, `_moveSC` 6c:1123, `_moveOut` 6c:1196, `_dmove` 6c:1431 (for `_contract`, `_moveSC`, `_moveOut`, `_dmove` the removed edges are uncircled non-loops, `u ≠ z`, `z ≠ v`; `_moveLoop` removes a circled loop);
  4. the step `locCostGe_locStep` 6d:1077, `locReg6Inv_locStep` 6d:1085, built from `localReg6d_locCostGe_term` 6d:955 and the term lemmas `localReg6d_ll_*` 6d:265-429; `hbad`, `hnb` of `LocStep` are not used (6d:60);
  5. the final step `locReg6_of_locCostGe` 6a:645, `locReg6far_of_locCostGe` 6a:653 (`scost_bot` 6a:560, `nElem_eq_zero_of_locStd` 6a:617) and the assembly `lw_localregular` 6d:1107.
- **Where the TeX step fails:** the 2-cycle collapse `R2` (`Contract`) at a bubble. Merged and compiled: `localReg6b_instCyc` 6b:1966, `scost ⊥ = 0` (6b:1980), after `Contract` `-2` (6b:1991), the witness `⊥` is not valid (6b:2025); delta `T2195b` (6b:58). `ord` does not change while two vertices lose their elementary pattern. E0 reproduces it: cost at the trivial merge `0 → -2`, `Φ^all = -2 → -2`: the minimum over merges is what is monotone.
- **Size.** `wc -l` of `6a`-`6d` = 1188 + 2382 + 1759 + 1510 = 6,839 (T2387:166 and the ticket say 6,366; (a) row 16 notes the difference; the files are unchanged since `37289f6`). This report uses `wc -l`.

## 2. P2: under lever S′ (T2395), the map and (1)-(6)

**The map** `img : BAPGraph → PGraph` (probe 32-48): promote the `=`-, `Ψ`-, `M`-dotted edges to `=`-dotted edges and take the band merge (`LGraph.merge`, `LWVocab.lean:778`), so the vertices of the image are the atoms (`BV:105`). Three deliberate differences from `B:308-313` (delta `T2397a`): (i) a solid edge inside an atom is **kept** as a circled loop (the paper discards it, but `ord` counts it, `B:353`); (ii) a solid edge between two atoms loses its circle (`CircIffLoop`); (iii) it gets a `×`-dotted edge, so the image is a normal band graph. The cost at atoms is `scostA Γ s = scost (promoteC Γ) s` for `s ⊇` atoms (probe 40). Difference (i) is T2395's K1.

| map property | statement (probe) | holds by | status |
|---|---|---|---|
| (m0) image normal, `CircIffLoop` | `BAImgNormal` 108 | construction of `promoteC` (flags, `×`-edges) | pin; proof: the classes of the promoted edges are the atoms |
| (m1) counters `n_S, n_W, n_V ↔ n_A, n_M` | `BAImgCounters` 115 | `BAGraph.counters_ofLGraph` BV:533 is the case without dotted edges (`scalingOrder_liftC` probe 256) | pin; new lemma |
| (m2) molecules = molecules of the image | `BAImgMol` 118 | `atom_subset_mol` BV:400, `mem_mol_iff` BV:394 | pin; new lemma |
| (m3) cost at atoms = band cost on the image | `BABridge` 111 | `LGraph.scost_relabel` 6a:401 + the class/atom bijection | pin; new lemma |
| (m4) simulation of the steps, up to relabelling | `BASimC` 129 (cost), `BASimP` 170 (paths); `baStep_of_simC` 137, `ba_ord_ge_of_simC` 148, `baPathStep_of_simP` 177 (proved) | the images are band terms up to renaming (E6); the transfers are `BABridge` + `scost_relabel` 6a:401, and `LGraph.localReg2_pathFam_map` LR2:616 | pin (R1 of T2395 + relabelling) |
| (m4′) the BA-only shapes of S′ | `BAShapeLL sh` 134, `BAShapePath sh` 174, `sh ∈ {s1, e1, e2, macroA, macroB}` | new local lemmas (§6 L3b3′); cost: E13 | pin; new lemmas |
| (m5) final step at vertex-level locally standard | `BAFinal` 67 | `#elem = 0`: an atom with a solid edge carries both colours (E7) | pin; new lemma (6a:560-663 analogue) |

**Evidence for (m4).** E6 (3,000 parents per step type; parent without `M` edge; selected vertices in distinct atoms; GG: the 2,525 parents whose `y`, `y'` are not the two external vertices): the image of every BA term equals, up to renaming, a band term of the same selection: `W1 = T1`, `W2 = T3`, `W3 = T2`, `W4 = T4` (`lweight`, `B:376-387`); `L1 = R3`, `L2 = D` (`lanlw`, `B:359-372`); `C1 = R3`, `C2 = R5`, `C3 = R7`, `C1w = R4`, `C2w = R6`, `C3w = R8` (`GGGamma`, `B:393-405`; `w = x` and `w` new in `(1 + M⁺S⁺)_{xw}`); `B2 = R2`, `B1 =` the transposed `R2` (the band reaches it by the selector `t` of `LocStep.gg`, LWLvl1.lean:3269), `A =` the merge-and-drop output of `R2` (`scost_partition_ge` 6a:503), with the circle convention of the partition outputs. E6b: the same with parents that already have atoms of several vertices. The BA formula has no band `R1` (`B:395`: a circled pair) and has both twisted `R2` copies.
**Lever S′ (T2395) and the strategy.** T2395 decided S′ = S + K1-K4 (T2395:1, :67-75): K1 the image keeps inside-atom edges (here `promoteC`); K2 the macro steps (a) `lanlw` then `lem_lweight` at the transfer loop, (b) `lanlw` then `GGGamma` at the transferred pair; K3 the measure `((K - ord)⁺, nExt, loops, n_S, pairs)`; K4 the identity half is BA's own ("Not transported" below). Its strategy `BALocStep` (T2395:85, `t/T2395` probe 207) acts **at atoms**: (1) an edge inside an atom first (a self-loop by `lem_lweight`, a proper one by macro (a)); (2) a bad atom by `lanlw`; (3) a same-colour pair at one vertex by `GGGamma`, at two vertices of one atom by macro (b). For (6) this gives: (i) one band `LocStep` at `img P` matches a step at `P` up to relabelling: Step 1 at the atom-level loop for (1) (`LocStep.weight` asks no `hwf`), Step 2 for (2), Step 3 for (3) at one vertex (at (2), (3) the image has no loop, so `hwf` holds; at (3) every atom has degree 0 or 2 and charge 0, so `hnb` holds). The first version's `BAImgSim` asked `img Q ∈ L'`, an equality of packed graphs that no row can prove (audit D1); `BASimC`/`BASimP` ask only that the cost bounds and the path invariant pass from `P` to a band graph `P'` and back from a band output `R` to `img Q`. (ii) The outputs are tagged (`BAShape` probe 123, `BTStep` 125): `band`, or one of T2395's BA-only shapes (T2395:41, :63, :78): `s1` (first sum of `GGGamma`, `y`, `y'` in two atoms), `e1` (`M_{αy}` of `lanlw` joining `[x]`, `[y]`), `e2` (an `M`-split joining two atoms joined by a parent edge), `macroA`, `macroB` (a macro step is one step; its outputs that are not `band`, including the stage-1 outputs of macro (b), which are band `(Oe1x)` term images at an atom where the band takes Step 3; the band term lemmas do not use `hbad`, `hnb`, 6d:60). (iii) A GG pair with an edge inside an atom (`[x] = [y]` or `[x] = [y']`), for which the first version priced "S'" (+550, **renamed S+GG**), does not occur under `BALocStep`: such an edge is an atom-level loop and priority (1) removes it first. **S+GG is subsumed by S′ and withdrawn**; T2395's S′ is the only S′ of this report. `[y] = [y']` is the band's `R2` `(δ, m)` term (T2395:63); `[y] ≠ [y']` is `s1`. (iv) The measure K3 (`nExt`) serves termination (G1, T2395 Step 4); (6) is an invariant along `BReach` (`ba_ord_ge` is an induction on reachability) and uses no measure. (v) S′ stops at atom-level locally standard graphs (T2395 `BAGraph.LocStd`); `BAFinal` and the conclusions of `ba_ord_ge`, `ba_ord_ge_of_simC` read vertex level (`locStdA`, delta `T2397e`). At atom level the final step is `locReg6_of_locCostGe`, `locReg6far_of_locCostGe` on `img Q` with (m1), (m3) and "distinct external atoms give distinct externals of `img Q`"; not compiled here, it is in row L3b4′ (§6).

**Properties (1)-(6) under the map** (`BALocReg` probe 188):

| prop | BA reading | band tool | map facts used | evidence |
|---|---|---|---|---|
| (1) locally standard | vertex level `locStdA` (probe 42; the paper's `deflvl1`); atom level = `LocStd (img Q)` is where S′ stops (§2 (v)) | the strategy's own output | none for (6) | E8b: 626 locally standard states, `ord ≥ 4` |
| (2) `n_M ≤ p`, `n_V ≤ n_W + 1` | `n_V` counts **atoms**: `LocReg2 (img Q) p` | `LGraph.molNV_le_molNW_add_one` LR:1778 on the image | (m0), (m1), (m2) | the vertex count fails at the start: 17 molecules (`p = 2`), 305 (`p = 4`); atoms 0 (E11); `T2397c` |
| (3)-(5) | `LocReg345 (img Q) p` from `PathInv2` of the image (probe 155-177) | `pathInv2_locStep` LR2:1582, `PathInv2.locReg345` LR2:1784 | (m2), `BASimP`, `BAShapePath`; (4) needs the colour of a vertex-level standard vertex at its molecule | E8b: `PathInv2` at 2.7e6 states, (3)-(5) at 626 locally standard states, 0 failures |
| (6) | `2p ≤ ord`, `3p ≤ ord` if the atoms of `x`, `y` differ | §1 items 1-5 | (m1), (m3), `BASimC`, `BAShapeLL`, (m5) | §3, E13 |

**The transport of `lw_localregular` (6) to BA under S′ is one theorem**, `ba_ord_ge_of_simC` (probe 148): from the initial values `h0` (`BAInit` probe 63), `BANormal`, `BASimC m T`, `BAShapeLL sh T` for the five shapes and `BAFinal`, through `baStep_of_simC` (probe 137: `locCostGe_locStep` 6d:1077 at the `band` outputs, the shape pins at the others) and `ba_ord_ge` (probe 95: init, step, final). Paths: `baPathStep_of_simP` (probe 177: `pathInv2_locStep` LR2:1582). Lean-checked at the start of `p = 2`: the 16 terms of `G = Ǧ + M` on `Γ_2` have `ord` `[2,3,3,2,3,4,4,3,3,4,4,3,2,3,3,2]` (`baStart2_orders` probe 325), and 7 have `x`, `y` in one atom (probe 327).
**Not transported:** the value conjuncts of `lw_localregular` (the expectation identity `(eq:local_Gs)`, the size bound of the errors, `Lvl1Reach` with its cutoff). Its identity conjunct assumes `M a a = m`, `M a b = 0` (6d:1117-1118), false at BA data ((a) row 13); at BA it comes from `baLanlw_holds` (`BAExpand.lean:744`), `baLweight_holds` (`BAExpandW.lean:354`), the `BAGGGamma` pin and `BAGraph.val_eq_partition` (BV:919), assembled in rows L3a. The transport above is (1)-(6) only.

## 3. P3: without S, the BA cost of a merge at atoms (paper-level argument, constants tracked)

Atoms (`B:302-304`, `BV:105`): the vertices of an atom are joined by `=`-, `Ψ`-, `M`-dotted edges; `M`- and `Ψ`-dotted edges carry no order (`B:345-355`). A merge of `Γ` is a setoid `s ⊇` atoms; `scostA Γ s` is the band cost with every edge inside a class circled. (`scaleatom` `B:316-319` and the decay of `M` bound sizes, not orders: (6) is counting and uses neither.)
1. **Initial values** (E5; the `2^{2p}` terms of `G = Ǧ + M` on `Γ_p`, `baSplitSolid` BV:163): `p = 1..4`: `min Φ^all = 2p`, `min Φ^far = 3p`, `min ord = p`; the terms with `x`, `y` in one atom (`Φ^far` vacuous) are 1/4, 7/16, 37/64, 175/256. The far corollary reads `atom(x) ≠ atom(y)`, not vertex-level `x ≠ y` (`T2397d`).
2. **Step lemma** `Φ(child) ≥ Φ(parent)` for `Φ^all` and `Φ^far`, on the 15 terms of the three expansions (`B:359-405`) and on their partition `G = Ǧ + M` (the `M` branch merges atoms and drops the edge, `BV:163`): E2, 1.999e7 pre-partition checks; E3, 1.486e7 checks on the partition outputs; parents random with `M` edges, all degeneracy classes (`[x] = [y]`, `[x] = [y']`, `[y] = [y']`, external atoms); 0 violations. The harness is sensitive: 10 of 14 mutants (a dropped waved edge or weight) are caught, the other four have slack (E10); the 12 band terms (transcribed from the Lean builders) give 5.40e6 checks, 0 violations (E1). The bound is sharp: slack 0 is attained for `W2, W4, L1, L2, A, B1, B2, C1, C2, C3, C3w` (E4).
3. **Why it holds:** the image of each term is a band term (§2), and the band local lemmas are proved for every graph and setoid; the BA partition is the band's up to the circle (the `M` branch is the band's `δ`-drop; a circled edge between atoms costs at least the band's uncircled edge, by Lemma A `LGraph.scost_cons_loop_ge` 6a:434 and `scost_partition_ge` 6a:503).
4. **Final step** (E7): `scostA(atoms) = ord + #elem` on 20,000 BA-normal graphs; on 3,000 vertex-level locally standard graphs `#elem = 0`, so `scostA(atoms) = ord`. Proof: an internal atom with a solid edge contains a vertex with a blue and a red half-edge, so its pattern is neither `(1,1,0,0)` nor `(0,0,1,1)`.
5. **End to end, `p = 2`, the deterministic strategy of `B:135-157` at the vertex level.** E8a (Φ, exhaustive: all 1,002 states of `ord ≤ 4`): `Φ^all ≥ 4`, `Φ^far ≥ 6` at every state, 0 violations, `ord` never falls. E8b (paths, exhaustive: all 40,337 states of `ord ≤ 5` and their 2.65e6 children): 626 locally standard states, `min ord = 4 = 2p`; none has the atoms of `x`, `y` apart, so every such locally standard graph has `ord ≥ 6 = 3p`. E9: `min Δord ≥ 0` on 4.9e6 random partition outputs (`Lvl1Good`, `LWLvl1.lean:989`).
6. **Constants:** `Φ^all ≥ 2p`, `Φ^far ≥ 3p`, `ord(Γ_p) = p`, `2^{2p}` terms: nothing else enters.
**Exact missing step: none for (6).** What the rows must prove under S′: (m0)-(m3), (m5), BA Lemma B, `BASimC`/`BASimP` from T2395's R1 matching and the relabelling lemmas, and the five shape lemmas `BAShapeLL` (cost: E13, 0 violations). GG inside an atom does not occur (§2 (iii)); the termination measure is T2395's.

## 4. P4: pins compiled against the merged vocabulary (`lake build RBM3D.Probe.T2397Pins` exit 0; 64 declarations, 63 on the standard axioms, `BAShape` on none; §8)

| rows | pin (probe line) | band original |
|---|---|---|
| L3b3′ | `BAInit p` 63 (`BAGraph.partition` of `ofLGraph Γ_p`), `locCostGeA` 50, `locReg6InvA` 54, `BAScostLL` 81 with `.trans` 86 (term level), `BAShape` 123, `BAShapeLL` 134 (the five shapes, packed) | 6a:927, 6a:177-182, 6a:168, 6b:92, 6d:955 |
| L3b4′ | `BAStep BStep` 73, `BANormal` 77, `BAFinal R` 67, `ba_ord_ge` 95 (proved), `BTStep` 125, `untag` 126, `BASimC` 129, `baStep_of_simC` 137 (proved), `ba_ord_ge_of_simC` 148 (proved) | 6a:645-653, 6d:1077-1136 |
| map (R0 / L3b-S1 of the first version) | `BAImgNormal` 108, `BABridge` 111, `BAImgCounters` 115, `BAImgMol` 118, `BAPathLift` 355 | BV:533, 6a:401, LR2:616 |
| L3b1-L3b2 | `BAPathInit` 155, `BAPathStep` 159, `BAPathFinal` 163, `BAMolVW` 167, `BASimP` 170, `BAShapePath` 174, `baPathStep_of_simP` 177 (proved), `BALocReg` 188 | LR:1929-1959, LR2:1577-1784 |

Instances (L4), name clash 0 (L5, §8): `inst_ba_ord_ge_p2` 313 (every hypothesis of `ba_ord_ge` discharged at `p = 2` by `fxyPowGraph_locReg6Inv`, `locReg6Inv_locStep`, `locReg6_of_locCostGe`, `locReg6far_of_locCostGe`, through the lift `liftC` probe 221, whose cost is the band cost, `scostA_liftC` 228); `inst_step1_p2` 320 (every output of the merged Step 1 at `Γ_2` has `Φ^all ≥ 4`, `Φ^far ≥ 6` at BA); BA-specific: `baStart2_orders`, `baStart2_xy_atom` (atoms of several vertices, by `decide`); **`inst_ba_ord_ge_of_simC_p2` 364**: every hypothesis of `ba_ord_ge_of_simC` discharged at the lifted band strategy `liftStepT` (330; every output tagged `band`): `BASimC` by `simC_liftStepT` 347 (`P' = P0`, `R = Q0`, transfers `locCostGeA_liftC`), the five `BAShapeLL` because the lift has no BA-only output (`tag_liftStepT` 340); `inst_step1_simC` 371 applies it at the Step-1 outputs at `Γ_2`; `inst_baPathStep_of_simP_p2` 377: `BASimP` by `simP_liftStepT` 356, only the conservativity pin `BAPathLift` (355, map row) stays a hypothesis. Limits: the lift has no `M` edge, so the shape pins hold there vacuously; their content is E13; (m0)-(m3) are pins, not proved; `BAStep`, `BAInit`, `BASimC` at `BALocStep`, `BAShapeLL` are the rows' targets.

## 5. C1 / L5

(6) and its invariant use no `g`, `κ`, `c = BAct_rate`, `ρ`: they are counts (E5, E7 are `g`-free). The constants of the same layer that depend on them are checked at `g = 1/64, 1, 10` with `κ` from `Im m` in (a) rows 6-12: window `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `lvl1Cutoff` `K = 80 / 120`, `K0 = 2`, `Im m ≥ κ` (`0.8325 / 0.3435 / 0.0439` at `L = 64`; `0.8325 / 0.3777 / 0.2620` at `L = 4`), Ward error ≤ 1.8e-14, decay ratio ≤ 3.8e-4. The truncation `e^{-c(log W)^{1+ε₁}}` of `B:317-319` is not used (L5): same-atom terms are handled by the `M`-decay ((a) row 14).

## 6. Row table L3b1-L3b6 (method of T2387:140-145: central = basis × ratio, TW 0.73/0.85/1.61, NW 0.85/1.20/2.10; E12)

| branch | row | basis | lo / central / hi | start |
|---|---|---|---|---|
| **twin** | L3b1 `LocalRegular` 1-2258 -(111-546), TW | 1,822 | 1,330 / 1,549 / 2,933 | after L3a5 |
| | L3b2 `LocalRegular2` 1-2068 -(120-562), TW | 1,625 | 1,186 / 1,381 / 2,616 | after L3b1 |
| | L3b3 `6a` 1-1188, `6b` 1-551, NW | 1,739 | 1,478 / 2,087 / 3,652 | after L3b2 |
| | L3b4 `6b` 552-2382, NW | 1,831 | 1,556 / 2,197 / 3,845 | after L3b3 |
| | L3b5 `6c`, NW | 1,286 | 1,093 / 1,543 / 2,701 | after L3b4 |
| | L3b6 `6d`, NW | 1,510 | 1,284 / 1,812 / 3,171 | after L3b5 |
| | **sum** | | **7,927 / 10,569 / 18,918** | |
| **S′** (G2's rows; R0, R1, L3b1, L3b2 are T2395's rows) | L3b3′ `BAScostS′`: BA Lemma B with `e2`, `e1`, `s1`, the macro (a) and (b) intermediates, `BAInit` (E14 items 200 / 120 / 200 / 60 / 150 / 80) | | 575 / 810 / 1,418 | after R0, L2c1, L2c2 (builders of `s1`, `e1`) |
| | L3b4′ `BAStepS′`: tagging of the `BALocStep` outputs, `BASimC` from R1 + relabelling, final step at atom level, assembly (`ba_ord_ge_of_simC`) and instances (E14: 80 / 120 / 60 / 120) | | 270 / 380 / 665 | after L3a3, R1, L3b3′ |
| | **sum S′ (G2)** | | **845 / 1,190 / 2,083** (T2395:150-151: 510 / 590 / 950) | |

S′ cancels all six twin rows (T2395:156). The first version's S rows S1-S4 (2,674 / 3,766 / 6,591) and S+GG are withdrawn: S1 is T2395's R0, S3's 15 image lemmas are T2395's R1, S4 is T2395's L3b1-L3b2; the same scope under S′ is 3,245 / 4,370 / 7,633 here against 2,910 / 3,770 / 6,500 in T2395 (E14). **Why G2's rows exceed T2395's L3b3 + L3b4 (1,190 vs 590 central):** T2395 prices `ScostLL` for the BA-only shapes as 40% of 6d §3 plus 100-300 new lines; this report adds (a) BA Lemma B (the `G = Ǧ + M` partition with `M`-splits that merge atoms, which also carries `e2`), (b) `BAInit` (the `2^{2p}` start terms are BA graphs, not band graphs), (c) the relabelling transfers inside `BASimC` (T2395's R1 matches invariants, not costs), (d) the atom-level final step (§2 (v)); the five shape lemmas are priced against the band primitives of the same shape (E14: `LoopPrims` 123, `Contract` 156, `MoveSC` 67, `Dmove` 209 lines). Bottom-up estimates, lo/hi = 0.71 / 1.75 × central (the NW factors of T2387), not measured twins. `BAShapePath` for the five shapes is in L3b1-L3b2 (T2395's rows) and not re-priced here.
**Split of the rows above 1,500 central (2149 budget note).** S′: none (L3b3′ 810, L3b4′ 380 central). Twin: L3b3 → L3b3a = `6a` whole (1,426); L3b4 → L3b4a = `6b` 1-1316, sections 1-8 (1,579) + L3b4b = `6b` 1317-2382, sections 9-12 (1,279); L3b6 → L3b6a = `6d` 1-749 (899) + L3b6b = `6d` 750-1510 (913); L3b1 (1,549) and L3b5 (1,543) stay (3 percent over). 8 rows, none above 1,579; the totals are preserved (4,284; 1,812).

## 7. Decisions, paper-delta candidates, limits

1. **Take S′ for (6)** (T2395, `d859e60`): release L3b3′ after R0, L2c1, L2c2 and L3b4′ after L3a3, R1, L3b3′; the shape list of `BAShape` is closed under T2395's Lemma E (the other outputs are band partition terms, T2395:99). No question to Jun.
2. If the dispatcher keeps the twin, L3b4-L3b6 wait for this report's audit as the ticket says; the 8-row split above applies.
3. **Deltas** (temporary tags): `T2397a` the atomic graph (`B:308-313`) must keep inside-atom solid edges (`B:353` counts them) and the image adds `×`-edges; `T2397b` (on `T2387c`, with T2395b) `B:416` asserts (1)-(6) with no argument: (6) is the cost route on the atomic image with five BA-only local lemmas; `T2397c` `(eq:MolVW)` counts atoms at BA (the vertex count fails at the start, E11); `T2397d` the far corollary reads `atom(x) ≠ atom(y)` (7/16 and 175/256 start terms have one atom); `T2397e` local standardness at BA, vertex level versus atom level (S′ stops at atom level, §2 (v)).
4. **Limits.** (1) Numerics are random parents (not all graphs) plus exhaustive runs of the deterministic strategy at `p = 2`; they are evidence for the proofs the rows must write, not proofs. (2) The BA terms are transcribed from `B:359-405` (D402's `(M⁺S⁺)_{xβ}` in the first two sums of `GGGamma` changes no image: `v ∈ [x]`); the Lean builders (L2c1, L2c2) do not exist, so the images are checked against the paper formulas. (3) `Ψ`-dotted edges are not produced by the three expansions and are not modelled. (4) `lweight` is used for weights, `lanlw` for edges inside an atom. (5) The S′ rows are bottom-up estimates. (6) (m0)-(m3) are Prop pins; `locStd_of_locStdA` and the final step are proved only at lifts. (7) `p = 4` was run only to `ord 5` (weights, E8c); E8a is exhaustive to `ord 4`, E8b to `ord 5`. (8) E13 classifies the S′ shapes on the term model of `steps.py` (vertex-level graphs, `S⁺_{xβ}` in the first sums of `GGGamma`); the graph-level image of the macro (b) intermediate and `BAShapePath` for the five shapes are not checked.

## 8. Repair (audit round 1, `docs/reports/T2397-audit.md`), Sun Oct 11 02:39:32 UTC 2026

- **D1** (required item 1): the literal `BAImgSim` and `baStep_of_sim`, `ba_ord_ge_of_sim`, `baPathStep_of_sim` and their instances are removed. Successors: the simulation up to relabelling `BASimC` (cost) and `BASimP` (paths), read through the transfers of the cost bounds and of `PathInv2` (probe 129, 170); `baStep_of_simC`, `ba_ord_ge_of_simC`, `baPathStep_of_simP` (proved). At the band lift `BASimC` is discharged (`simC_liftStepT`), so `inst_ba_ord_ge_of_simC_p2` has no hypothesis besides the reachability `hQ`; `BASimP` is discharged up to the conservativity pin `BAPathLift`.
- **D2** (required items 2, 3): §0, §2, §4, §6, §7 and line 1 follow T2395's S′ (K1-K4, `BALocStep` at atoms, macro steps, `nExt`); the five BA-only shapes are pinned (`BAShape`, `BAShapeLL`, `BAShapePath`) and priced (L3b3′, E14); their cost step is checked in E13; the first version's "S'" is renamed S+GG and is subsumed by S′ (§2 (iii)).
- Item 4: probe 385 lines (limit 400), this report within 300; build and `#print axioms` of all 64 declarations in the prove report, section Repair.

**E13** (cost step at exactly the S′ shapes; parents are random BA-normal graphs with at least one `M`-dotted edge; `S1` is the `GGGamma` term `A` with `[y] ≠ [y']`; `E1` the `M`-split of `G_{αv}` in `lanlw` `L1` with `[x] ≠ [v]`; `E2` every partition output of the three expansions with an `M`-split between two atoms of the term joined by a kept parent edge; macro (a) intermediate = that split with `[x] = [v]`, then `lem_lweight` at its loop `Ǧ_{ββ}`; macro (b) intermediate = `lanlw` `L2` with only `e₂` split and the far end of `q` in `[x]`, then `GGGamma` at `β` for a blue `q`):
```
$ cd $SCRATCH/T2397 && python3 r_shapes.py 100000 7 > ev/E13_shapes.out; cat ev/E13_shapes.out
parents with >= 1 M-dotted edge: 100000 per step kind (GG, weight, edge), seed 7
  E1 [y] external                                      checks    36,424  violations 0
  E1 [y] internal                                      checks    13,263  violations 0
  E2 (GGGamma) joined atoms ext-ext                    checks    56,887  violations 0
  E2 (GGGamma) joined atoms other                      checks   225,697  violations 0
  E2 (lanlw) joined atoms ext-ext                      checks    49,333  violations 0
  E2 (lanlw) joined atoms other                        checks   140,057  violations 0
  E2 (lweight) joined atoms ext-ext                    checks    60,452  violations 0
  E2 (lweight) joined atoms other                      checks    95,444  violations 0
  S1 y,y' two atoms: both ext                          checks    10,556  violations 0
  S1 y,y' two atoms: both int                          checks     1,966  violations 0
  S1 y,y' two atoms: one ext                           checks    14,537  violations 0
  macro(a) P -> stage 2 output                         checks 1,720,178  violations 0
  macro(a) P -> transfer intermediate                  checks    50,313  violations 0
  macro(a) intermediate -> stage 2 output              checks 1,720,178  violations 0
  macro(b) P -> stage 2 output                         checks 2,474,384  violations 0
  macro(b) P -> transfer intermediate (blue q)         checks    52,624  violations 0
  macro(b) P -> transfer intermediate (red q)          checks    52,256  violations 0
  macro(b) intermediate -> stage 2 output              checks 2,474,384  violations 0
  total checks 9,248,933, violations 0
  min (Phi^all(child) - Phi^all(parent), ord(child) - ord(parent)) per shape: E1 [y] external: (2, 0), E1 [y] internal: (2, 2), E2: (0, 2), S1 y,y' two atoms: both ext: (0, 0), S1 y,y' two atoms: both int: (0, 2), S1 y,y' two atoms: one ext: (0, 2), macro(a) intermediate: (0, 0), macro(b) intermediate: (0, 0)
  sensitivity (one waved edge of the output dropped; caught = violations): E1: 0/49,687, S1: 9,640/27,059, macro(a) intermediate: 49,907/50,313, macro(b) intermediate: 101,698/104,880
```
`min` is the lexicographic minimum of `(ΔΦ^all, Δord)`: slack 0 occurs at `S1`, `E2` and both intermediates, so the bounds are sharp; `ΔΦ^far` is checked in the same comparison. Sensitivity: `E1` has slack 2, so dropping a waved edge (which costs 2) is not caught there.
**E14** (rows, §6):
```
$ cd <worktree> && python3 -I $SCRATCH/T2397/r_rows.py > $SCRATCH/T2397/ev/E14_rows.out; cat $SCRATCH/T2397/ev/E14_rows.out
band analogues (lines, from-to): 6b s6 LoopPrims (Loop, AddLoop, MoveLoop) 123 (554-676); 6b s9 ContractPrim (Contract) 156 (1319-1474); 6c s6 MoveSC 67 (1093-1159); 6c s8 Dmove 209 (1231-1439); 6a scost_cons_loop_ge (Lemma A) 29 (434-462)
L3b3' BAScostS' (the five BA-only ScostLL lemmas, BA Lemma B, BAInit): lo/central/hi 575 / 810 / 1,418
     200  BA Lemma B (G = G^ + M: merge-and-drop, circled edge by Lemma A) with E2 (merge of two atoms joined by a kept edge)
     120  E1 (lanlw T1, M_{alpha y}: [x], [y] merged, edge dropped; leaf as AddLoop)
     200  S1 (y, y' in two atoms: pair contracted to a waved edge, [y], [y'] merged; analogue Contract)
      60  macro (a) intermediate (image = MoveLoop term, E6c; image lemma + import of scostLL_moveLoop)
     150  macro (b) intermediate (analogue MoveSC; graph-level image not checked: hi covers a new Dmove-size primitive)
      80  BAInit (2^{2p} start terms: Lemma B + fxyPowGraph_locCostGe)
L3b4' BAStepS' (step along BALocStep, assembly of (6)): lo/central/hi 270 / 380 / 665
      80  tagging of the BALocStep outputs (macro steps one step each) (BTStep; T2395 L3a3 definitions)
     120  BASimC from R1 (graph-level matching) + BABridge + scost_relabel
      60  final step at atom level (img LocStd, (m1), (m3), distinct external atoms)
     120  assembly ba_ord_ge / baStep_of_simC / ba_ord_ge_of_simC (probe) + instances
G2 rows under S' (L3b3' + L3b4'): 845 / 1,190 / 2,083;  T2395 L3b3 + L3b4: 510 / 590 / 950;  difference central +600
rows of T2395 that carry the rest of the old S rows (R0, R1, L3b1, L3b2): 2,400 / 3,180 / 5,550
old S rows of this design (S1-S4): 2,674 / 3,766 / 6,591;  same scope under S' (R0, R1, L3b1, L3b2, L3b3', L3b4'): 3,245 / 4,370 / 7,633;  T2395's pricing of that scope: 2,910 / 3,770 / 6,500
```
