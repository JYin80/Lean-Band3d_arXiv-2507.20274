Prover model: claude-sonnet-5-5
# T2472b (BA-L L3d4b, `RBM3D/Graph/BAProvB.lean`): stage 1b report, written Tue Oct 13 00:04:04 UTC 2026
Scope: ticket `docs/tickets/T2472.md`, targets 5 (b), 6, 7, 8 (a)(b), 10, plus the root import line. Branch `t/T2472b` (worktree `RBM3D-wt/T2472b`), stacked on `t/T2472` e7ada40a; main merged first (merge fdac18ed, main 2dcfcda5).
Section (a) is `docs/reports/T2472-prove.md` (a), (a″) and `T2472-1a-audit.md` (PASS, interface table (viii), pre-signed split, no switch to `prover-max`); not repeated and not edited; no (a′) correction was needed. L3d4a `Graph/BAProv` (targets 1-4, 5 (a), 9) is on main (c4b39007) and untouched.

## (b) Script output
```
$ TZ=UTC git log --format='%h %ad %s' --date=format-local:'%Y-%m-%d %H:%M:%S UTC' -7 | cut -c1-110
0c7e272e 2026-10-12 23:59:04 UTC T2472b: BAProvB drops the unused open private names
f362b709 2026-10-12 23:56:19 UTC T2472b: BAProvB section 8 (compiled instances ... ) and the root import
7319b6d7 2026-10-12 23:49:59 UTC T2472b: BAProvB sections 6-7 (recursion with provenance, engine with provenance, 8 (b))
97691878 2026-10-12 23:43:32 UTC T2472b: BAProvB sections 4-5 (positions of the five frame kinds ... the step lemma with positions)
51ed2f4f 2026-10-12 23:36:41 UTC T2472b: BAProvB sections 1-3 (weighted expansion of an extension, ... lw, gg, lanlw and the two macros)
fdac18ed 2026-10-12 23:19:20 UTC Merge branch 'main' into t/T2472b
2dcfcda5 2026-10-12 23:13:56 UTC T2477: merge BA M/N N3b (...)
$ wc -l RBM3D/Graph/BAProvB.lean      # stop size 2,000; at the section commits: 500, 806, 1126, 1239; after pruning unused `open private` names:
    1238 RBM3D/Graph/BAProvB.lean
$ lake build RBM3D.Graph.BAProv RBM3D.Graph.BAProvB     # the committed file 0c7e272e (start 23:59:04 UTC)
✔ [3953/3953] Built RBM3D.Graph.BAProvB (12s)
Build completed successfully (3953 jobs).
$ lake build        # the whole library, runs #assert_rbm_axioms
info: RBM3D.lean:549:0: axiom audit: 14149 theorems, 4467 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4317 jobs).
```
`#print axioms` of all 72 public declarations of the file (names by script from the file): 69 print exactly `[propext, Classical.choice, Quot.sound]`; the other 3 (the defs `BAProv_ppA`, `BAProv_ppB`, `BAProv_qqB`) print `[propext]`. The targets:
```
BAProv_lw_W BAProv_gg_W BAProv_lanlw_W BAProv_macroA_W BAProv_macroB_W BAProv_twist_EW BAWExp.twist BAProv_frameStep_posW   [propext, Classical.choice, Quot.sound]
BAProvStepPos baProv_stepPos BAProv_exists_ne baProv_exists BAProv_start_W BAProv_startOuts_good                         [propext, Classical.choice, Quot.sound]
ba_localregularXP_ne BAEngineProv ba_localregularXP baEngineProv_imp_localregularX                                         [propext, Classical.choice, Quot.sound]
```
Target statements, extracted by script (file line, declaration up to `:=`, cut at 165 characters; the two Prop-valued targets `BAProvStepPos`, `BAEngineProv` are printed in full below):
```
259: theorem BAProv_lw_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (Γ : BAGraph E I) (p : SEdge (E ⊕ …
282: theorem BAProv_gg_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (Γ : BAGraph E I) (p q : SEdge (E …
347: theorem BAProv_lanlw_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (Γ : BAGraph E I) (p : SEdge ( …
399: theorem BAProv_macroA_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (Γ : BAGraph E I) (p : SEdge  …
454: theorem BAProv_macroB_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (Γ : BAGraph E I) (p q : SEdg …
730: theorem BAProv_frameStep_posW (d : ℕ) (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) {F : List (BAPGraph (Fin 2))} (h : BAFrameStep P F) : BAPro …
762: theorem BAProv_twist_EW (g0 Em t : ℝ) (m : ℂ) {E : Type} (Q : BAPGraph E) (c t' : Bool) (Wt : (Q.E' ⊕ Q.I' → Idx d L W) → ℝ) (ℓe : E → Idx d L W) : ∫ ω, (Q.tw …
772: theorem BAWExp.twist {d : ℕ} {P : BAPGraph (Fin 2)} {ps : List (BAProvOut P)} (c t' : Bool) (h : BAWExp d P ps) : BAWExp d (P.twist c t') (ps.map (BAProvOut.t …
796: theorem baProv_stepPos (d : ℕ) : BAProvStepPos d
913: theorem BAProv_exists_ne (d : ℕ) (K : ℤ) (Γ : BAPGraph (Fin 2)) (hN : Γ.g.Normal) : ∃ oP eP : List (BAProvOut Γ), (∀ o ∈ oP ++ eP, o.ExtOK ∧ o.Molecular) ∧ BA …
938: theorem baProv_exists (d : ℕ) (K : ℤ) (Γ : BAPGraph (Fin 2)) (hN : Γ.g.Normal) : ∃ oP eP : List (BAProvOut Γ), (∀ o ∈ oP ++ eP, o.ExtOK ∧ o.Molecular) ∧ BAPro …
1026: theorem ba_localregularXP_ne (p : ℕ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) : ∃ outs errs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))), outs …
1104: theorem ba_localregularXP : BAEngineProv
1115: theorem baEngineProv_imp_localregularX (h : BAEngineProv) : BAProv_LocRegXClosed
$ sed -n 792,794p / 1097,1102p / 1110,1112p RBM3D/Graph/BAProvB.lean
def BAProvStepPos (d : ℕ) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), BALocStep P L → P.g.Normal →
    ∃ ps : List (BAProvOut P), ps.map (·.Q) = L ∧ (∀ o ∈ ps, o.ExtOK ∧ o.Molecular) ∧ BAWExp d P ps
def BAEngineProv : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))),
    (∀ o ∈ outs ++ errs, o.ExtOK ∧ BACoverBy (P := o.Q) fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k))) ∧
    BALocRegConcl p c K0 d D (outs.map (·.Q)) (errs.map (·.Q)) ∧
    (∀ o ∈ outs ++ errs, p ≤ o.Q.g.waved.countP (fun e => !e.col)) ∧
    BAWExp d (baPG (BAGraph.ofLGraph (fxyPowGraph p))) (outs ++ errs)
def BAProv_LocRegXClosed : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)
```
Statement diff against the probe texts fixed at the 1a-audit (`stmtdiff.py`: declarations of `RBM3D/Probe/T2472Pins.lean` and `BAProvB.lean`, docstrings stripped, whitespace normalised; the probe's `T2472_LocRegXClosed` is read as `BAProv_LocRegXClosed`):
```
SAME BAProvStepPos    SAME BAEngineProv    SAME BAProv_LocRegXClosed    SAME baEngineProv_imp_localregularX
```
Pins against the check (`T2472-check.lean`, compiled on the branch): the check file plus `import RBM3D.Graph.BAProvB` and the four examples
`example : T2472_LocRegXClosed := baEngineProv_imp_localregularX ba_localregularXP`, `example : T2472_FxyDUniv := @fxyValD_univ`, `... FxyDUnion := @fxyValD_union`, `... Bridge := @baProv_bridge`:
```
$ lake env lean check_on_branch.lean ; echo exit=$? error_lines=$(grep -c error ...)      # and the unmodified docs/tickets/checks/T2472-check.lean
exit=0 error_lines=0          (plain check file: exit=0, 0 error lines)
```
Compiled nonempty instances (section 8 of the file, `d = 3`, `L = 4`, `W = 2`, flow point `(g0P, EP, t0P, m0P)` with `flowP_data`, labels `ℓ0`; every deterministic hypothesis discharged, no external premise):
```
1132 ba_localregularXP_ne 2 (1/4) _ 2 3 10   (target 8: lists non-empty, ExtOK + cover, BALocRegConcl, >= 2 black waved edges, BAWExp)
1135 baEngineProv_imp_localregularX ba_localregularXP 2 (1/4) _ 2 3 10      1138 the pinned text of T2472_LocRegXClosed proved by it
1143 BAWExp.prod on the engine's non-empty list (p = 2, weights BAProv_w: 1 at ℓ0 0, 1/2 elsewhere, not the leaf)
1152 BAProv_startOuts 2: 16 outputs, ExtOK, Molecular, covered      1156 BAWExp.prod on BAProv_start_W at the flow point
1164 gg at P_A (31 outputs)   1166 within at P_B   1169 ggSplit at P_C   1172 edge at P_E   1175 weight at the first start term (E = Fin 2): BAProvPosW
1182 target 6: baProv_stepPos at locStepB / normalB: ps non-empty, ExtOK, Molecular, BAWExp evaluated at the flow point with the weight BAProv_wt
1197, 1199 BAProv_exists_ne at baGGLhs (K = 10), baProv_exists at the twist of P_B (K = 3)      1229 target 7 with the weighted expansion at the flow point
1207 BAProv_lw_W   1210 BAProv_gg_W   1213 BAProv_lanlw_W   1216 BAProv_macroA_W   1219 BAProv_macroB_W   1223 BAProv_twist_EW   1225 BAWExp.twist (target 5 (b))
```
Greps and hygiene (new file; output verbatim, counts by `grep -c`/script):
```
$ grep -nE "sz\.lam|withLam|Sizes|gK" RBM3D/Graph/BAProvB.lean | wc -l       -> 25 lines: line 27 (the `open` of the namespace RBM.Gauss.Sizes), line 49 (inside the proof of the public
   BAProv_integrable_term) and 23 lines inside the two PRIVATE helpers BAProv_step_W (13) and BAProv_lanlw_core (10); all but line 27 are `lwWxSizes d L W 0 hL` (the merged sequence-space construction used by
   BAWeightOp_core / BAExpandW_term_integral); none is `sz.lam`, `withLam` or `gK`
$ python3 uba.py     # the 72 public declarations, statements only (docstrings stripped; theorems cut at `:=`)
public theorem/def statements scanned: 72 | with a Sizes/sz.lam/withLam/gK hit: []
$ grep -nE "BAShapeLL|BAFrameStepTN|T2472_Binder" RBM3D/Graph/BAProvB.lean
1033:  have hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN := by      (inside the proof of ba_localregularXP_ne; no statement)
$ grep -cE "sorry|admit|native_decide|^axiom|^inductive|^structure|maxHeartbeats" RBM3D/Graph/BAProvB.lean
0
$ git diff --name-only main...t/T2472b          # main 0f3ecb6b (T2476) at the check
RBM3D.lean
RBM3D/Graph/BAProvB.lean
RBM3D/Probe/T2472Pins.lean          <- on the branch since t/T2472 (1a probe), never merged: bring in BAProvB.lean and the one import line only
$ grep -rln "RBM3D.Graph.BAProvB" RBM3D.lean RBM3D            # importers
RBM3D.lean
```
Name-clash grep of the 72 new public names (word-bounded alternation), `git grep -l -E` on `main` 0f3ecb6b and on the 82 branches `t/T24*` other than `t/T2472`, `t/T2472b` (run Mon Oct 12 23:57:47 UTC):
```
main files with hits:            (none)
branches scanned 82, with hits 0
```
`open private` (used only through `open private ... from`): `BAWeightOp_core`, `BAWeightOp_sd` (BAWeightOp); `BAGGOp_core` (BAGGOp); `BAExpandW_integrable_PF` (BAExpandW); `BALvl1A_data_zero`, `BALvl1A_lwSplit_last`, `BALvl1A_sum_eraseIdx` (BALvl1A); `BAEngine_frame_ne_nil`, `BAEngine_integral_comb`, `BAEngine_partition_ne_nil`, `BAEngine_Spec` (BAEngine). No private deleted, no merged file edited. Ports: none from RBM1D/RBM2D (no diff-stat owed); twins of the band `Graph/LWProv.lean` (`:821-1820`), cited in the docstrings.
Lines per section (file 1,238; header 30): 1 integrability/extension 90, 2 step from core + t = 0 121, 3 weighted identities lw/gg/lanlw/macros 257, 4 positions 242, 5 twist/step lemma 64, 6 recursion 145, 7 engine 174, 8 instances 115. Central 1,295 (1a-audit §8), stop line 2,000: not reached.

Narrative
- The route of G5-a (iii) was carried out as predicted: every step identity of the merged chain is proved per labelling of the old vertices (`BAWeightOp_core`, `BAGGOp_core`, `BAExpandW_term_integral`, all on the sequence space); multiplying by the real weight `Wt(ℓe, ℓi)` and summing over `ℓi` gives the weighted identity `E Γ.valW = Σ_T E T.valW` with the weight read through `owxEmb k`.
- `BAProv_step_W` (private, section 2) is that argument once for `lw`/`gg`/`lanlw`: the new-label sums `BAProv_R` (the integrand of `BAWeightOp_R`/`BAGGOp_R`), the transport `PF ↔ seqP` by `lwWx_integral`, and the case `t = 0` (every term has a waved edge with `S = S⁺ = 0`; the selected edge `Ǧ` vanishes).
- The macros `within`, `ggSplit` are compositions at the graph level (no new core): `lanlw` weighted, the pathwise splits `BAProv_macroA_term`, `BAProv_macroB_term` (weighted twins of the private `BALvl1A_macroA_val`, `_macroB_val`), and `lw` resp. `gg` weighted at the transfer graph with the weight `Wt ∘ owxEmb 2`. The weights compose as `ℓ ∘ (e₂ ∘ e₁)`.
- Section 4 turns a graph-level identity into `BAWExp` for the explicit position list `BAProv_provOuts P emb Ts` (weighted `BALvl1A_pack`): `BAGraph.valW_partition` (L3d4a), the child read through `P.ext` (`BAProv_pcomp_valW`), integrability (`BAProv_integrable_pvalW`), and the non-factoring case (both sides `0`).
- The twist (target 6): `BAProv_twist_valW` (from `BASymm1_term_twist`, the weight is real) and `baTwistIntegral_gen` give the weighted twist; `BAWExp.twist` carries the maps unchanged; `baProv_stepPos` is the frame step at `P.twist c t` twisted back by `BALvl1A_twist_invol`.
- `BAProv_aux`/`BAProv_exists_ne` is `BALvl1C_aux` with maps (strong induction on `BALvl1Mu`), carrying also `oP ++ eP ≠ []`; `baProv_exists` forgets it. `BAProv_comp_pos` is `lwProv_WExp_comp_pos`.
- The engine: per start output `o` (`BAProv_startOuts p`, the explicit `ofTerm` with `vmap`, `BAProv_startOuts_good` repeats the cover argument of `BAProv_start` for the explicit maps) the recursion at the cutoff `lvl1Cutoff c K0 d D o.Q.g.counters`, composed with `o`; `baEngine_assemble` with the binder discharged by `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn` (inside the proof only). `ba_localregularXP_ne` carries the non-emptiness for the instance of target 10; `ba_localregularXP : BAEngineProv` is its projection.
- One defect found by the full build and fixed: the premise scan of `Test/Axioms.lean` reported the Prop-def `BAProv_Lvl1Body` (taken as a hypothesis by the helper `BAProv_Lvl1Body_spec`, concluded only under `∃`); the helper is now `private` and the premise scan passes (second full build). `Test/Axioms.lean` is unchanged; no registry entry.
- Role: the switch conditions of 1a (xiii) did not occur (no new shadow molecule, every identity per labelling, as in the 1a-audit §8); the stop rules of the ticket were not hit (largest file 1,238 < 2,000; no new `inductive`; no `Sizes`/`sz.lam` in a public statement; no merged file edited; no unproved `Prop` premise in a public result).
- The `x ~ y` outputs stay in the lists of `ba_localregularXP` (`2p ≤ ord` only); their M-chain bound is L3d2b's (1a (vii), 1a-audit O4); nothing of it was touched here.

Hypothesis table (C1; premise, band discharge, BA discharge):
| result | premises | band | BA |
|---|---|---|---|
| `BAProv_lw_W`, `_gg_W`, `_lanlw_W`, `_macroA_W`, `_macroB_W` | `3 ≤ L`, `BASelf d L g0 Em m`, `0 ≤ t < 1`; the selected edges blue and circled (loop / pair / `lwSplit` membership) | `GaussIBP`, `M = mI`, flow | exactly `hL hSelf ht0 ht1` and the edge hypotheses of the `BAFrameStep` constructor; no smallness of `g`, no `M = mI`, no `Normal` |
| `BAProv_*_posW`, `BAProv_frameStep_posW` | `∀ e ∈ P.g.dotted, e.eq = false` | `Normal` | weaker than `Normal` |
| `BAWExp d P ps` (def), `.twist` | `3 ≤ L`, `BASelf`, `0 ≤ t < 1`, every real `Wt` | as above | binder of the def; `.refl`/`.comp`/`.prod` (L3d4a), `.twist`, `BAProv_comp_pos`, `BAProv_start_W` conclude it |
| `baProv_stepPos`, `baProv_exists` | `P.g.Normal` | `Normal` | `Normal` (as the band) |
| `ba_localregularXP`, `_ne` | `0 < c` | `∀ m` (band `lw_localregularXP`) | `0 < c` only; the binder of `ba_localregularX` is discharged inside |
| `baEngineProv_imp_localregularX` | `BAEngineProv` | — | the engine itself (concluded by `ba_localregularXP`) |
Census (1a (iv)) of what each step used: lw: `BAWeightOp_core` (private, `open private`); gg: `BAGGOp_core` (private); lanlw: `BAExpandW_term_integral` (public) in `BAProv_lanlw_core`; macros: `BALvl1A_lwSplit_last`, `BALvl1A_sum_eraseIdx` (private) and the new pathwise twins; twist: `BASymm1_term_twist`, `baTwistIntegral_gen` (public); recursion: twin `BAProv_aux` of the private `BALvl1C_aux` with `baLvl1ExistsStep_holds`, `baLvl1StepGood_holds`, `ba_lvl1_mu_lt`, `baLvl1Lt_wf`, `ba_lvl1_induction`; engine: `baEngine_assemble`, `BAEngine_Spec` (private), `ba_nWS_ge`, `baStart_nWS`; integrability `BAExpandW_integrable_PF`, `BALvl1A_data_zero` (private). No step needed a sum over the old labels before the identity (G5-a (iii), switch (b)).
Interface table for L3d2b and L5 (names of this row; the L3d4a names are in `T2472-prove.md` (b)):
| band consumer | BA name | file |
|---|---|---|
| `lwMomentExp_pin_gen` `LWMomentExp:1302-1345` (engine call :1325) | `ba_localregularXP : BAEngineProv`; `ba_localregularXP_ne` (same, lists non-empty); lists, `BALocRegConcl` (a)-(d), `p ≤ n_{W,black}`, `BAWExp` | `BAProvB` |
| `lwMomentExp_expand` :390-460 (`WExp.prod` :404) | `BAWExp.prod` (L3d4a) on the `BAWExp d S (outs ++ errs)` conjunct; `baStart_nWS` (BAEngine) | `BAProv`/`BAProvB` |
| `lwMomentExp_rep` :1000-1016 | the cover conjunct of `BAEngineProv` with `BACoverBy.rep` (L3d4a) | `BAProv`/`BAProvB` |
| the unweighted pin of the engine | `baEngineProv_imp_localregularX` | `BAProvB` |
| `LWTermHolds:1524` (L5) | nothing from `BAProv*` | — |

## (c) Verified Mathlib names used (script-extracted from the file, 69 identifiers, `#check @…` of each in `mathlib_chk.lean`: 68 succeed; the one failure, `Tame.integrable`, is a project name that needs `open RBM.Green`, not a Mathlib name; none invented, none found absent)
Filter.Eventually.of_forall; Finset.mul_sum, sum_add_distrib, sum_congr, sum_eq_zero; Function.comp_assoc, comp_def; List.any_eq_true, append_assoc, append_eq_nil_iff, append_nil, cons_append, exists_mem_of_ne_nil, flatMap_congr, flatMap_map, length_map, length_nil, map_append, map_congr_left, map_cons, map_flatMap, map_map, map_nil, mem_append, mem_append_left, mem_append_right, mem_cons, mem_cons_of_mem, mem_cons_self, mem_flatMap, mem_map, mem_map_of_mem, mem_singleton, nil_append, not_mem_nil, prod_cons, prod_eq_zero, prod_nil, sum_append, sum_cons, sum_eq_zero, sum_map_add, sum_map_mul_left, sum_nil; Matrix.of; SimpleGraph.ConnectedComponent.ind, Reachable.refl; continuous_const, continuous_finsetSum (the deprecated `continuous_finset_sum` is not used), integrable_const, integrable_finsetSum, integrable_zero, integral_add, integral_congr_ae, integral_const_mul, integral_finsetSum, integral_zero; le_trans, map_list_sum, map_mul, map_sum, map_zero, mul_add, mul_one, not_le, zero_mul.
(`Tame.integrable`, `gaussIBP`, `lwWx_integral`, `lvl1_sum_flatMap`, `owx_*` are project names used in the compiled file.)

## (d) Open issues and paper-delta candidates
- Open: nothing of targets 5 (b), 6, 7, 8, 10 is left. For the merge (hub): bring in `RBM3D/Graph/BAProvB.lean` and the line `import RBM3D.Graph.BAProvB` (placed after `import RBM3D.Graph.BAProv` in `RBM3D.lean`); `RBM3D/Probe/T2472Pins.lean` stays on the branch (never merged). Main moved to 0f3ecb6b after my merge, so `RBM3D.lean` may need a textual merge of the import block.
- Open (unchanged from the 1a-audit): the `x ~ y` outputs, 4,006 of 10,900 in the numerics, stay in the lists (`2p ≤ ord`); L3d2b owns the M-chain bound (asymptotic in `W`, 1a-audit O4); the rooted G3 and the weighted homogeneity (`BAReal`) are L3d2b's.
- T2472d (Lean/paper): the weighted expansion of a step is proved per labelling of all old vertices (the weight `Π_k 1_{Dm}([β^{(k)}])` of `7_8:1631-1650` is a function of the labelling of the start graph, read through `π` along the recursion); in the paper the same expansion is performed on the product `|f_{xy}|^p` and the domains are read off the resulting graphs (relates to T2472a, T2472c).
- T2472e (Lean/paper): `BAEngineProv` indexes the outputs by position with their own maps; equal graphs at two positions may carry different maps (the Amend-2 form of the band, `lwProv_LocStepXProvPos`); the paper speaks of the set of locally standard graphs. The Lean lists also carry `BAWExp` and the non-emptiness `ba_localregularXP_ne`, neither of which is in `lem:localregular`.
