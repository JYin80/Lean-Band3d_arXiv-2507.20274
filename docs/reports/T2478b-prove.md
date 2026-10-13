Prover model: claude-sonnet-5-5
## (a) Math preflight (stage 1a)
Not repeated: `docs/reports/T2478-prove.md` lines 1-94 ((a) and (a′); verdict PASS; target 9 "go" by (a′) 1) and `docs/reports/T2478-1a-audit.md` (round 2, PASS). This report is T1b = targets 7-11 (branch `t/T2478b`); T1a = targets 1-6 is on `main` (6039f7ed).

## (a′) Preflight corrections — Tue Oct 13 02:00:10 UTC 2026
Author: claude-sonnet-5-5 (stage 1b). Section (a) is not edited. None of entries 1-4 changes a verdict; entry 3 is for the dispatcher.
1. Row 22 "`open private` list: empty" was computed for the band files of targets 1-8; target 9's proof opens three private helpers of `LocalAvg2`: `la2_zdistInf_add_le`, `la2_zdistInf_neg`, `la2_zdistInf_zero` (`Step2CloseGen.lean:49`).
2. Rows 16/18: the delivered target-9 block is 639 lines (`Step2CloseGen.lean:166-804`) against the itemised 525 (range 400/740). The regularity `(eq:Psirelations)` is replaced by the shift lemma on the explicit `Bparam` (`Step2CloseGen_STWB_shift`), the lattice sum by the product bound `Step2CloseGen_latsum`, the floor `W^{-D}` by `Step2CloseGen_floor`; no paper input beyond the pin `STGijDecgL`.
3. Ticket target 11 ("every pin discharged by merged band producers and `LWtermExp d` as a hypothesis"): the delivered corollary has four hypotheses `LWterm d`, `LWtermExp d`, `STEMn2Exp d`, `STGridMart d`. `LWterm`: `STOptL2` needs `STLWB`, whose producer `lwterm_holds` is in the excluded `Graph/LWTermHolds`. `STEMn2Exp`: the cone of `stEMn2Exp_holds` (`Induction/EMn2Exp2`) contains `BA.FlowPins`, `BA.MFixedPoint`. `STGridMart`: `stGridMart_holds` (`Path/DifREP2`) has a BA-free cone but 22 further modules, among them `StepDecompN`, `LoopC2N`, `HierarchyN`, `GridDriftN`, `AzumaProxyN` (cone lines in (b) (2)).
4. Dispatcher answer (5): `StepDecompGen_LoopForm` (`Chain/StepDecompGen.lean:60`) has per `n` the four conjuncts `0 < Im m`, `LM = loopFine`, `LIM = loopL`, `eta = etaOf`; nothing about `KI`. It gives only the first conjunct of `Step2IterGen_ListLink` (`LM = LIM ∘ KLloopOf`, with `loopM_eq_loopL`), not `KI ∘ KLloopOf = K`. The bridge was not used (no `StepDecompGen` import).

## (b) Script output, T1b = targets 7-11 — Tue Oct 13 02:00:10 UTC 2026
Files: `RBM3D/Chain/OptL2Gen.lean` (targets 7, 8), `RBM3D/Chain/Step2CloseGen.lean` (targets 9, 10, 11), `RBM3D/Test/Axioms.lean` (registry). Branch `t/T2478b`, HEAD 3166b5d9, stacked on `t/T2478`; `main` merged in first (45669a82; merge-base with main 6039f7ed). Ports are from the same-repository band files `Induction/OptL2a.lean`, `OptL2b.lean`, `LocalAvg2.lean`, `Step2Iterate.lean` (not edited); nothing from RBM1D/RBM2D, so no RBM1D/RBM2D diff-stat.

### (1) Lines per file against the stop line (CONTROL H134: `wc -l` at every commit; stop 2,000 per file; reserve 1,800)
```
$ for h in $(git log --format=%h --reverse 45669a82..HEAD): git show $h:<file> | wc -l      (columns: OptL2Gen, Step2CloseGen; 45669a82 = merge of main)
005cee52   575     0  T2478b: OptL2Gen sections 1-3 (OptL2aJg, drift step, premises, grid events, pathwise
978f8e0e  1032     0  T2478b: OptL2Gen target 7 (stOptL2a_driftg, _martingaleg, _gronwallg)
a6b43968  1415     0  T2478b: OptL2Gen target 8 (stOptL2_of_pinsg), band re-derivations and instances
8b7996fe  1417   910  T2478b: Step2CloseGen (targets 9-11: STGijDecgL reader, section 12.2 identities, ban
91e3dca8  1417   910  T2478b: registry (STStep1LoopgL owed; STOptL2gL concluded by stOptL2_of_pinsg)
c541a2f9  1423   920  T2478b: module docstrings, TN-C4 grep, warnings
ac330398  1423   921  T2478b: Step2CloseGen corollary docstring (cone facts)
53c1b613  1423   921  T2478b: OptL2Gen band bridge name carries the file stem
c439064d  1423   921  T2478b: Step2CloseGen identity instances at n = 100
3166b5d9  1423   921  T2478b: Step2CloseGen corollary docstring (cone numbers)
$ wc -l RBM3D/Chain/OptL2Gen.lean RBM3D/Chain/Step2CloseGen.lean
1423 RBM3D/Chain/OptL2Gen.lean
921 RBM3D/Chain/Step2CloseGen.lean
2344 total
```
No file reaches the stop line (max 1,423), no reserve hand-over. T1b total 2,344 lines against the 1a central 1,904 ((a′) 2 of `T2478-prove.md`) and the 2.6x reference 4,950; the pre-signed split T1a (targets 1-6) / T1b (targets 7-11) stands, no third row.

### (2) Build, axioms, premise scan, layout
```
$ lake build RBM3D.Chain.OptL2Gen RBM3D.Chain.Step2CloseGen 2>&1 | tail -1
Build completed successfully (3854 jobs).
$ lake env lean RBM3D/Chain/OptL2Gen.lean | wc -l ; lake env lean RBM3D/Chain/Step2CloseGen.lean | wc -l     # all warnings and errors of the files
0
0
$ lake env lean <scratch>/axioms.lean    # #print axioms of the 21 public theorem/def of the two files; counted:
  21 declarations, axiom sets: ['[propext, Classical.choice, Quot.sound]']
  OptL2aJg, optL2Gen_bandStep2_OptL2aJ, stOptL2a_driftg, stOptL2a_martingaleg, stOptL2a_gronwallg, stOptL2_of_pinsg, optL2Gen_stOptL2_of_pins_band, Step2IterGen_ListLink, step2IterGen_listLink_band, STthetaOpg_eq_ThetaN, STLMg_eq_STLIMg, STLKMg_eq_STLKIMg, STELKLKMg_eq_STelklkMg, STEGtMg_eq_STegtMg, STEEMg_eq_STeeMg, STgAg_eq_STgANg, STgDriftg_eq_STgDriftNg, stStep2LocalPT_of_L2decayDecG, stLocalAvgOfL2_holdsDecG, step2CloseGen_stLocalAvgOfL2_band, step2CloseGen_step2_of_pinsLW'
$ grep -nE "sorry|admit|native_decide|^axiom|^private axiom" RBM3D/Chain/OptL2Gen.lean RBM3D/Chain/Step2CloseGen.lean | wc -l
0
$ lake build  (RBM3D.lean with the two root imports added temporarily; file restored, `git status` empty)
+import RBM3D.Chain.OptL2Gen
+import RBM3D.Chain.Step2CloseGen
info: RBM3D.lean:558:0: axiom audit: 14253 theorems, 4499 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 61, structural 45, refuted 6, superseded 14).
registry: 2 borrowed + 112 owed + 122 structural + 7 refuted + 18 superseded; 134 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4326 jobs).
$ lake env lean <scratch>/scan.lean       # import RBM3D + both modules + #assert_rbm_axioms
axiom audit: 14253 theorems, 4499 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 61, structural 45, refuted 6, superseded 14).
registry: 2 borrowed + 112 owed + 122 structural + 7 refuted + 18 superseded; 134 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
  first run of this scan, before the registry edit (tool log): `axiom audit: 1 premise(s) that no theorem of this development proves are in none of ...: [RBM.BA.STStep1LoopgL]`
  after the edit the ledger reads: RBM.BA.STStep1LoopgL: 15 [no certificate]; `STOptL2gL` no longer listed
$ git diff main...t/T2478b -- RBM3D/Test/Axioms.lean | grep -E '^[+-] ' | cut -c1-110
-   -- T2478 (BA-T T1a, DECISIONS §279): the premise of the generic Step 2 skeleton (`RBM3D/Chain/Step2IterGen
-   `RBM.BA.STOptL2gL, -- `(eq:opt_L2)` per time over a flow carrier family (`Chain/Step2Gen.lean:621`): hypot
+   -- T2478 (BA-T T1b, DECISIONS §279): the Step 1 loop premise of the generic `(eq:opt_L2)` on the grid (`RB
+   `RBM.BA.STStep1LoopgL, -- `(lRB1)` (`1_2:1321`) uniform in `u ∈ [s,t]` at a law `μ` over a flow carrier: h
$ layout
$ grep -n '^import RBM3D.BA' RBM3D/Chain/OptL2Gen.lean RBM3D/Chain/Step2CloseGen.lean | wc -l
0
$ grep -rn "import RBM3D.Chain.\(OptL2Gen\|Step2CloseGen\|Step2IterGen\)" RBM3D RBM3D.lean
RBM3D/Chain/OptL2Gen.lean:6:import RBM3D.Chain.Step2IterGen
RBM3D/Chain/Step2IterGen2.lean:6:import RBM3D.Chain.Step2IterGen
RBM3D/Chain/Step2CloseGen.lean:6:import RBM3D.Chain.Step2IterGen2
RBM3D/Chain/Step2CloseGen.lean:7:import RBM3D.Chain.OptL2Gen
RBM3D.lean:552:import RBM3D.Chain.Step2IterGen
RBM3D.lean:553:import RBM3D.Chain.Step2IterGen2
  the two lines for the hub to add after the last `import` of RBM3D.lean: import RBM3D.Chain.OptL2Gen ; import RBM3D.Chain.Step2CloseGen
$ cone (transitive `import RBM3D.*`)
  RBM3D.Chain.OptL2Gen: 115 modules, 94195 lines, RBM3D.BA.* modules: 0
  RBM3D.Chain.Step2CloseGen: 152 modules, 135202 lines, RBM3D.BA.* modules: 0
  RBM3D.Path.DifREP2: cone 149 modules, 22 not in the cone of Step2CloseGen, BA modules in cone: []
  RBM3D.Induction.EMn2Exp2: cone 98 modules, 8 not in the cone of Step2CloseGen, BA modules in cone: ['BA.FlowPins', 'BA.MFixedPoint']
$ diff-stat main...t/T2478b
 RBM3D/Chain/OptL2Gen.lean      | 1423 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/Step2CloseGen.lean |  921 ++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    4 +-
 3 files changed, 2346 insertions(+), 2 deletions(-)
$ git diff main...t/T2478b --stat -- <the band files, Chain/* merged, Step2IterGen*> | wc -l
0
merge-base main HEAD: 6039f7ed; HEAD: 3166b5d9
```

### (3) Statements against the pins (script diff by compilation)
`<scratch>/audit.lean` = imports of both modules + the Part 2 defs `T2478_*` of the check file (from `open MeasureTheory` to `/-! ### Shapes`, copied by script) + the block below.
```
example : T2478_OptL2OfPinsg := @stOptL2_of_pinsg                  -- target 8
example : T2478_LocalReaderDec := @stStep2LocalPT_of_L2decayDecG    -- target 9
example : T2478_LocalAvgOfL2Dec := @stLocalAvgOfL2_holdsDecG        -- target 9
example {d} {sz} (Cm : Step2Mat sz) : T2478_ListLink Cm ↔ Step2IterGen_ListLink Cm := Iff.rfl   -- target 10
$ lake env lean <scratch>/audit.lean 2>&1 | grep -c error ; lake env lean docs/tickets/checks/T2478-check.lean; echo $?
0
exit 0
```
Targets 7 and 11 have no binding `T2478_*` text; target 7's three statements are the band statements read through the substitution map `pathP sz, pathH sz, STflowE z, etaT, STgDrift, OptL2aJ ↦ Cm.Pp, Cm.Hpath, Cm, Cm.eta, STgDriftg, OptL2aJg`, and each band statement is re-derived from the generic one (`type_of% @stOptL2a_drift`, `_martingale`, `_gronwall`, `@stOptL2_of_pins`, `@stLocalAvgOfL2_holds`; (4)). Declarations (file:line):
```
T7  OptL2Gen.lean: OptL2aJg 59, optL2Gen_bandStep2_OptL2aJ 64, stOptL2a_driftg 589, stOptL2a_martingaleg 678, stOptL2a_gronwallg 859
T8  OptL2Gen.lean: stOptL2_of_pinsg 1109, optL2Gen_stOptL2_of_pins_band 1366
T9  Step2CloseGen.lean: stStep2LocalPT_of_L2decayDecG 584, stLocalAvgOfL2_holdsDecG 781, step2CloseGen_stLocalAvgOfL2_band 810
T10 Step2CloseGen.lean: Step2IterGen_ListLink 65, step2IterGen_listLink_band 73, STthetaOpg_eq_ThetaN 82, STLMg_eq_STLIMg 90, STLKMg_eq_STLKIMg 95, STELKLKMg_eq_STelklkMg 102, STEGtMg_eq_STegtMg 125, STEEMg_eq_STeeMg 137, STgAg_eq_STgANg 147, STgDriftg_eq_STgDriftNg 152
T11 Step2CloseGen.lean: step2CloseGen_step2_of_pinsLW' 836
```

### (4) Compiled nonempty instances, band re-derivations, hypothesis and bridge tables
Data `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`), `z0`, `flow_z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, window `[0, 1/16]`, `𝔠_d = 1/26`; identities at `n = 100`, `u = 1/32`. `grep -c '^example'`: OptL2Gen 8, Step2CloseGen 7.
| target | example (file:line) | discharged at the data | left as hypothesis |
|---|---|---|---|
| 7 drift, martingale, Grönwall | OptL2Gen 1277, 1297, 1309 (`τ = D = 1`, `K ≥ N`) | F1-F2, F3, F9, Hermitian walk, `STBdatagL`, target 1 (`step2IterGen_newKLK_band`), `STEMn2PolygL` (`stEMn2Poly_holds`), `(con_st_ind)` (`conStInd_inst`), time ranges | `STLWBgL`, `STGridMartgL`; Step 1 and `STLKgL` (stochastic) |
| 8 `stOptL2_of_pinsg` | OptL2Gen 1340 (`∃ 𝔠₀`, every `0 < 𝔠_d ≤ 𝔠₀`) | as above | `STLWBgL`, `STGridMartgL`; `STLKgL`, Step 1 |
| 7, 8 band re-derivations | OptL2Gen 1366 (named `optL2Gen_stOptL2_of_pins_band`), 1374, 1381, 1394, 1409 | all band producers | `STLWB`, `STGridMart` (band pins) |
| 9 reader, closing pin | Step2CloseGen 853, 865 | `flowOK`, size data (`localAvg1_inst_hdat`, `localAvg1_data`), `(GiiGEX)`, `(GavLGEX)` (`stGbEXP_holds`), `STGijDecgL` (`bandFM_STGijDecgL_of_three_le`) | weak law, `(eq:L2_decay)` (stochastic) |
| 9 band re-derivation | Step2CloseGen 810 (`step2CloseGen_stLocalAvgOfL2_band`), 824 (`type_of% @stLocalAvgOfL2_holds`) | all | none |
| 10 | Step2CloseGen 884, 886, 900 (class, six identities at `(n, u) = (100, 1/32)`, drift and observable) | all (`step2IterGen_listLink_band`) | none |
| 11 | Step2CloseGen 910 (through `inst_step2`) | all producers of the file's cone | `LWterm 3`, `LWtermExp 3`, `STEMn2Exp 3`, `STGridMart 3`; `STLK`, `STDecay`, Step 1 |

Hypothesis and bridge table as used (generic premise → band discharge → BA source, shapes only):
| band fact (file:line) | generic premise (this branch) | band discharge | BA source |
|---|---|---|---|
| `STFlow` admissible, `T < lemT < 1` (`OptL2a:283-305`) | `Step2EventsGen_Flow` (F1-F2) | `Step2EventsGen_bandFlow` | `baStep2Data.flowOK_adm/_T` |
| `ST_Bdata_holds` (`OptL2a:693`) | `STBdatagL` (`c ≤ 1` by `min c 1`: `OptL2Gen_sizedata`) | `bandFM_STBdata`, `ST_Bdata_holds` | T1-BA |
| `stNewKLK_holds` at `ℓ = 0` (`OptL2a:98-146`) | `Step2IterGen_NewKLK` (target 1) | `step2IterGen_newKLK_band` | T1-BA (T2478-prove.md rows 13-17) |
| `pathH_isHermitian`; `ST_grid_whp_of_sections`, `ST_grid_whp_zero` (`OptL2a:487, 519, 1299`); `ST_model_le_path` (`OptL2b:302`) | hHerm; `Step2EventsGen_Grid` (F9) | `pathH_isHermitian`; `Step2EventsGen_bandGrid` | `baStep2Mat_Hpath`; `Step2EventsGenTw_baGrid` |
| `ST_mE_im_ge`, `q = (√κ/2)⁻¹` (`OptL2a:1143, 1203, 1331, 1394`) | `DecayGen_Spec` (F3), `q = κm⁻¹`, `η = (1-t) Im m` | `DecayGen_bandSpec` | `EMn2BA_mF_data` |
| `STLWB` (`OptL2a:404`), `stEMn2Poly_holds` (`:449`), `STGridMart` (`:1078`) | `STLWBgL`, `STEMn2PolygL`, `STGridMartgL` | `bandFM_STLWB` of `STLWB_of_LWterm`; `bandFM_STEMn2Poly`; `bandStep2_STGridMart` | `BASTLWB`; `baSTEMn2Poly`; `baGridMart_holds` |
| `STGijGEX` window of `stStep2LocalPT_of_L2decayG` (`LocalAvg2:367`) | `STGijDecgL` (`CltGen:94`) with `Φ = N^{τ'/8}√STWB`, `Ψ = W^{-d/2}`, `D = (d + (d-2)/𝔠 + 1)/2` | `bandFM_STGijDecgL_of_three_le` (`FarEntry:1724`) | U4-BA from `baGbEXPij'_holds`; `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds` |
| `STLM_eq_STLIM` and `KLK`-definitional `KI` (`Step2Iterate:1594`) | `Step2IterGen_ListLink` | `step2IterGen_listLink_band` | `loopM_eq_loopL`, `baStep2Mat_KI` |
`open private` list: `la2_zdistInf_add_le`, `la2_zdistInf_neg`, `la2_zdistInf_zero` from `RBM3D.Induction.LocalAvg2` (`Step2CloseGen.lean:49`); `OptL2Gen.lean`: none.

### (5) Site-1 table and the J decision
Not part of T1b: site 1 is `ST_selfImprove_sectiong` (T1a, `T2478-prove.md` (b) (5)). Targets 7-8 use `STEMn2PolygL` (the first estimate), not the Ĵ-form `STEMn2ExpgL`; `OptL2aJg` is the maximum `max_{σ,a} |(𝓛-𝒦)^{(2)}|` of the carrier matrix, defined on `Cm` (band bridge `optL2Gen_bandStep2_OptL2aJ`, `rfl`). No step needs a deterministic `J` beyond it.

### (6) Tripwire (C6/I1: fire if `g > 0.5` or `f_sem > 0.30`)
```
$ python3 -I gfsem.py     # the 1a script, band files unchanged
g = 442/2269 = 0.195; f_sem = 8/3161 = 0.003
$ proxy g of the 1a token set on the generic regions of the new files; grep for the star-tree / K closed-form tokens
tripwire proxy g (1a token set) on the generic region of OptL2Gen.lean: 77/1103 = 0.070  (fire above 0.50)
tripwire proxy g (1a token set) on the generic region of Step2CloseGen.lean: 30/676 = 0.044  (fire above 0.50)
$ grep -c -E 'KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|couplingLen|KLtree|treeEq|KLK_two|KLmaxDist|STKloop_two' OptL2Gen.lean Step2CloseGen.lean
OptL2Gen.lean:0   Step2CloseGen.lean:0
```
Not fired. No step of the port used a star-tree or `K` closed form.

### (7) Target 9 (GMN-C1): outcome
Delivered: `stStep2LocalPT_of_L2decayDecG` (`Step2CloseGen.lean:584`, pin `T2478_LocalReaderDec`) and `stLocalAvgOfL2_holdsDecG` (`:781`, pin `T2478_LocalAvgOfL2Dec`), both compiled against the pins in (3); block `Step2CloseGen.lean:166-804` = 639 lines ((a) row 16: central 525, range 400/740). Route as in (a) row 18: `Ω` from `localAvg1_whp_omegaG`; loop premise of `STGijDecgL` from `localAvg1_whp_L2G` at `τ'/4`, the charge `(+,-)` through `Cm.L_swap`; `STGijDecgL` at `Φ_n(a,b) = N^{τ'/8}√(W^{-d}B_{u,|a-b|})`, `Ψ_n = W^{-d/2}`, `D = (d + (d-2)/𝔠 + 1)/2`, with `τ' = min(τ, c)`; `R ≤ C₂ N^{τ'/8}√(W^{-d}B_{u,r})` (`Step2CloseGen_R_le`, `C₂ = Step2CloseGen_C2`, `C₂² ≤ N^{τ'/4}` eventually); diagonal from `STGiiGEXgL` and `localAvg1_maxLoop2_leG`. Band recovered: `step2CloseGen_stLocalAvgOfL2_band` (`type_of% @stLocalAvgOfL2_holds`). No fallback to T1-BA.

### (8) Greps (X1-C1, U-C4, TN-C4, UBA-C1)
```
X1-C1: grep -nE "<the ticket pattern>" RBM3D/Chain/OptL2Gen.lean RBM3D/Chain/Step2CloseGen.lean, hits by region
OptL2Gen.lean: docstring before section 1: 1 hit (prose)
  ## 1. The maximum `J` and the drift bound at one grid state (`OptL lines 52-137: 0 hits {}
  ## 2. The premises of the pins at a time section and the events on lines 138-422: 0 hits {}
  ## 3. The pathwise Grönwall inequality on one sample (`OptL2a:746- lines 423-579: 0 hits {}
  ## 4. Target 7: the three statements on the grid (`OptL2a:975-1419 lines 580-1036: 2 hits {'class name Step2IterGen_NewKLK d (pattern KLK d)': 2}
  ## 5. Target 8: the pin `STOptL2gL` from `STLWBgL`, `STEMn2PolygL` lines 1037-1246: 1 hits {'class name Step2IterGen_NewKLK d (pattern KLK d)': 1}
  ## 6. Band re-derivations and compiled nonempty instances (targets lines 1247-1424: 60 hits {'band bridge / discharge / instance': 60}
Step2CloseGen.lean: docstring before section 1: 1 hit (prose)
  ## 1. Target 10: section 12.2 over the carrier (`Step2Iterate:1586 lines 60-165: 17 hits {'KLloopOf (pattern Lloop)': 17}
  ## 2. Target 9 (GMN-C1): the local bound from `STGijDecgL` (`Local lines 166-804: 0 hits {}
  ## 3. Target 11: the band corollary, the band re-derivation of tar lines 805-840: 2 hits {'band bridge / discharge / instance': 2}
  ### Compiled nonempty instances (targets 9-11; CLAUDE.md §4 step 2 lines 841-922: 28 hits {'band bridge / discharge / instance': 28}
$ grep -nE "\.lam" RBM3D/Chain/OptL2Gen.lean RBM3D/Chain/Step2CloseGen.lean     # sz.lam only inside Bparam / STWB arguments
Step2CloseGen.lean:260, 281  (`sz.lam n ^ 2 + |1 - u|`, the shift lemma); OptL2Gen.lean: no hit
$ U-C4: grep -nE "^(noncomputable )?(private )?def" both files   # no matrix- or tensor-valued kernel
OptL2Gen.lean:59 OptL2aJg (ℝ-valued);  Step2CloseGen.lean:65 Step2IterGen_ListLink (Prop); 370, 373, 376, 379 private ℝ constants Step2CloseGen_K1/K2/S/C2
$ TN-C4: grep -nE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" both files | wc -l     -> 0
$ UBA-C1: grep -nE "gK|BAflowLam0|withLam|lam0" both files | wc -l                           -> 0
$ name clash: git grep -l -w -E "<the 21 new public names>" <ref> -- RBM3D RBM3D.lean   (main and every local branch t/* except t/T2478b)
refs scanned: 489, refs with a Lean file hit outside Test/Axioms.lean: 0
```

### Narrative (facts of the files and the tool log)
1. Targets 7-8 are the text of `OptL2a:51-1419`, `OptL2b:101-316` over `Cm : Step2Mat sz`; the model-free and size-level helpers (`OptL2alam`, `OptL2aPsi`, `OptL2a_lam_*`, `_floor`, `_rho_le`, `_w_pow`, `_mart_arith`, `_alpha_arith`, `_q_log_le`, `_x_le`, `_prob_combine`, `_grid`, `_cards`, `OptL2b_arith`, `OptL2b_con_restrict`) are used by name.
2. The band facts `STFlow`, `ST_Bdata_holds`, `pathH_isHermitian`, `ST_mE_im_ge` are replaced by the hypotheses F1-F3, F9, the inline Hermitian walk, `STBdatagL`, and `q = κm⁻¹`; the three statements of target 7 and `stOptL2_of_pins` are re-derived from the generic ones (OptL2Gen 1366-1409).
3. `stOptL2_of_pinsg` compiles against `T2478_OptL2OfPinsg` (hypotheses in the pin's order: F1-F2, F9, F3, Hermitian walk, `STBdatagL`, `STLWBgL`, `STEMn2PolygL`, target 1, `STGridMartgL`).
4. Target 9 is a new proof (not a port): the lattice sum is `Σ_a e^{-γ|a-c|_∞} ≤ (2/(1-e^{-γ/d}))^d` by the bound `max ≥ (1/d) Σ` and `Fintype.prod_sum`; the shift lemma is the proof of `localAvg1_STWB_comp` with `3` replaced by `j+1`; the profile sum and the floor use only `Bparam` and `Admissible` (`Bandwidth`).
5. Target 10 is the band text with `hL : Step2IterGen_ListLink Cm` rewriting `LM`, `K` at `KLloopOf` (band lemmas `KLloopOf_cut*`, `STeeLoop_one/two` used by name); `STthetaOpg_eq_ThetaN` is `rfl` and carries no `hL`.
6. Target 11 is `step2IterGen_step2_of_pins_band` (T1a) with `STOptL2`, `STLocalAvgOfL2` produced by targets 8, 9; four hypotheses remain ((a′) 3).
7. Registry: the scan reported `STStep1LoopgL` as an unregistered premise (top-level binder of `stOptL2a_martingaleg` only); registered as owed next to `STStep1WeakgL`. The line `STOptL2gL` is removed (concluded by `stOptL2_of_pinsg`).
8. No `set_option maxHeartbeats`, no `sorry`; 21 public declarations, all private helpers carry the stem `Step2CloseGen_` / `OptL2Gen_`.
9. `RBM3D.lean` is not edited (root imports are the hub's step, CLAUDE.md §3 (A)4); the full `lake build` above was run with the two lines added temporarily.

## (c) Verified names (by compilation in this branch)
- Mathlib: `Real.pow_div_factorial_le_exp` (`Analysis/Complex/Exponential.lean:257`), `Fintype.prod_sum` (`Algebra/BigOperators/Ring/Finset.lean:301`), `Finset.prod_le_prod₀`, `geom_sum_mul_neg`, `Finset.sum_range_reflect`, `Real.exp_lt_one_iff`, `Real.exp_nat_mul`, `Equiv.sum_comp`, `Equiv.subRight_apply`, `ZMod.val_injective`, `ZMod.val_natCast_of_lt`, `Real.sqrt_le_iff`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_mul`, `Real.sqrt_eq_rpow`, `Real.exp_le_one_iff`, `Finset.sum_mul_sum`, `Nat.le_self_pow`, `Real.rpow_le_rpow_of_exponent_ge`.
- Verified absent / wrong form: `Real.exp_lt_one` (unknown constant; use `Real.exp_lt_one_iff`); `Finset.prod_le_prod` is the ordered-monoid version, the nonnegative real version is `Finset.prod_le_prod₀`.
- RBM names used beyond the ticket's list: `localAvg1_stochDomAt_of_whp`, `localAvg1_perTime_of_stoch`, `localAvg1_whp_L2G`, `localAvg1_whp_omegaG`, `localAvg1_maxLoop2_leG`, `localAvg1_det`, `localAvg1_STWB_ge`, `localAvg1_STWB_le`, `ST_W_tendsto`, `ST_rpow_neg_half`, `Green.perTime_timeIcc_of_forall_seq`, `StochDomAt.highProb`, `Gauss.HighProbAt.inter`, `eventually_le_rpow`, `Step2EventsGen_grid_whp_of_sections`, `_grid_whp_zero`, `_model_le_path`, `_PT_of_sections`, `_prec_sup`, `_prec_mono_eventually`, `optL2Gen_stOptL2_of_pins_band`.

## (d) Open issues and paper-delta candidates
- **T2478d** (candidate; tags continue T1a's T2478a-c): target 9 proves the local bound `|(G-M)_{xy}|² ≺ W^{-d}B_{u,|[x]-[y]|}` from `STGijDecgL` with the explicit shift lemma `B_{u,K'} ≤ (j+1)^{d-2}B_{u,K}` (`K ≤ K'+j`) and the lattice sum, instead of the regularity `(eq:Psirelations)` (`7_8:2033-2050`) and the `(log W)^{3/2}` truncation; `c' > 0` of `STGijDecgL` is arbitrary.
- **T2478e** (candidate): the band corollary `step2CloseGen_step2_of_pinsLW'` takes `LWterm d`, `LWtermExp d`, `STEMn2Exp d`, `STGridMart d` ((a′) 3); statement-level, not a paper difference. Dispatcher decision: accept as delivered, or amend the row to import `Path/DifREP2` (22 further modules incl. the `*N` block) so that `STGridMart d` is discharged by `stGridMart_holds`; `STEMn2Exp d` cannot be discharged inside the BA-free layering.
- For the hub at merge: add the two root imports of (2); the registry change is in the branch (`STStep1LoopgL` added, `STOptL2gL` removed).
- For T1-BA: (i) `Step2IterGen_ListLink` at `baStep2Mat` needs `loopM_eq_loopL` and `baStep2Mat_KI`; the `StepDecompGen_LoopForm` bridge covers only the `LM` conjunct ((a′) 4); (ii) target 9 at BA takes `STGijDecgL` at `baFMz` (U4-BA from `baGbEXPij'_holds`), `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds` and the size data `STBdatagL` at BA; (iii) `STStep1LoopgL` at BA is the BA chain's Step 1.
