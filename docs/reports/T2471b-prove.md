Prover model: claude-sonnet-5-5
# T2471b = P1b-2 of ticket T2471: stage 1b (`prover-hard`), targets 4-7, BA leaf `RBM3D/BA/GridRepTailBA.lean`
Branch `t/T2471b` (stacked on `t/T2471` d6f59884, `git merge main` = commit 8b867f9c; `51e233bd`, P1b-1, is an ancestor of HEAD). HEAD `817c5c2f`. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2471b`. Scratch: scratchpad `T2471b/`.

## (a) Math preflight
The row's stage 1a is `docs/reports/T2471-prove.md` (a), (a′), (a″) and `docs/reports/T2471-1a-audit.md` (PASS, split confirmed, condition (7) not met, so `prover-hard`); not repeated. No separate `T2471b` section (a) existed when this stage started (`wc -l docs/reports/T2471b-prove.md` at 21:14:21 UTC: `No such file`).
## (a′) Preflight corrections: Mon Oct 12 22:06:42 UTC 2026 (verdict of (a) stays PASS; no change to a statement or a verdict)
* (a) (x) lists `open private` from `LoopC2N` (116, 365, 376, 424) and the BA leaf's own jets. Not used: `Φ_b(M) = 𝓛_{u,σ,b}(g₀Ψ + M)` is TL's twisted observable `L̃_{σ,(b₀;b₁,b₁)}` (`GridMartBA_twL2M_diag`), so TL's `TwistGridWTail_hermTestFun`, `_Phi_second` (`6 η⁻⁴`), `_fderiv_eq`, `_Phi_measurable`, `_Y_fields`, `_condMGF_generic` apply at `ι = Fin 2 → Zd` as they are. Actual `open private` (file head, l.40-45): `GridMartBA_{Q1,Q2,Phi,Phi_add_le,chain,twDerM_eq,Q1_conjTranspose,Q2_conjTranspose,Hpath_herm,twL2M_diag}`, `TwistKer_{fE,trace_sandwich,loopFine_eq}`, `TwistGridWTail_{card_blk,norm_sum_sum_le,tri,wd_sq,norm_sum_wS_mul_le,linTrVar_le,chg_eq_Gres,linTr_neg_I_smul,sum4_swap}` (1a-audit O3 predicted the `GridMartBA` reuse).
* The ticket's 6 (a) "clause 1 by telescoping, using target 5" is superseded by UN-C5 (CONTROL H256 (3), as (a) l.77 says): clause 1 is the ring identity of the residual at every `n`; target 5 enters clauses 2-3 (`gridRepTailBA_rem_eq`, (5c)).
* (a) D3 central for P1b-2: 1,430 lines; delivered 1,396.

## (b) Script output
```
$ date -u; touch RBM3D/BA/GridRepTailBA.lean; lake build RBM3D.BA.GridRepTailBA     (21:53:24 UTC)
exit=0   last line: Build completed successfully (4054 jobs).   lines with `error` or `sorry`: 0
$ git log: wc -l of RBM3D/BA/GridRepTailBA.lean at each commit (stop line 2,000; reserve file only above 1,800; (a) central 1,430)
31cff9eb  509  sections 1-3 (BA kernel and window, Q-layer, cross-label STeeMg)
2d35cf39  926  section 4 (Z/Y increments, cross-label QV, BA discharge of Inc)
550930aa 1073  sections 5-6 (Hyp and clause 4 at BA, list identities)
4a58496d 1248  section 7 (assembly baGridRepNAt2_of_bridge, baGridRepNAt2_holds)
24794897 1392  section 8 (instances at d = 3)
f3ea2230 1391  lint cleanups        7e462fd7 1397  instance of target 6 (a)        817c5c2f 1396  unused open private names dropped
$ import RBM3D; import RBM3D.BA.GridRepTailBA; #assert_rbm_axioms     (lake env lean, 21:53:34 UTC; Test/Axioms.lean untouched)
exit=0   first line: axiom audit: 13806 theorems, 4387 definitions, 0 axioms in `RBM` ...   "no theorem of this development" (premise error): 0 lines; `GridRepTail` in the output: 0 lines
$ python3 axsum.py (#print axioms of the 83 public theorem/def/abbrev of the file, incl. the Inst namespace)
declarations printed: 83; with exactly [propext, Classical.choice, Quot.sound]: 81; subset of the three: gridRepTailBA_STeeLoop_one, gridRepTailBA_STeeLoop_two ([propext, Quot.sound])
'RBM.BA.gridRepTailGen_ker_BA': [propext, Classical.choice, Quot.sound]       'RBM.BA.gridRepTailGen_window_BA': [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_inc_BA': [propext, Classical.choice, Quot.sound]       'RBM.BA.gridRepTailGen_hyp_BA': [propext, Classical.choice, Quot.sound]
'RBM.BA.baGridWTail2_holds': [propext, Classical.choice, Quot.sound]          'RBM.BA.baStep2_STgAg_eq': [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_STgDriftg_eq': [propext, Classical.choice, Quot.sound]        'RBM.BA.baStep2_STEEMg_eq': [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_filt_withLam': [propext, Classical.choice, Quot.sound]        'RBM.BA.baGridRepNAt2_of_bridge': [propext, Classical.choice, Quot.sound]
'RBM.BA.baGridRepNAt2_holds': [propext, Classical.choice, Quot.sound]         'RBM.BA.GridRepTailBAInst.inst_baGridWTail2': [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailBAInst.inst_baGridRepNAt2': [propext, Classical.choice, Quot.sound]
```
### Target statements (script `extract.py`, signature lines of the file; `baGridRepNAt2_of_bridge` is in the diff block below)
```
GRTBA:60: theorem gridRepTailGen_ker_BA {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) {κ : ℝ} (hκ : 0 < κ)
GRTBA:61:     (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) :
GRTBA:62:     GridRepTailGen_Ker (baStep2Mat sz lam0 E).toFlowFM n := by
GRTBA:110:     GridRepTailGen_Window (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) t n := by      (hyps: hκ, hz : BAFlow, htT : t n ≤ BAflowT0, hN0, hεn : 1/(8κ) ≤ N^ε; l.107-109)
GRTBA:886: theorem gridRepTailGen_inc_BA (hm : ‖BAmF sz lam0 E n‖ ≤ 1) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
GRTBA:887:     (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u) :
GRTBA:888:     GridRepTailGen_Inc (baStep2Mat sz lam0 E) s t K n := by
GRTBA:927: theorem gridRepTailGen_hyp_BA (d : ℕ) :
GRTBA:928:     GridRepTailGen_Hyp d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
GRTBA:944: theorem baGridWTail2_holds (d : ℕ) :                                                    [target 4]
GRTBA:945:     STGridWTail2gL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 :=
GRTBA:1049: theorem baStep2_STgAg_eq {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)       [target 5]
GRTBA:1050:     (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
GRTBA:1051:     STgAg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgANg (baStep2Mat sz lam0 E) s t K n σ a k ω :=
GRTBA:1057:     STgDriftg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgDriftNg (baStep2Mat sz lam0 E) s t K n σ a k ω :=      (binders as 1049-1050)
GRTBA:1061: theorem baStep2_STEEMg_eq {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
GRTBA:1062:     (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
GRTBA:1063:     STEEMg (baStep2Mat sz lam0 E) n u H σ a = STeeMg (baStep2Mat sz lam0 E) n u H σ a a :=
GRTBA:1067: theorem baStep2_filt_withLam {d : ℕ} (sz : Sizes d) (j : ℕ) : filt (sz.withLam 0) j = filt sz j := rfl
GRTBA:1148: theorem baGridRepNAt2_of_bridge (d : ℕ)  (hB : <T2471_Bridge body, l.1150-1163>) :          [target 6 (a)]
GRTBA:1237: theorem baGridRepNAt2_holds (d : ℕ) :                                                  [target 6 (b)]
GRTBA:1238:     ∃ C₀ : ℝ, 0 ≤ C₀ ∧
GRTBA:1239:       STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 :=
```
### Statement diff against `docs/tickets/checks/T2471-check.lean` (script `stmtcheck.py`, whitespace-normalised bodies; numbers = characters)
```
6(a) hypothesis == T2471_Bridge body : True 600 600
6(a) conclusion == T2471_GridRepN2 body: True 93 93
6(b) statement == T2471_GridRepN2 body : True
4 statement == check shape (STGridWTail2gL for T2471_WTail2): True
5 baStep2_STgAg_eq == check shape: True
5 baStep2_STgDriftg_eq == check shape: True
5 baStep2_STEEMg_eq == check shape: True
```
```
$ lake env lean audit_like.lean   (scratch: the check's T2471_GridRepN2, T2471_Bridge, T2471_WTail2 copied verbatim; examples below)
example : ∀ d : ℕ, T2471_GridRepN2 d := baGridRepNAt2_holds                          example : ∀ d : ℕ, T2471_Bridge d → T2471_GridRepN2 d := baGridRepNAt2_of_bridge
example : ∀ d : ℕ, T2471_WTail2 d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := baGridWTail2_holds
example : ∀ d : ℕ, T2471_Bridge d := baGridBridge_holds                              exit=0 (only unused-variable warnings of the check's own defs)
```
`STGridWTail2gL` (merged P1b-1, `Chain/GridRepTailGen.lean` l.133) equals `T2471_WTail2` (P1b-1 report, `stmtcheck.py`: True 925 925). `BAGridBridge d` (`GridMartBA.lean`) is the inline hypothesis (the probe's `rfl`), so `baGridRepNAt2_holds d := baGridRepNAt2_of_bridge d (baGridBridge_holds d)` compiles. The auditor's `example : ∀ d : ℕ, T2471_GridRepN2 d := baGridRepNAt2_holds` has the same type.
### Compiled nonempty instances (same file, namespace `RBM.BA.GridRepTailBAInst`, `d = 3`)
Data: `sz0` (`N_0 = 2097152`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`, `s ≡ 1/10 < t ≡ 1/2 ≤ BAflowT0 sz0 zSeq n` (`half_lt_t0`), `D = 1`, `ε' = 1/10`, `K_n = ⌈N_n^{CK}⌉ + 1`. Every deterministic hypothesis is discharged; nothing is assumed.
```
$ grep -nE "^(example|theorem inst_)" RBM3D/BA/GridRepTailBA.lean   (line: item)
1283 Ker, 1287 Window, 1292 Inc, 1300 Hyp (examples); 1305 inst_baGridWTail2; 1328, 1332, 1337 target 5 (5a), (5b), (5c); 1342 filt;
1346 inst_baGridRepNAt2; 1385 baGridRepNAt2_of_bridge 3 (baGridBridge_holds 3); 1390 baGridRepNAt2_holds 3
$ statements extracted by line range (script prints the file lines)
GRTBA:1283: example : ∀ n, GridRepTailGen_Ker CmI.toFlowFM n := fun n =>
GRTBA:1284:   gridRepTailGen_ker_BA sz0 _ _ n (by norm_num : (0 : ℝ) < 1 / 2) (BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n)
GRTBA:1287: example (n : ℕ) : GridRepTailGen_Window CmI tI n :=
GRTBA:1288:   gridRepTailGen_window_BA (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 tI n (htI n) (by linarith [hN1I n]) (hεnI n)
GRTBA:1292: example (K : ℕ → ℕ) (n : ℕ) : GridRepTailGen_Inc CmI sI tI K n :=
GRTBA:1300: example : GridRepTailGen_Hyp 3 BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 :=
GRTBA:1305: theorem inst_baGridWTail2 :
GRTBA:1306:     ∃ CK : ℝ, 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
GRTBA:1307:       (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
GRTBA:1308:       (∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)),
GRTBA:1309:         CmI.Pp {ω | ∃ k, k ≤ K n ∧
GRTBA:1310:           ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
GRTBA:1311:               (∑ j ∈ Finset.range k, gridStep sI tI K n *
GRTBA:1312:                 ‖STeeUMg CmI n (gridTime sI tI K n j) (gridTime sI tI K n k) (CmI.Hpath sI tI K n j ω) i.1 i.2‖ +
GRTBA:1313:                 ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
GRTBA:1314:             ‖∑ j ∈ Finset.range k,
GRTBA:1315:               Step2Gen_UN CmI.toFlowFM n i.1 (gridTime sI tI K n j) (gridTime sI tI K n k)
GRTBA:1316:                 (fun b => (∑ j' ∈ Finset.range (j + 1), martIncNg CmI sI tI K n j' i.1 ω b) -
GRTBA:1317:                   ∑ j' ∈ Finset.range j, martIncNg CmI sI tI K n j' i.1 ω b) i.2‖} ≤
GRTBA:1318:           ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)))) := by
GRTBA:1346: theorem inst_baGridRepNAt2 :
GRTBA:1347:     ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ CK : ℝ, 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
GRTBA:1348:       (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
GRTBA:1349:       ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))) → ℕ → PathΩ sz0 → ℂ,
GRTBA:1350:         (∀ (n : ℕ) (i : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))), ∀ᵐ ω ∂CmI.Pp, ∀ k, k ≤ K n →
GRTBA:1351:           STgANg CmI sI tI K n i.1 i.2 k ω = STgANg CmI sI tI K n i.1 i.2 0 ω +
GRTBA:1352:             ((gridStep sI tI K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftNg CmI sI tI K n i.1 i.2 j ω +
GRTBA:1353:             Rem n i k ω + Mart n i k ω) ∧
GRTBA:1354:         (∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)), ∀ᵐ ω ∂CmI.Pp, ∀ k, k ≤ K n →
GRTBA:1355:           ‖Rem n i k ω‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep sI tI K n)) ∧
GRTBA:1356:         (∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)),
GRTBA:1357:           CmI.Pp {ω | ∃ k, k ≤ K n ∧
GRTBA:1358:             ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
GRTBA:1359:                 (∑ j ∈ Finset.range k, gridStep sI tI K n *
GRTBA:1360:                   ‖STeeMg CmI n (gridTime sI tI K n j) (CmI.Hpath sI tI K n j ω) i.1 i.2 i.2‖ +
GRTBA:1361:                   ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖} ≤
GRTBA:1362:             ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)))) ∧
GRTBA:1363:         (∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)),
GRTBA:1364:           CmI.Pp {ω | ∃ k, k ≤ K n ∧
GRTBA:1365:             ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
GRTBA:1366:                 (∑ j ∈ Finset.range k, gridStep sI tI K n *
GRTBA:1367:                   ‖STeeUMg CmI n (gridTime sI tI K n j) (gridTime sI tI K n k) (CmI.Hpath sI tI K n j ω) i.1 i.2‖ +
GRTBA:1368:                   ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) <
GRTBA:1369:               ‖∑ j ∈ Finset.range k,
GRTBA:1370:                 Step2Gen_UN CmI.toFlowFM n i.1 (gridTime sI tI K n j) (gridTime sI tI K n k)
GRTBA:1371:                   (fun b => Mart n (i.1, b) (j + 1) ω - Mart n (i.1, b) j ω) i.2‖} ≤
GRTBA:1372:             ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)))) := by
```
### Name clash (script `clash.sh`: `git grep -E <the 73 distinct public names outside the Inst namespace | GridRepTailBAInst | GridRepTailBA\b>` in `RBM3D`, `RBM3D.lean`; 21:55 UTC)
```
main a931034a: files with a hit: 0
t/* branches scanned (all but t/T2471b): 474; branches with a hit: 1 t/T2471(1)
$ git grep -noE <pattern> t/T2471 -- RBM3D RBM3D.lean   ->  RBM3D/Probe/T2471Pins.lean:125, 126: baGridWTail2_holds ; :366: baGridRepNAt2_of_bridge
```
Those three hits are the substrings of the probe's `T2471_baGridWTail2_holds_stmt`, `T2471_baGridRepNAt2_of_bridge_stmt` (never merged), not clashes. No T2474 name (`loopFamNg ... HierDriftGen_*`) occurs in the file (grep: 0).
### Greps of ticket target 8 on the BA leaf
```
$ grep -c "sz\.lam" RBM3D/BA/GridRepTailBA.lean                                  0     (UBA-C1: no size-level lam; no crossing, not triggered)
$ grep -cE withLam / BAflowLam0 / lam0:   36 / 32 / 234     `sz.withLam 0` = the coupling-0 path model (as baStep2Mat, TL); `BAflowLam0` only in BA flow statements and instances (l.94-114, 928-945, 1153-1239, 1280-1391)
$ grep -nE '\|E\||zt E|etaT|mSigma|STflowE|lemT|STFlow|mE\b|2 - κ' (X1-C1)    hits: 0
$ grep -nE 'Ring\.inverse|Matrix\.of|cycProd|Ugen' (U-C4)                        hits: 0   (no kernel defined)
$ grep -nE 'STGridRepNgL|∀ m|\{m |\(m :' (TN-C4)                                 hits: 0
$ grep -nE 'sorry|admit|native_decide|^axiom'                                    hits: 0
$ grep -nE '^import' : Chain.GridRepTailGen2, BA.{GridMartBA, TwistKer, TwistGridWTail, TwistGridWTail2, TwistGridTail2, TwistGridRem2, GreenSchur, EMn2BA}
$ grep -rln GridRepTailBA RBM3D RBM3D.lean   ->  RBM3D/BA/GridRepTailBA.lean    (no importer)
$ git diff --stat main...t/T2471b      RBM3D/BA/GridRepTailBA.lean | 1396 +   ;   RBM3D/Probe/T2471Pins.lean | 400 +   (inherited from t/T2471, never merged)
$ same diff restricted to Path, Induction, BA/Twist*, BA/Step2BA, BA/GridMartBA, Chain, Test, RBM3D.lean:     (empty)
```
### Hypothesis table (class field -> BA discharge, all compiled)
| field | BA discharge (file line) | sources |
|---|---|---|
| `Ker` K1-K4 | `gridRepTailGen_ker_BA` l.60 | `BAuKerSemigroup_holds` via `Step2Kern_uKer_BA`; `TwistGridWTail_sum_norm_twU_le`, `_norm_twU_sub_one_le`, `_twU_conj` via `twU_eq_uKer` (probe l.166, ported) |
| `Window` | `gridRepTailGen_window_BA` l.107, `gridRepTailBA_eta` l.91 | `EMn2BA_one_sub_T0`, `EMn2BA_mF_data`, `TwistGridWTail2_inv_eta`; only `N^ε ≥ 1/(8κ)`, eventually |
| `Inc` Q0 | `gridRepTailGen_inc_BA` l.886 | `isProbabilityMeasure_pathP`, `pathH_measurable_filt`, `GridMartBA_Hpath_herm`, `gridRepTailBA_measurable_STeeMg` l.698 |
| `Zfields` | `gridRepTailBA_zfields` l.799 | `TwistGridWTail_condMGF_generic` at `ι = Fin 2 → Zd`, `gridRepTailBA_linTrVar_le_QV` l.521 (factor 2), `gridRepTailBA_STeeMg_norm_le` l.424, `gridRepTailBA_stepZCN_sum` l.622 |
| `Yfields` | `gridRepTailBA_yfields` l.851 | `TwistGridWTail_Y_fields` with `C₂ = 6 η⁻⁴`, `gridRepTailBA_xi_ae` l.709, `gridRepTailBA_Yconst_le` l.781 (`768 ≤ 2000 N²`) |
| Q1, Q2 | `gridRepTailBA_STeeMg_norm_le`, `_sub_le` l.424, 440 | `Q_k` entries `≤ η⁻³` (l.197, 206), shift `3 η⁻⁴ |Δz|` (l.215, 237), `Φ₂` l.260-273; `|z_{u'} - z_u| = (u'-u)|m| ≤ u'-u` (`BAm_norm_le_one`); constants `2N(16N)^6`, `12·16^7 N^8 (u'-u)` exactly |
| `Hyp` | `gridRepTailGen_hyp_BA` l.927 | `hz.1.2.2.1 : SizeTendsto`, `tendsto_rpow_atTop`, `BAflow_real` |
### T2460 status at target 6
Merged (`ad52b370`, `docs/queue/T2460.state` 19:33:28 per T2471-prove.md (a)); `baGridBridge_holds` (`BA/GridMartBA.lean:538`) is used by target 6 (b) and by the instances; `BAGridBridge d` is defeq to the inline hypothesis of 6 (a). 6 (b) is in this row.
### Narrative
* Delivered: P1b-2 = targets 4-7 in one file, 1,396 lines (below the 1,800 reserve rule: `GridRepTailBA2` not created). No hypothesis added, no pinned signature changed, no merged file edited, no RBM1D/RBM2D port (no diff-stat). Ports inside RBM3D: probe `t/T2471:RBM3D/Probe/T2471Pins.lean:166-340` (`3044b47e`; `Ker` at BA, target 5) and the 1a scratch `unc5.lean` (55 lines, T2471-prove.md (a″); UN-C5 identities), `TwistGridWTail_xi_ae` (`BA/TwistGridWTail.lean:1526`, for `martIncNg`), `GridMartBA_loop6_*`, `_sum_trace` (`BA/GridMartBA.lean`, for two labels).
* Route (D1 (i)): no second BA text of the tail. `Φ_b` is TL's observable at `c₁ = c₂ = b₁`, so TL's Hermitian test class, second-derivative bound, derivative formula, `Y` fields and `ι`-generic mgf are used unchanged.
* The new computation is the cross-label identity (Hermitian `H`): `STeeMg(σ,b,b') = Φ₂(Q₁^b,Q₁^{b'}) + Φ₂(Q₂^b,Q₂^{b'})` (two 6-loop identities, `W^d Σ_c Tr(R E_c R'^* E_c) = Φ₂(R,R')`), then `linTrVar ≤ Φ(R₁+R₂) ≤ 2(Φ(R₁)+Φ(R₂)) = 2 Re Σ κκ̄ STeeMg` (inequality: Cauchy-Schwarz over the cuts, as D202; `b₁ ≠ b₁'` included, no restriction to `b = b'`).
* `Z_b = stepZCN` with weight `δ_b` (linear in the weights through the trace form), `Y = martIncNg - Z`, so the a.e. split of `Inc` is an identity; `ξ = stepXiCN` is a copy of TL's `xi_ae` with `𝒦` cancelling.
* Target 6 follows UN-C5: `Mart = Σ_{j<k} martIncNg`, `Rem` = residual at every `n` (clause 1: `ring`); eventually (bridge H1, H2) `Mart = twMart`, `Rem = twRem` at `(σ, a 0, a 1, a 1)`; clause 2 = `baTwistGridRem_holds`; clause 3 = `baTwistGridTail_holds` at `ε'/2` with H3′, (5c) and `N^{ε'/2} ≥ 2` (`gridRepTailBA_shift_ineq`); clause 4 = target 4; `CK` = max of three.
* Root imports: not edited (CLAUDE.md §1: hub only); the pre-check above used a scratch file importing the module.

## (c) Verified Mathlib names used (new in this file, by compilation)
`tendsto_rpow_atTop`; `Filter.Tendsto.eventually_ge_atTop`; `Real.rpow_le_rpow`; `Real.mul_rpow`; `Real.rpow_le_rpow_of_exponent_le`; `Real.rpow_one`; `Real.rpow_nonneg`; `Real.rpow_add`; `Complex.re_le_norm`; `Complex.norm_conj`; `Complex.mul_conj'`; `Complex.ext`; `Finset.sum_mul_sum`; `Finset.sum_comm`; `Finset.sum_pair`; `Finset.sum_ite_eq`, `Finset.sum_ite_eq'`; `Finset.sum_sub_distrib`; `Matrix.sum_mul`, `Matrix.trace_sum`, `Matrix.smul_mul`, `Matrix.trace_smul`, `Matrix.sum_apply`, `Matrix.smul_apply`; `MeasureTheory.condExp_sub`, `condExp_const`, `condExp_finsetSum`, `condExp_smul`, `ae_all_iff`, `measure_mono`, `memLp_top_of_bound`; `one_le_pow₀`; `inv_anti₀`; `Nat.le_ceil`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
1. **Merge (hub):** add `import RBM3D.BA.GridRepTailBA` after the last `import` line of `RBM3D.lean` (not done here). The diff to `main` also contains `RBM3D/Probe/T2471Pins.lean` (stacked branch; probe, never merged): bring in only `RBM3D/BA/GridRepTailBA.lean`. P1b-2 merges after P1b-1 (already on main).
2. **Premise scan:** no registry line needed; `GridRepTailGen_Ker/Window/Inc/Hyp` are concluded by theorems of P1b-1 (band) and of this file (BA); `GridRepTailBA_F1/F2` are concluded by `gridRepTailBA_F1_ba`, `_F2_ba`; the bridge is inline.
3. **Style:** the module docstring has 7 long lines (l.19, 20, 23, 24, 25, 27, 31; as `BA/TwistGridWTail2.lean:16`); the file's `set_option linter.style.longLine false` comes after it. No other warning in the file's build output.
4. **Paper-delta candidates:** none new. The slot-count factor 2 in the `Z` proxy is the existing D202 type (`docs/paper-deltas.md:819`, `qvPropagatedN` with factor `k`); H3′ is `T2460a`; `Rem` as the residual at every `n` is CONTROL H256 (3), recorded.
5. **Not claimed:** `STGridRepNgL` (all `m`) at BA, zero-mode forms `Q ≠ ∅`, U5d (ticket "Not here"); `gridRepTailBA_*` hold for `m = 2` only.
