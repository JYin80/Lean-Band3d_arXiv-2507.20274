Prover model: claude-sonnet-5-5

# T2498a2 prove report: row a, second part (U3s3a′: `Induction/QBudgetA`, `QBudgetB`, `QEndA` in place, new `Induction/QEndA2`; targets 7, 8 and the rest of 9)
Branch `t/T2498a2` (stacked on `t/T2498`, `main` merged at `ee4af714`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498a2`), ticket `docs/tickets/T2498.md` with Amend 1. Stage 1b: first `date -u` Wed Oct 14 04:22:40 UTC 2026; final commit `39fd68bb`, 05:17:51 UTC (`git log`). Rows b, c and the first part (merged `ec57490f`) are not touched.

## (a) Math preflight
Not rewritten: `docs/reports/T2498-prove.md` (a), (a′), (a″) and `docs/reports/T2498-1a-audit.md` (PASS; cut U3s3a | U3s3a′ at `QLevelsB | QBudgetA`) stand for row a. The 1a forecast of this part is (xii) `a2 = 1009 / 1279 / 1616`.

## (a′) Preflight corrections and design deviations — Wed Oct 14 05:21:13 UTC 2026
No number or verdict of (a) is corrected. Deviations of the Lean text from the 1a plan (none changes a pinned text; each is a paper-delta candidate in (d)):
1. `hQ_altQNg`, `subGaussStop_altQNg` carry two radii `ε₁ ≤ ε` (`√A·W^{ε₁} ≤ W^ε`, `ε₁ ≤ ε` derived in the proof) and the constants `C4 ≤ Cv` with `A^k ≤ W^{(Cv−C4)ε}`, as part 1's `qvFormQNg_le_of_bounds` (`T2498a`).
2. The spectral levels of `ℬ₄ + ℬ₅` are the fields of `B45Gen_Facts` at one index (`κm`, `hmn`, `hward`, `hker`, `hK₆`, `hrow`, `hcol`), `Γ = κm⁻¹`, in `dFlowQNg_levelLin`, `alt_hdriftLinQNg`, `alt_hdriftGridQNg`, `altEnd_unQg`; the band `|E| ≤ 2 − κ` and `2/√κ` do not occur.
3. `altYGridNg` reads the flow matrix `Hf`, the law `μ` (`Step2EventsGen_Law`) and `Step34Gen_LCompat`; the band hypothesis `∀ n, 1 ≤ X n` (unused in its proof) is dropped.
4. D2 `gridDriftQNg_envelope_ev` is the 1a-audit fixed text (all-`w` link; drift classes and `0 < lam` under `∀ᶠ n`); the check is in (b).
5. Band text is kept with its proofs (twins appended, as in part 1) except `budgetAltQN` and `dDriftAltLinQN_le_shape` (corollaries at `bandStep2Mat`; the ≈ 250-line band proof of `budgetAltQN` is gone) and seven unread band theorems of `QBudgetA` (removed; table in (b)); superseded duplicates (D4) stay as band text.

## (b) Script output (stage 1b)
Commits (`TZ=UTC git log ee4af714..HEAD`): `1926cecf` 04:35:37, `aa2a926b` 04:44:45, `e51926c0` 04:57:39, `fcd3ef4f` 05:06:51, `39fd68bb` 05:17:51 (the first four are section checkpoints, the last is the full-build commit).
### Name-level tables (`tables.py`, `scope2.py`: declarations parsed from `git show ee4af714:` and `HEAD`, namespaces tracked; instance moved = same name in `QEndA2`)
```
file       lines old->new | public names at base: kept in file / moved to QEndA2 / removed | new public names: def thm inst(theorem named *_instance)
QBudgetA   1339-> 1497 |  17:  10 /  0 /  7 |  6 15  1
  removed (7, each has its generic twin): kappaAltQN_mul_Bctl_pow_le kappaAltQN_succ_mul_Bctl_pow_le kappaAltQN_le_kapFar qvBdAltQN_eq_qvShape tbInitAltQN tbDriftAltQN tbQvAltQN
QBudgetB   1142-> 1538 |  14:  14 /  0 /  0 |  1  5  4
QEndA      2056-> 1866 |  38:  22 / 16 /  0 |  2 19  0
QEndA2        0-> 1642 |   0:   0 /  0 /  0 |  0  0 31
```
```
QBudgetA|  6 def unedited, twin appended                               | altBudget_kapFar altBudget_qvFar qvBdAltQN cQVAltQN dDriftAltLinQN assembledRHSAltQN
QBudgetA|  7 removed                                                   | kappaAltQN_mul_Bctl_pow_le kappaAltQN_succ_mul_Bctl_pow_le kappaAltQN_le_kapFar qvBdAltQN_eq_qvShape tbInitAltQN tbDriftAltQN tbQvAltQN
QBudgetA|  2 band theorem kept, proof = corollary of the generic twin  | dDriftAltLinQN_le_shape budgetAltQN
QBudgetA|  1 superseded duplicate, band text kept                      | dDriftAltQN_le_shape
QBudgetA|  1 band instance kept                                        | budgetAltQN_instance
QBudgetB|  1 def unedited, twin appended                               | altBudgetNumQN
QBudgetB|  2 model-free, reused                                        | altBudgetExpQN altBudgetExpQN_of_choice
QBudgetB|  4 band theorem, proof kept, twin appended                   | dFlowQN_levelLin alt_hdriftLinQN dDriftAltLinQN_nonneg altBudgetNumQN_eventually
QBudgetB|  1 superseded duplicate, band text kept                      | dDriftAltQN_eq_lin
QBudgetB|  6 band instance kept                                        | dFlowQN_levelLin_instance alt_hdriftLinQN_instance dDriftAltLinQN_nonneg_instance dDriftAltQN_eq_lin_instance altBudgetExpQN_of_choice_instance altBudgetNumQN_eventually_instance
QEndA   |  2 def unedited, twin appended                               | altYSetN altExitTauN
QEndA   | 17 band theorem, proof kept, twin appended                   | measurableAltYSetN mem_of_lt_altExitTauN altExitMeasN ... altEnd_unQ
QEndA   |  3 superseded duplicate, band text kept                      | gridDriftQN_envelope altEnd_crudeSup altEnd_yMomentsMax
QEndA   | 16 instance moved verbatim to QEndA2                         | altYSetN_instance altYGridN_instance gridDriftQN_envelope_instance ... altEnd_yMomentsMax_instance
```
Private copies and `open private` (xi): `QEndA2` copies `altEnd_gridStep_nonneg`, `altEnd_gridTime_nonneg`, `altEnd_gridTime_le` (so no `open private` of a Q file); `open private` added: `QBudgetB:40` (`B45_norm_colsum`, `Induction/B45`), `QEndA:44-45` (`GridGoodGen_precL_whp`, `gridGood_gridTime_mem`), `QEndA2:1316` (`B45_norm_colsum`); none opens a Q file.
### G1: the frozen public names (`#check @name`, `pp.fieldNotation false`, run by `lake env lean` in the main worktree `22bbe858` (main oleans) and in the branch)
```
62 frozen public names (present at base and at HEAD; scratchpad `T2498a2/frozen.txt`)
branch: exit 0, 1238 output lines; main: exit 0, 1238 output lines; diff of the two outputs: 0 lines
Part 3 names of QBudgetA/B/QEndA (25) among the frozen names: 25; missing: []
$ git diff --stat ee4af714 main -- QBudgetA.lean QBudgetB.lean QEndA.lean   -> empty (base files = main's)
```
### D2 against the 1a-audit text (`T2498_GridDriftQEvFixed`, scratchpad `T2498/audit1a/D2fixed2.lean`; `d2check.lean`)
```
def body vs theorem statement (comments stripped, whitespace collapsed): IDENTICAL 1248 1248
$ lake env lean d2check.lean   # `example : T2498_GridDriftQEvFixed := @RBM.Ind.gridDriftQNg_envelope_ev`  -> exit 0
$ lake env lean docs/tickets/checks/T2498-check.lean   -> exit 0, 1705 output lines, 0 containing "error"
```
### Builds (all times `date -u`)
```
$ lake build RBM3D.Induction.QBudgetA RBM3D.Induction.QBudgetB RBM3D.Induction.QEndA RBM3D.Induction.QEndA2   # 05:20:30 -> 05:20:33
Build completed successfully (3910 jobs).
$ lake build   # whole library; RBM3D.lean carries `import RBM3D.Induction.QEndA2`; 05:15:28 -> 05:17:29, exit 0
info: RBM3D.lean:613:0: axiom audit: 15093 theorems, 4651 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 122 (borrowed 1, owed 55, structural 46, refuted 6, superseded 14).
Build completed successfully (4383 jobs).
$ grep -h 'premises found' ../T2498-merge-build.log   # hub's merge build of part 1 (scratchpad)
premises found by scanning: 122 (borrowed 1, owed 55, structural 46, refuted 6, superseded 14).
```
### Axioms (`ax2.lean`: `collectAxioms` over every non-internal constant of the four modules, then the 68 new public names)
```
modules found 4; declarations 131; [([Classical.choice, Quot.sound, propext], 131)]
new public names checked: 68; with a non-standard axiom: 0
RBM.Ind.{ altBudget_kapFarg altBudget_qvFarg qvBdAltQNg cQVAltQNg dDriftAltLinQNg assembledRHSAltQNg altBudget_kapFarg_band altBudget_qvFarg_band qvBdAltQNg_band cQVAltQNg_band 
  dDriftAltLinQNg_band assembledRHSAltQNg_band kappaAltQNg_mul_Bctl_pow_le kappaAltQNg_succ_mul_Bctl_pow_le kappaAltQNg_le_kapFar qvBdAltQNg_eq_qvShape tbInitAltQNg tbDriftAltQNg 
  tbQvAltQNg dDriftAltLinQNg_le_shape budgetAltQNg QBudgetAInst.budgetAltQNg_instance altBudgetNumQNg altBudgetNumQNg_band dFlowQNg_levelLin alt_hdriftLinQNg dDriftAltLinQNg_nonneg 
  altBudgetNumQNg_eventually QBudgetBInst.dFlowQNg_levelLin_instance QBudgetBInst.alt_hdriftLinQNg_instance QBudgetBInst.dDriftAltLinQNg_nonneg_instance 
  QBudgetBInst.altBudgetNumQNg_eventually_instance altYSetNg altExitTauNg altYSetNg_band altExitTauNg_band measurableAltYSetNg mem_of_lt_altExitTauNg altExitMeasNg altYGridNg 
  gridDriftQNg_envelope_ev assembledRHSAltQNg_qErr_le hQ_altQNg subGaussStop_altQNg alt_hkerGridQNg alt_hdriftGridQNg alt_hA0clsGridQNg alt_hDclsGridQNg altEnd_driftSupg altEnd_hexpg 
  altEnd_stronglyMeasurable_zVecQNg altEnd_aFroz_eq_aTrueg altEnd_unQg QEndAInst.altYSetNg_instance QEndAInst.altYGridNg_instance QEndAInst.gridDriftQNg_envelope_ev_instance 
  QEndAInst.assembledRHSAltQNg_qErr_le_instance QEndAInst.hQ_altQNg_subGaussStop_altQNg_instance QEndAInst.alt_hkerGridQNg_instance QEndAInst.alt_hdriftGridQNg_instance 
  QEndAInst.alt_hA0clsGridQNg_instance QEndAInst.alt_hDclsGridQNg_instance QEndAInst.altExitMeasNg_instance QEndAInst.altEnd_hexpg_instance 
  QEndAInst.altEnd_stronglyMeasurable_zVecQNg_instance QEndAInst.altEnd_aFroz_eq_aTrueg_instance QEndAInst.altEnd_unQg_instance QEndAInst.altEnd_driftSupg_instance }: [propext, Classical.choice, Quot.sound]
```
### Targets: `file:first-last line` of the statement (to `:=`) and `[i file:line]` = its compiled instance (a `theorem`/`example` that applies it at concrete data)
```
7  vocabulary altBudget_kapFarg 191 altBudget_qvFarg 195 qvBdAltQNg 201 cQVAltQNg 214 dDriftAltLinQNg 220 assembledRHSAltQNg 226 (QBudgetA); bridges `*_band` QBudgetA:245-267 (`rfl`)
   kappaAltQNg_mul_Bctl_pow_le QBudgetA:284-286 [i QBudgetA:1369]
   kappaAltQNg_succ_mul_Bctl_pow_le QBudgetA:298-300 [i QBudgetA:1376]
   kappaAltQNg_le_kapFar QBudgetA:311-313 [i QBudgetA:1383]
   qvBdAltQNg_eq_qvShape QBudgetA:353-359 [i QBudgetA:1389]
   tbInitAltQNg QBudgetA:364-368 [i QBudgetA:1402]
   tbDriftAltQNg QBudgetA:384-395 [i QBudgetA:1406]
   tbQvAltQNg QBudgetA:448-459 [i QBudgetA:1414]
   dDriftAltLinQNg_le_shape QBudgetA:526-531 [i QBudgetA:1418]
   budgetAltQNg QBudgetA:582-621 [i QBudgetA:1465]
   altBudgetNumQNg QBudgetB:121-122 [i QBudgetB:1484]
   dFlowQNg_levelLin QBudgetB:858-876 [i QBudgetB:1326]
   alt_hdriftLinQNg QBudgetB:955-984 [i QBudgetB:1348]
   dDriftAltLinQNg_nonneg QBudgetB:999-1001 [i QBudgetB:1398]
   altBudgetNumQNg_eventually QBudgetB:1032-1039 [i QBudgetB:1484]
8  QEndA
   altYSetNg QEndA:1033-1034 [i QEndA2:1090]
   altExitTauNg QEndA:1039-1040 [i QEndA2:1553]
   measurableAltYSetNg QEndA:1062-1063 [i QEndA2:1090]
   mem_of_lt_altExitTauNg QEndA:1070-1075 [i QEndA2:1394]
   altExitMeasNg QEndA:1080-1083 [i QEndA2:1553]
   altYGridNg QEndA:1150-1155 [i QEndA2:1098]
   gridDriftQNg_envelope_ev QEndA:1184-1200 [i QEndA2:1119]
   assembledRHSAltQNg_qErr_le QEndA:1297-1319 [i QEndA2:1143]
   hQ_altQNg QEndA:1359-1379 [i QEndA2:1178]
   subGaussStop_altQNg QEndA:1522-1555 [i QEndA2:1178]
   alt_hkerGridQNg QEndA:1582-1599 [i QEndA2:1369]
   alt_hdriftGridQNg QEndA:1618-1642 [i QEndA2:1394]
   alt_hA0clsGridQNg QEndA:1659-1673 [i QEndA2:1428]
   alt_hDclsGridQNg QEndA:1684-1707 [i QEndA2:1472]
   altEnd_driftSupg QEndA:1717-1721 [i QEndA2:1617]
   altEnd_hexpg QEndA:1738-1751 [i QEndA2:1561]
   altEnd_stronglyMeasurable_zVecQNg QEndA:1769-1774 [i QEndA2:1583]
   altEnd_aFroz_eq_aTrueg QEndA:1787-1791 [i QEndA2:1589]
   altEnd_unQg QEndA:1802-1819 [i QEndA2:1600]
```
Band bridges `altBudget_kapFarg_band`, `altBudget_qvFarg_band`, `qvBdAltQNg_band`, `cQVAltQNg_band`, `dDriftAltLinQNg_band`, `assembledRHSAltQNg_band` (QBudgetA:245-267), `altBudgetNumQNg_band` (QBudgetB:156), `altYSetNg_band`, `altExitTauNg_band` (QEndA:1048-1053) are `rfl`.
### Compiled nonempty instances: data and hypotheses left open
Data (`d = 3`, `sz0`): `QBudgetA` §5 `n = 0`, `E ≡ 1/2`, `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4`, `m = 1`, `C4 = qProxy4C 3 3 10 (1/2) 1`; `QBudgetB` §4 `n = 4`, `E ≡ 0`, `m = 2` (the eventual instance: `E ≡ 1/2`, `m = 1`, `κ' = 24/25`); `QEndA2` `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `m = 2`, `n = 4` or a large `n` where an abstract threshold (`qProxyW0`, `QDriftA_W0`, `W₀`) enters (`K n = N_n^{31}` in `assembledRHSAltQNg_qErr_le_instance`, `⌈N^{D''+14}⌉` in the `hQ` instance); alternating `σ`, explicit mollifier. Every deterministic hypothesis is discharged. Left open, both registered pins: `hKb : STKboundgL` (`gridDriftQNg_envelope_ev_instance`, as `GridEnvelopeGenCheck`) and `hP : PrecL …` (`altYGridNg_instance`). `AzumaSubGNg` and `QVPropagatedNg` are the theorems `azumaSubGNg`, `qvPropagatedNg`. Example (`QBudgetA:1465-1472`):
```
theorem budgetAltQNg_instance :
    assembledRHSAltQNg (bandStep2Mat sz0 Einst) sInst vg Kg 0 1 C4₀ 10 1 1 (1 / 2) (4 / 5) Γ4 Λ3
        (fun j => dDriftAltLinQNg (bandStep2Mat sz0 Einst) 0 (gridTime sInst vg Kg 0 j) 1 (Γ4 0) 1 12 1 Cn₀
          (1 / 5) 6 1 1)
        (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (7 + 2 * Cn₀) 1 (1 / 21) 1 (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (C4₀ + Cn₀ + 12) *
        (Λ3 0 ^ ((1 : ℝ) / 2) + (1 + 12 + 1 + 1)) * (sz0.Bctl 0 (vg 0)) ^ (1 + 1 + 1) := by
```
### Name clash (`git grep -w -F -l` of the 68 new final components, `RBM3D RBM3D.lean`)
```
68 distinct final components; names with a hit: main 22bbe858 0, t/T2498 5e8ef75a 0, t/T2499 0c272838 0, t/T2500 fc90ad3a 0, t/T2501 0d98bc2b 0, t/T2501a2 3f8e9624 0, t/T2501b df731125 0, t/T2502 b6bcabe8 0, t/T2503 9c304204 0
```
### Lines (stop rule), numstat, calibration
```
    1497 RBM3D/Induction/QBudgetA.lean
    1538 RBM3D/Induction/QBudgetB.lean
    1866 RBM3D/Induction/QEndA.lean
    1642 RBM3D/Induction/QEndA2.lean
    6543 total
$ git diff --numstat ee4af714 HEAD   (QEndA -> QEndA2 moved = difflib blocks >= 3 lines of old QEndA found in QEndA2: 1038)
1	0	RBM3D.lean
638	480	RBM3D/Induction/QBudgetA.lean
428	32	RBM3D/Induction/QBudgetB.lean
841	1031	RBM3D/Induction/QEndA.lean
1642	0	RBM3D/Induction/QEndA2.lean
1	1	RBM3D/Test/Axioms.lean
added (4 Lean files) 3549, removed 1543, moved 1038; added - moved = 2511; 1a central 1279 (x1.74 = 2225): realized/forecast 1.96
row a (part 1: 2256 + this part: 2511) = 4767 against the ticket's 1,880 (sensitivity price 3,271): x2.54, +46% over the sensitivity price
```
### Hypothesis rules and layering (`greps.sh`; `C1`/`X1-C1` regex of `T2498.md:92` run over the 39 new generic statements, defs and theorems to `:=`)
```
C1 / X1-C1 regex hits in the generic statements: 1  ('gridDriftQNg_envelope_ev', 'QEndA', 1191, 'Lloop')   -> `KLloopOf` in the 1a-audit D2 link (model-free label list)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" <4 files> | wc -l
       0
$ grep -nE "^import RBM3D\.BA" <4 files> | wc -l
       0
$ grep -nE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" <4 files> | wc -l
       0
$ grep -n withLam <4 files> | wc -l
       0
$ git diff ee4af714 HEAD -- <4 files> | grep -E "^[-+]import"
RBM3D/Induction/QBudgetA.lean: +import RBM3D.Chain.NQBudgetGen
RBM3D/Induction/QBudgetA.lean: +import RBM3D.Chain.NQLinGen
RBM3D/Induction/QEndA2.lean: +import RBM3D.Induction.QEndA
RBM3D/Induction/QEndA2.lean: +import RBM3D.Chain.QGridGen2
$ grep -nE "^open private" <4 files>
RBM3D/Induction/QBudgetB.lean:40:open private B45_norm_colsum from RBM3D.Induction.B45
RBM3D/Induction/QEndA.lean:44:open private GridGoodGen_precL_whp from RBM3D.Chain.GridGoodGen
RBM3D/Induction/QEndA.lean:45:open private gridGood_gridTime_mem from RBM3D.Induction.GridGoodN
RBM3D/Induction/QEndA2.lean:1316:open private B45_norm_colsum from RBM3D.Induction.B45 in
$ git show ee4af714:<file> | grep -c "^open private"  (base)
QBudgetA: 0
QBudgetB: 0
QEndA: 0
$ X1-C4 defs in the writable files
       0
$ T2497 QGrid names defined in the writable files
       0
$ grep -nE "∀ \(sz : Sizes d\)" <4 files> (new text only: line numbers)
RBM3D/Induction/QBudgetB.lean:175:    ∀ (sz : Sizes d) (n : ℕ) (E u κ Γc Λc Φc Γ Φ₁ Φ₂ Φ₃ τ' ε' D' ν X τN : ℝ)
RBM3D/Induction/QBudgetB.lean:264:    ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
RBM3D/Induction/QEndA.lean:743:    ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
RBM3D/Induction/QEndA.lean:813:    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ)
RBM3D/Induction/QEndA.lean:1686:      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (Cm : Step2Mat sz) (gK : ℕ → ℝ) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool)
$ git diff --name-only main...t/T2498a2   -> RBM3D.lean RBM3D/Induction/{QBudgetA,QBudgetB,QEndA,QEndA2}.lean RBM3D/Test/Axioms.lean RBM3D/Probe/T2498Pins.lean (the probe is the stack base `t/T2498`, never merged)
$ git diff --name-only ee4af714 HEAD -- QEndGrid QEndB1 QtXiRoundLift QGridA QGridB NQ* Chain/NQ* BA | wc -l   -> 0
cone (reverse imports of `Induction.QBudgetA`, script over the `import` lines): 12 modules: MainIndHolds MainIndOut QBudgetB QEndA QEndA2 QEndB1 QEndGrid QtXiRoundLift Step3 Step4 Main.BandTerminal Probe.T2498Pins
$ grep -rln "import RBM3D.Induction.QEndA2" RBM3D RBM3D.lean   -> RBM3D.lean
```
### Registry (`Test/Axioms.lean`; the only edit is the `GoodSetNg` owner text of `T2498.md:90`)
```
$ git diff -U0 ee4af714 HEAD -- RBM3D/Test/Axioms.lean | grep -c '^[-+]   `'   -> 2
old: ... band re-derivation `hQ_nonAltN_of_Ng`; U3s3 reads it); BA: the initial membership
new: ... band re-derivation `hQ_nonAltN_of_Ng`; U3s3 reads it through `gridGoodNgL_of` and `stOeqNQPTgL''_of`; alternating majorant `hQ_altQNg` (T2498, `Induction/QEndA`)); BA: the initial membership
$ git diff --stat ee4af714 HEAD -- RBM3D/Test/Axioms.lean | tail -1   -> 1 file changed, 1 insertion(+), 1 deletion(-)  (no `owedProps` line added; the premise scan found 122, as at `main`)
```

### Narrative
- Twins `<band name>g` are appended in namespace `RBM.Ind` (`open RBM.BA`, no `BA/*` import); the band vocabulary defs are unedited and each twin has a `rfl` bridge. The kernel is `Step2Gen_UN/ThetaN` at `Cm`, `η_u = Cm.eta n u`, `stepErrNg`; `LoopForm` and the inline `‖Cm.m n‖ ≤ 1` replace `|E n| < 2`.
- `QBudgetA`: kernel weights, the three term budgets on `tbInitNg`/`tbDriftNg`/`tbQvNg`, `dDriftAltLinQNg_le_shape`, `budgetAltQNg` (the proof of the band `budgetAltQN` with `Cv` explicit and `Cm.eta`, `(Cm.m n).im`). The two band theorems read by `QEndGrid` are corollaries at `bandStep2Mat sz (fun _ => E n)`; seven unread band theorems are removed (readers outside the file: 0 before this edit, `git grep -lw`); the band examples of §5 for the removed theorems are re-pointed to the twins (8 generic examples); the full build compiles `QEndGrid`, `QEndB1`, `QtXiRoundLift` unchanged.
- `QBudgetB`: the private rows `QBudgetB_ev_ha2`, `QBudgetB_ev_ha3` read a sequence `im n` instead of `(mE (E n)).im` (band proof and generic proof share them); `dFlowQNg_levelLin` is the band proof on `drift13_fastDecayg`, `driftTensorNg_norm_le_of_goodLin`, `goodSetNg_LKM_far`, `altB45Ng_levelM`.
- `QEndA`: §0-§7 band text unchanged; §8 (the band instances) moved verbatim to `QEndA2` (`wc`: 1,866 and 1,642 lines). The generic text follows the band order: exit family, measurability, `altYGridNg` (transfer by `Step2EventsGen_Law`, union bound `highProbAt_iInter`), D2, `hQ_altQNg` (D1 `QProxyG_KerEK4` at `gK`, R1 comparison, `NQGood1Gen_eta_anti`, `norm_STeeMg_shiftNg_le`, `qvFormQNg_le_of_bounds` at `m + 1`), `subGaussStop_altQNg` (`azumaSubGQ_gridExitNg`), C3-C5.
- D2 (`gridDriftQNg_envelope_ev`): the premise per index is T2497's `gridDriftQNg` classes under `∀ᶠ n`; the envelope of `𝒦` on `[0, u_{j+1}]` is `exists_norm_KI_le_wing` at the worst-time sequence of the band proof (`gridDriftQN_envelope'`); the statement is identical to the 1a-audit text (script above).
- Instances: all generic targets have one (table above); the 16 band instances moved to `QEndA2` still apply the band theorems, the 15 new ones apply the generic theorems at `bandStep2Mat sz0 E`. The band `altEnd_crudeSup` is still read by the moved band instances (`crude_u`).
- UBA-C1 / family rows as used here: R1 (`hcmp`, `hA`, `hdW`, `hAk`, `C4 ≤ Cv`, the two radii) enters only `hQ_altQNg`, `subGaussStop_altQNg`, `alt_hkerGridQNg` (D1 `hKer`, row 8) and, through `alt_hDclsQNg`, `alt_hDclsGridQNg` (`Step5KerGen_ThDecay`, `C₆`, `A`, row 9); the spectral fields of `B45Gen_Facts` (row 9) enter `dFlowQNg_levelLin`, `alt_hdriftLinQNg`, `alt_hdriftGridQNg`, `altEnd_unQg`; the drift classes and the all-`w` link (row 11) enter `gridDriftQNg_envelope_ev` (the link at one `n`, `HierDriftGen_KLink`, and `Step2Gen_USemigroup` enter `altEnd_hexpg`, `altEnd_aFroz_eq_aTrueg`). None of R1, D1, D2 enters `QBudgetA`, `altBudgetNumQNg_eventually`, `altYGridNg`; no `∀ n` drift premise, no `STGridRepNgL`.
- No stop rule fires: every file is under 2,000 lines (largest `QEndA` 1,866), no band file outside the writable files is edited, no band `def` changes, no import of a new file of this row by an in-place file, no `BA/*` import; the premise scan of the full build finds no new premise (122, as at `main`); the instances leave only the two registered pins open.
- Calibration: added − moved = 2,511 against the 1a central 1,279 (×1.96); row a total 4,767 against 1,880 (sensitivity price 3,271); `QEndA` grew by ≈ 850 lines against the ticket's ≈ 350. The dispatcher decides what this does to rows b, c and the UP-C3 line (5,850); I only report it.

## (c) Verified Mathlib names (all 69 namespace-qualified names of the added lines resolve: `#check @name` in a file importing `QEndA2`, exit 0, 0 errors; none absent)
`Complex.{norm_of_nonneg}`
`ENNReal.{ofReal}`
`Eventually.{of_forall}`
`Filter.{Eventually.of_forall, eventually_ge_atTop, not_eventually.1}`
`Fin.{append, last}`
`Finset.{le_sup', mem_range.1, mem_univ, range, sum_congr, sum_nonneg, univ.erase}`
`Matrix.{isHermitian_zero}`
`Measurable.{comp, stronglyMeasurable}`
`MeasureTheory.{hittingBtwn_mem_set_of_hittingBtwn_lt}`
`Nat.{cast_ne_zero.2, cast_nonneg, ceil_pos.2, eq_zero_of_not_pos, le_ceil, le_mul_of_pos_right, le_self_pow, le_succ, lt_succ_iff.1, lt_succ_of_le, one_le_iff_ne_zero.2, pos_of_ne_zero, pow_le_pow_left, zero_le}`
`Real.{coe_toNNReal, exp, exp_le_one_iff, le_coe_toNNReal, le_sqrt', log, log_le_sub_one_of_pos, log_mul, log_nonneg, log_two_lt_d9, mul_self_sqrt, one_le_rpow, rpow_add, rpow_le_one_of_one_le_of_nonpos, rpow_le_rpow_left_iff, rpow_le_rpow_of_exponent_le, rpow_le_rpow_of_nonpos, rpow_mul, rpow_natCast, rpow_neg, rpow_neg_one, rpow_nonneg, rpow_one, rpow_pos_of_pos, rpow_two, rpow_zero, sq_sqrt, sqrt, sqrt_eq_rpow, sqrt_le_sqrt, sqrt_nonneg, sqrt_one, sqrt_sq}`
`Set.{Icc, indicator_of_notMem, mem_iInter.1}`

## (d) Open issues and paper-delta candidates
- Registered pins left as hypotheses of two instances: `STKboundgL` in `gridDriftQNg_envelope_ev_instance` (its proof `bandFM_STKbound` sits in `BA/FlowPins`, not importable from an in-place file) and `PrecL …` in `altYGridNg_instance` (the owed `STLKU`-type control).
- `Test/Axioms.lean`: only the `GoodSetNg` owner text is edited. The `STXiBootgL'` comment `(proofs: U3s3, U3s4)` (1a (x)) is not in the ticket's registry text and is not touched.
- `RBM3D.lean`: one line `import RBM3D.Induction.QEndA2` after the last import (the hub unions it with T2502/T2503). `Probe/T2498Pins.lean` is untouched and stays on the branch.
- The superseded duplicates `gridDriftQN_envelope`, `altEnd_crudeSup`, `altEnd_yMomentsMax`, `dDriftAltQN_le_shape`, `dDriftAltQN_eq_lin` have no generic twin (ticket D4) and stay band text with their band instances.
- BA readings of the new statements are not proved here (BA sources: `baStep2Mat_KI`, `baB45Gen_facts`, `baEKSumDecay2_holds`, T4/T5-BA classes); rows b, c read the twins by name.
- Paper-delta candidates (Lean devices; no paper statement changes), continuing `T2498a`-`f` of part 1: `T2498g` the spectral levels `κm`, `K₆`, `hward`, `hker`, `hrow`, `hcol` and `Γ = κm⁻¹` replace `|E| ≤ 2 − κ`, `2/√κ` in the linear level and in `altEnd_unQg`; `T2498h` D2 `gridDriftQNg_envelope_ev` (all-`w` link, classes under `∀ᶠ n`, wing envelope; the 1a-audit text); `T2498i` two radii `ε₁ ≤ ε` and `C4 ≤ Cv` in `hQ_altQNg`, `subGaussStop_altQNg` (continues `T2498a`); `T2498j` removal of seven unread band theorems of `QBudgetA`, `budgetAltQN` and `dDriftAltLinQN_le_shape` as corollaries (continues `T2498c`); `T2498k` `altYGridNg` over `(μ, Hf)` with `Step34Gen_LCompat`, `Step2EventsGen_Law`, without the unused `∀ n, 1 ≤ X n`.
