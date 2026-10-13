Prover model: claude-sonnet-5-5

## (a) Math preflight
No section (a) exists for row b: at the 1b start `wc -l docs/reports/T2496b-prove.md` answered `No such file or directory` (first tool call, `date -u` = Tue Oct 13 11:14:50 UTC 2026). The stage-1a material is `docs/reports/T2496-prove.md` (a), (a″) and `T2496-1a-audit.md` (PASS; split applies); it is cited, not repeated, and not edited. `$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2496b`.

## (a′) Preflight corrections at the 1b start — Tue Oct 13 11:35:29 UTC 2026
**Verdict: BLOCKED at the 1b-start name-level check (row U4s3b, targets 6-10). No Lean written in the sole writable files, no build of them, no Lean commit by the 1b: `t/T2496b` is `t/T2496` e96c59dd plus the instructed merge of `main` e89f5609 (merge commit f5d1c244, 2026-10-13 11:15:12 UTC); `DuhamelI` 1,994 lines, `DuhamelII` 976, `DuhamelI2` absent.** Targets 8 and 9 (and the grid part of target 7) read two facts of the grid walk that have no home in family rows 1-11 as fixed at the 1a-audit, nor in Amend 1 (A6-A9). Each needs a new premise, i.e. a new hypothesis (stage rule 4), so the dispatcher amends (precedent: Amend 1 of this ticket, `T2496-prove.md` (a′) G1-G4). Not affected: target 6 and the kernel and numerics part of target 7. Affected: targets 8, 9, the section and lift part of 7, and the instances (target 10).

| # | band fact read (file:line, `DuhamelI` / `DuhamelII`) | home in rows 1-11 + A6-A9 | band discharge | BA source | status |
|---|---|---|---|---|---|
| 1 | `v3_premises_of_stFlow`: admissible sizes, `\|E n\| ≤ 2-κ`, `t<1` (`:1439, :1905` / `:517, :882`) | row 1 `Step5CasesGen_FlowFacts` (`Admissible`, `T0<1`, `κm ≤ Im m`, `eta = (1-u) Im m`; as `stEtermsMidgL_of`) | `step5CasesGen_flowFacts_band` | `EMn2BA_T0_lt_one`, `EMn2BA_mF_data` | OK |
| 2 | `Theta`, `Ugen`, `step5Kernel_profile_explicit_holds` (`:516-647`) | row 2 `IniTermGen_KerFacts` (`USemigroup`, `ThDecay`, R1) with `Step5KerGen_UN_decomp`, `step5KerGen_profile_holds` | `iniTermGen_kerFacts_band` (compiled, probe C) | U4-BA (a) | OK |
| 3 | grid Duhamel form `pfStep5Grid_duhamel` (`:1049` / `:291`) | row 3 `GridRepTailGen_Ker` (guarded) through target 6 | `gridRepTailGen_ker_band` (compiled, probe C) | `gridRepTailGen_ker_BA`, `BAflow_real` | OK, see (d) 2 |
| 4 | `ST_gridMart_of_repN (stGridRepN_holds d hd)` (`:1446` / `:529`) | row 4 `STGridMartgL` | `bandStep2_STGridMart.1 (ST_gridMart_of_repN …)` (compiled, probe C) | `baGridMart_holds` (compiled, probe C) | OK |
| 5 | **model sections ↔ grid walk**: `ST_grid_whp_zero` (`:1475` / `:558`), `ST_grid_whp_of_sections` via `duhamelI_whp_sec` (`:1492-1504` / `:575-587`), `ST_pathP_eq_seqP` (`:1641` / `:724`); measurability `STLKM_measurable`, `STEGtM_measurable`, `STEEkM_measurable`, `duhamelI_ELKLK_meas` (`:1342-1346, :1365-1369, :1479-1509, :1640`) | **none** (scan below) | `Step2EventsGen_bandGrid sz (STflowE z)` | `Step2EventsGenTw_baGrid sz (BAflowLam0 sz z) (BAflowEs sz z)` | **G5** |
| 6 | **Hermitian grid walk** `pathH_isHermitian` (`:1670-1671` / `:754-755`): the a priori bound `duhamelI_apriori` (`:1209`) at the grid matrices; generic `norm_loopFine_crudeNg` needs `H.IsHermitian` | **none** (scan below) | `pathH_isHermitian` | `baStep2Mat_Hpath_herm` (`Step2IterBA:62`) | **G6** |
| 7 | `LemDecCalELip_LK2` (`DuhamelI:1918`), `LemDecCalELip_LK_sub` (`DuhamelII:423`), `LemDecCalELip_env` (`DuhamelII:415`) | D2 row 8 `hFM`, D3 `hKs` + `hmn` row 9, `hLF` row 10; targets 1 `LemDecCalELip_LK2gL`, `lemDecCalELipG_loops`, `LemDecCalELip_LK_subg`, `LemDecCalELip_envg` | `lemDecCalELipG_flowMod_band`; `T2496b_Ks_band` from `LemDecCalELip_STKloop_two_lip` (compiled, probe D) | D2 at `seqHflowBA`, `contGood (sz.withLam 0)` (U4-BA; scratch `ba_D2` of the U4s3a report); `baKsol_two` / U3-BA twin | OK |
| 8 | `LemDecCalELip_STKloop_two_norm`, `‖𝒦^{(2)}‖ ≤ N` (`:1229`) | A8 (a) `lemDecCalELipG_Kn` from `Step2IterGen_K2` (row 7 as amended by A9) and `STBdatagL` (row 6); my reading of A9: `Step2IterGen_K2` is a premise of 8, 9 as of 5 (to confirm, (d) 1); `EtermsMid_NewKLKL` is not read | `step2IterGen_K2_band`, `bandFM_STBdata` | `baStep2_K2` (compiled, probe C), `baSTBdatagL_holds` | OK |
| 9 | `norm_loopFine_crudeN` (`:1215`), `norm_mE`, `sum_norm_SB_row`, `etaT`, `zt` | `norm_loopFine_crudeNg` under row 10, `hmn`, `hSr` (A7) | as `etermsMid_band_gL` | `baStep2Mat_loopForm`, `BAm_norm_le_one`, `S = 1` | OK |
| 10 | `cont_highProbAt_good sz` (lift, `:1805`) | D2 event `G`, `HighProbAt μ sz.size G` (`etermsMid_lift` pattern) | `lemDecCalELipG_flowMod_band` | as row 7 (D2) | OK |
| 11 | `GridDuhamelN_Ugen_self`, `𝒰_{s,s} = 1` (`:1559` / `:642`) | row 2 `USemigroup` (`uKer_{t,t} = 1`), `Step5KerGen_uKer_eq` | `step2Gen_USemigroup_band` | `BAuKerSemigroup_holds` | OK |

**Why G5 and G6 cannot be derived from the premise rows.** `STGridMartgL` quantifies over the walk law `(mkM sz z).Pp` only: its signature has no `Measure` argument (probe A). The generic grid lemmas take `Step2EventsGen_Law Cm μ Hm` (law of `Hpath` at grid index `k` = law of `Hm` at the grid time) and the matrix-level measurability from `Step2EventsGen_Grid Cm μ` (probe A). D2's `Hm` is an existential with `HighProbAt μ`, not tied to `Pp`. Scan of the premise definitions for the model law and the walk:
```
$ python3 $S/premlaw.py        # tokens counted in the body of each premise definition (comments stripped)
Step5CasesGen_FlowFacts      RBM3D/Chain/Step5CasesGen.lean:140   Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=0
IniTermGen_KerFacts          RBM3D/Chain/IniTermIIGen.lean:68    Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=0
GridRepTailGen_Ker           RBM3D/Chain/GridRepTailGen.lean:54    Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=0
STGridMartAtgL               RBM3D/Chain/Step2Gen.lean:857   Pp=3 Hpath=1 Step2EventsGen_Law=0 law=0 μ=0
STGridMartgL                 RBM3D/Chain/Step2Gen.lean:882   Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=0
STBdatagL                    RBM3D/Chain/Step2EventsGen.lean:966   Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=0
Step2IterGen_K2              RBM3D/Chain/Step2IterGen.lean:71    Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=0
LemDecCalELipG_FlowMod       RBM3D/Induction/LemDecCalELip.lean:311   Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=2
StepDecompGen_LoopForm       RBM3D/Chain/StepDecompGen.lean:60    Pp=0 Hpath=0 Step2EventsGen_Law=0 law=0 μ=0
Step2EventsGen_Grid          RBM3D/Chain/Step2EventsGen.lean:80    Pp=1 Hpath=1 Step2EventsGen_Law=0 law=0 μ=2
Step2EventsGen_Law           RBM3D/Chain/Step2EventsGen.lean:90    Pp=1 Hpath=1 Step2EventsGen_Law=1 law=0 μ=2
```
Among the scanned definitions only `STGridMartAtgL` mentions `Pp` (not `μ`), only D2 mentions `μ` (not `Pp`, `Hpath`), and only `Step2EventsGen_Grid`/`_Law` mention both. The merged generic grid consumers `OptL2Gen` and `Step2IterGen2` take both facts as unguarded family premises: `hGrid : ∀ sz z, Step2EventsGen_Grid (mk sz z) (law sz)` and `hHerm : ∀ sz z s t K n k ω, ((mk sz z).Hpath s t K n k ω).IsHermitian` (`Chain/OptL2Gen.lean:593-594, 863-866, 1113-1116`; `Chain/Step2IterGen2.lean:303-306`; the law alone as `hLaw` in `GridGoodGen:852`, `NQLinGen:369`, `NQEndFlowGen:688`).

**Amend proposal (texts compiled at band and BA, probe B).** A10 (G5): targets 8, 9 gain the unguarded premise `hGrid` above; A11 (G6): the unguarded premise `hHerm` above. The `Hm` of `hGrid` serves the transfer of E1-E4 and of the endpoint (law, measurability, clause 2 `LM`); the `Hm` of D2 serves the lift (`LemDecCalELip_LK2gL`); no coupling between them is used. Nothing else in the ticket changes; the premise list of `stDuhamelIgL_of`, `stDuhamelIIgL_of` would be: rows 1, 2 (+ the parameter `gK`), 3, 4, 6 (`STBdatagL`), 7 (`Step2IterGen_K2`), 8 (D2), 9 (`hmn`, `hKs`), A7 (`hSr`), 10 (`hLF`), A10, A11. Band and BA names are in the table; the BA discharges of rows 2, 7 (D2), 9 (`hKs`) have their owners as in the U4s3a report.

*Note, Tue Oct 13 17:41:32 UTC 2026 (`date -u`, rerun): the BLOCKED verdict above is closed by Amend 2 (`docs/tickets/T2496-amend-2.md`: A10 `hGrid`, A11 `hHerm`, `GridRepTailGen2` import, `DuhamelI2` cut, `Step2IterGen_K2`). The table and the scan above stay as the record of the 1b-start check; (b)-(d) below replace the previous ones.*

## (b) Script output (rerun on `t/T2496b`; `$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2496b`)
```
$ git merge main   # `date -u` Tue Oct 13 16:46:17 UTC 2026; main was docs-only ahead of 462b5e09
$ git -C ../RBM3D-wt/T2496b log -3 --format='%h %cd %s' | cut -c1-110    # commit made at `date -u` = Tue Oct 13 17:39:06 UTC 2026
038fbef5 Tue Oct 13 10:39:06 2026 -0700 T2496 U4s3b: DuhamelI, DuhamelI2, DuhamelII over the flow carrier (tar
74265465 Tue Oct 13 09:46:17 2026 -0700 Merge main into t/T2496b
7b9e0c4c Tue Oct 13 09:45:17 2026 -0700 H286: DECISIONS §306, ROUTES, HANDOFF, STARTUP, DISPATCHER-PROMPT, CON
$ lake build RBM3D.Induction.DuhamelI RBM3D.Induction.DuhamelI2 RBM3D.Induction.DuhamelII | tail -1
Build completed successfully (3943 jobs).
$ lake build      # full library with `#assert_rbm_axioms`; `date -u` 17:32:23 -> 17:34:24 UTC; last Lean edit and the build start are in one command (mtimes 10:32:12-10:32:23 local PDT = UTC-7)
info: RBM3D.lean:602:0: axiom audit: 14908 theorems, 4618 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4372 jobs).
$ wc -l RBM3D/Induction/Duhamel{I,I2,II}.lean      # stop size 2,000; 1,800 rule
  1087 DuhamelI.lean    1699 DuhamelI2.lean    968 DuhamelII.lean
$ git diff --numstat main...HEAD -- <the three files> RBM3D/Test/Axioms.lean
337 1244 DuhamelI | 1699 0 DuhamelI2 | 420 428 DuhamelII | 2 2 Test/Axioms     (added 2,458, removed 1,674)
$ python3 $S/rep/numstat.py   # non-blank added lines equal to a removed line, multiset over the three files: verbatim moved = 783
UP-C2 (d) landing = added 2,458 - moved 783 = 1,675; with U4s3a 1,411 (`T2496-prove.md` (b)): 3,086 against the calibration line 3,540 (D4). Stop-report forecast 1,714-1,782 (D1 336-380 lines).
$ git diff --name-only main...HEAD   ->  DuhamelI, DuhamelI2, DuhamelII, Test/Axioms (+ Probe/T2496Pins.lean from t/T2496, branch only, never merged)
$ git diff --name-only main...HEAD -- RBM3D/Chain RBM3D/BA RBM3D/Path <12 band readers of the ticket> | wc -l      ->  0
$ lake env lean $S/rep/axioms.lean | grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]'     # 22 names; lines of another form: 0
22   = the 16 new public declarations (`python3 $S/rep/names.py new`: duhamelIG_{Phi_STprof,Phi_lam,Ugen_le,mart_Ugen,apriori,lift} (DuhamelI); RBM.BA.{duhamelIG_duhamel,stDuhamelConclgL_engine,
       stDuhamelIgL_of}, duhamelIG_path_rem, duhamelI_Ks_band, duhamelI_band_gL (DuhamelI2); duhamelIIG_holder, RBM.BA.{stDuhamelConclgL_engineQ1,stDuhamelIIgL_of}, duhamelII_band_gL (DuhamelII))
       + stDuhamelI_holds, stDuhamelII_holds, stDuhamelConcl_engine, stDuhamelConcl_engineQ1, inst_duhamelI_proved, inst_duhamelII_proved
```
**Target statements, extracted by script** (`$S/rep/targets.txt`; long lines cut at 230):
```
-- target 6, DuhamelI2.lean:327 (variables `{d} {sz : Sizes d} {C : FlowFM sz} {n : ℕ}`)
theorem _root_.RBM.BA.duhamelIG_duhamel (hker : GridRepTailGen_Ker C n) (Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ)
    (A F Rem Mart : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (hk : u k < 1)
    (hA : ∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) (hRem : ∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R)
    (hrec : ∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (Step2Gen_ThetaN C n σ (u i) (A i) b + F i b) + Rem j b + Mart j b)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖A k a - Step2Gen_UN C n σ (u 0) (u k) (A 0) a -
        ∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN C n σ (u j) (u k) (F j) a -
        ∑ j ∈ Finset.range k, Step2Gen_UN C n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
      64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M)
--- target 8 (DuhamelI2.lean) ---
-- target 8, DuhamelI2.lean:1482
theorem _root_.RBM.BA.stDuhamelIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hF : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hKer : IniTermGen_KerFacts d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hGR : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hGM : STGridMartgL d Flow mkM T0) (hBd : STBdatagL d Flow T0) (hK2 : Step2IterGen_K2 d Flow mkM)
    (hFM : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
      ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c)
    (hmn : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hKs : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, t n ≤ T0 sz z n) →
        ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
          ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
            ‖(mkM sz z).K n u σ a - (mkM sz z).K n u' σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 2 + 2) * |u - u'|)
    (hLF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mkM sz z).Hpath s t K n k ω).IsHermitian) :
    STDuhamelIgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
-- target 9, DuhamelII.lean:823: the same 12 premises (`hF` ... `hHerm`); diff of the two signatures:
-theorem _root_.RBM.BA.stDuhamelIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
+theorem _root_.RBM.BA.stDuhamelIIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
-    STDuhamelIgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
+    STDuhamelIIgL d law Flow (fun sz z => (mkM sz z).toFlowFM) T0
```
```
$ lake env lean $S/rep/auditcheck.lean; echo $?    # docs/tickets/checks/T2496-check.lean + 3 auditor-style examples (text of `rep/auditcheck.lean:393-452`)
0   example : ∀ C n, GridRepTailGen_Ker C n → T2496_DuhamelForm C n := fun C n h => duhamelIG_duhamel h  |  T2496_DuhamelIHead := stDuhamelIgL_of ..  |  T2496_DuhamelIIHead := stDuhamelIIgL_of ..
    (negative control: the same file plus `example : False := RBM.BA.duhamelIG_duhamel` gives 1 error line)
$ lake env lean $S/rep/frozen.lean; echo $?     # G1: `example : <old text of main> := <old name>` for stDuhamelI_holds, stDuhamelII_holds, stDuhamelConcl_engine, stDuhamelConcl_engineQ1
0
```
**Compiled nonempty instances** (`awk` of `^example|^theorem inst_`; every deterministic hypothesis discharged at `d = 3`):
* target 6 `duhamelIG_duhamel`: `DuhamelI2.lean:1647` at the band kernel `bandStep2Mat sz0 (fun _ => 1/2)`, `n = 0`, `σ = (+,-)`, `k = 3`, `Δ = 1/16`, `A_j ≡ 1 + j/10`, `Mart_j ≡ j/10`, `F_i = -Θ^{(2)}A_i`, K1-K4 from `gridRepTailGen_ker_band`.
* target 8 `stDuhamelIgL_of`: `DuhamelI2.lean:1665` (`inst_duhamelI ((STDuhamelI_iff_gL 3).2 (duhamelI_band_gL 3 _)) Cd hCd`, every premise from a band result), `:1608` `inst_duhamelI_proved`, engines `:1614`, `:1622` (`hE` = `STEtermsMidConcl`, another gate's pin, stays a hypothesis).
* target 9 `stDuhamelIIgL_of`: `DuhamelII.lean:962` (same pattern with `inst_duhamelII`), `:923` `inst_duhamelII_proved`, engine `Q1` examples `:931`, `:940`, and `stDuhamelII_holds` at interior data `:948`.
* target 7 kernel facts: `DuhamelI2.lean:1673` (`duhamelIG_Phi_lam` at `(sz0, z0)`, `n = 0`, `w = 1/2`), `:1692` (`duhamelIG_Ugen_le`).  `duhamelIG_apriori`, `_lift`, `_mart_Ugen`, `_path_rem`, `duhamelIIG_holder` and the private sections have no stand-alone instance; they are on the proof path of the instances above.
**Name-level table, premises of targets 8, 9 as used** (guard; band discharge compiled in `duhamelI_band_gL`; BA source: `#check` of the merged names, `$S/rep/banames.lean`, 11 names, 0 errors):
| # | premise | guard | band discharge | BA source |
|---|---|---|---|---|
| 1 | `hF` `Step5CasesGen_FlowFacts` | built in | `step5CasesGen_flowFacts_band` | `EMn2BA_T0_lt_one`, `EMn2BA_mF_data` |
| 2 | `hKer` `IniTermGen_KerFacts` + `gK` (R1 inside) | built in | `iniTermGen_kerFacts_band`, `gK = sz.lam` | U4-BA (a) (owner, not merged) |
| 3 | `hGR` `GridRepTailGen_Ker` | `0 < κ → Flow →` | `gridRepTailGen_ker_band` | `gridRepTailGen_ker_BA`, `BAflow_real` |
| 4 | `hGM` `STGridMartgL` | pin, `∃ C₀` before the family | `bandStep2_STGridMart.1 (ST_gridMart_of_repN (stGridRepN_holds d hd))` | `baGridMart_holds` |
| 5 | `hBd` `STBdatagL`, 6 `hK2` `Step2IterGen_K2` | as merged | `bandFM_STBdata`, `step2IterGen_K2_band` | `baSTBdatagL_holds`, `baStep2_K2` |
| 7 | `hFM` D2 `LemDecCalELipG_FlowMod` | `∃ c` before `(sz, 𝔠, z)`, `Flow →` | `lemDecCalELipG_flowMod_band` (`c = 1`) | U4-BA (`seqHflowBA`, `contGood (sz.withLam 0)`) |
| 8 | `hmn` `‖m‖ ≤ 1` | `0 < κ → Flow →` | `norm_mE` | `BAm_norm_le_one` |
| 9 | `hKs` D3 (text of `NQEndFlowGen_KLipFam` at `k = 2`, inline) | `0 < κ → 0 < ε → Flow →`, `∀ t ≤ T0` | `duhamelI_Ks_band` (`DuhamelI2.lean:1513`) | `baKsol_two` / U3-BA twin |
| 10 | `hLF` `StepDecompGen_LoopForm` | `0 < κ → Flow →` | `stepDecompGen_loopForm_band` | U2-BA carrier facts (`baStep2Mat_loopForm` is not on `main`; `GridGoodBA` takes it as `hL`) |
| 11 | `hGrid` (A10) `Step2EventsGen_Grid` | unguarded | `Step2EventsGen_bandGrid` | `Step2EventsGenTw_baGrid` |
| 12 | `hHerm` (A11) Hermitian walk | unguarded | `pathH_isHermitian` | `baStep2Mat_Hpath_herm` |
Not a premise: `hSr` (A7, `Σ_b ‖S_{ab}‖ ≤ 1`): the Duhamel proofs do not read it (no `sum_norm_SB_row` in the three files).  Pinned `∃`: `𝔠d` (inside `STIngR5gL`), `C₀` (`hGM`), `c` (`hFM`); none after `(sz, z)`.  `hE` of the engines is the body of `STEtermsMidConclgL` written out (as the band engine did), so the registry scan sees `PrecL` only.
**D1-D3, ports, layout, imports**
* D1 = target 6: text of the check's `T2496_DuhamelForm` (`rep/auditcheck`: exit 0).  Port of `BA/Step5IIIWalk.lean:304-671` (368 lines; last commit of the file `git log -1`: f2af0245, 2026-10-13 01:00 UTC) into `DuhamelI2.lean:53-422` (370 lines); after the rename `Step5IIIWalk_` -> `duhamelIG_` it differs in 16 lines (`variable {d}`, `private`, `_root_.RBM.BA.`, `end Duhamel`).  RBM1D/RBM2D: not touched, no port.
* D2 = `LemDecCalELipG_FlowMod` (U4s3a, unchanged); the engines take `Hm`, `G`, `c` from it for the lift (`LemDecCalELip_LK2gL`, `duhamelIIG_holder`); `hGrid` supplies its own `Hm'` for the grid events (no coupling).  D3 = `hKs`, used by `LK2gL`; A8 (a) `lemDecCalELipG_Kn` from `hK2` at `s := 0` and `hBd` (no inline premise (b)).
* Layout: `DuhamelI` 1087 = §1-§2 `Φ` (unchanged), §3-§4 carrier kernel (`duhamelIG_Phi_STprof/_lam`, `_Ugen_le`, `_mart_Ugen`), §6 numerics + `duhamelIG_apriori`, §7 counting helpers, §8 `duhamelIG_lift`.  `DuhamelI2` 1699 = D1, moved model-free §5 helpers, drift/martingale/`duhamelIG_path_rem` (§5), `duhamelIG_section` (private), engine, pin, band discharges, instances.  `DuhamelII` 968.
* Imports: DuhamelI `+Chain.Step5KerGen, Chain.IniTermIIGen`; DuhamelI2 (new) `DuhamelI, PfStep5Grid, Chain.GridRepTailGen2`; DuhamelII `DuhamelI2` in place of `DuhamelI`.  No `RBM3D.BA.*`, no `NQEndFlowGen`.  Reverse cone: 4 modules / 850 lines (`MainIndHolds`, `MainIndOut`, `Main.BandTerminal`, `Probe.T2496Pins`; chain `DuhamelI <- DuhamelI2 <- DuhamelII`).  `DuhamelI2` is imported by `DuhamelII` only; `RBM3D.lean` is not edited (the hub adds `import RBM3D.Induction.DuhamelI2`).
* `open private`: DuhamelI2 <- DuhamelI `duhamelI_zdistInf_sub_comm, _tailW_eq, _cardK, _measure_le`; <- Step5KerGen `Step5KerGen_cmp_pos` (unused); <- PfStep5Grid the 13 `pfStep5Grid_*` of `Step5IIIWalk.lean:56-58`.  DuhamelII <- DuhamelI `_tailW_eq, _cardK, _measure_le`; <- DuhamelI2 `duhamelI_absorb, duhamelIG_{prec_congr,whp_sec,ELKLK_meas,ELKLK_eq,pair,theta_rows}`; <- `emn2Exp2_exists_CR`, `lemDecCalELipG_Ks`, `lemDecCalELipG_absorb`.  DuhamelI <- Step5KerGen `Step5KerGen_cmp_pos`.
* UBA-C1 as used: R1 only in `duhamelIG_Phi_STprof` (inside `step5KerGen_profile_holds`) and the guard (g) `duhamelIG_cmp_pos'` (4 lines, private); `gK` occurs in `hKer` and as a parameter of the pins; no `withLam`, `lam0`, no second comparison; C1 scan below.
* Registry (`Test/Axioms.lean:209-210`): owner texts of `STDuhamelIgL`, `STDuhamelIIgL` -> `generic: stDuhamelIgL_of / stDuhamelIIgL_of (T2496, in place, ...); BA: U4-BA (b)`; new `owedProps` lines: 0 (the full build above passes the scan).
```
$ python3 $S/rep/c1scan.py      # C1/X1-C1 regex over the statements of the 95 theorem declarations of the three files, private ones included
DuhamelI2.lean duhamelI_Ks_band [STFlow, STflowE, lemT] -> band discharge | duhamelI_band_gL [STFlow, STflowE, lemT, seqP] -> band tuple | stDuhamelConcl_engine [Prec, STFlow, STflowE, etaT, lemT] -> band corollary (frozen text)
DuhamelII.lean duhamelII_band_gL [STFlow, STflowE, lemT, seqP] -> band tuple | stDuhamelConcl_engineQ1 [Prec, STFlow, STflowE, etaT, lemT] -> band corollary (frozen text);   generic statements with hits: 0
$ bash $S/rep/greps.sh   # X1-C4 (new defs of the pinned names): 0 | STGridRepNgL: 0 0 0 | sorry|admit|axiom|native_decide: 0 | import RBM3D.BA / NQEndFlowGen: 0 | new def lines: private `duhamelIG_Uc`, `duhamelIG_Tc` (D1 port) only
   U5S-C3 `grep -nE '∀ \(sz : Sizes d\)'`: 47 hits = the carrier-tuple binders of the three pins/engines (`Flow`, `mkM`, `T0`, `E`, `gK`) and the premise rows 3, 7-12 of the table (rows 3, 8, 9, 10 guarded `0 < κ → Flow … →`, row 7 `Flow … →`, rows 11, 12 unguarded), plus `duhamelIG_Phi_STprof/_lam` (DuhamelI:357, 464), `duhamelIG_section`, `duhamelII_prof_avg` (DuhamelII:129)
$ bash $S/rep/clash.sh   # new public names (16) + `DuhamelI2` against 514 local refs (main + t/* branches except t/T2496b), `git grep -w -F`
names: 17; refs scanned: 514; total hits: 0
```

**Narrative.**
* Result: targets 6-10 are written in place in `DuhamelI`, the new `DuhamelI2`, `DuhamelII` and committed on `t/T2496b` (038fbef5); the full build passes (the readers `MainIndHolds`, `MainIndOut`, `BandTerminal` compile unchanged).
* Target 6 is the port of the BA block (370 lines); targets 8, 9 are the pins `stDuhamelIgL_of`, `stDuhamelIIgL_of` over `(law, Flow, mkM, T0)` with the premises of the table; both read the engines `stDuhamelConclgL_engine` (`Q = ∅`) and `stDuhamelConclgL_engineQ1` (`Q = {0}`).
* Target 7: the model kernel is replaced by the carrier kernel `Step2Gen_thetaKer`: `𝒰_{v,w} = 1 + (w-v) θ_w` (`Step5KerGen_UN_decomp`) through `Φ`, the profile bound `duhamelIG_Phi_STprof` from `step5KerGen_profile_holds` (R1 inside), the martingale term by Abel summation, `duhamelIG_path_rem` from D1 and `STGridMartAtgL` only (no `STGridRepNgL`).
* The section (`duhamelIG_section`, `duhamelIIG_section`, private) transfers the events E1-E4 from the model to the grid walk with `Step2EventsGen_grid_whp_zero/_of_sections` (F9 law identity of `hGrid`), E5-E6 from `hGM`, applies `duhamelIG_path_rem` at the labels (`Q^{(1)}`: also at `(c, a₂)` with `duhamelII_prof_avg`) and reads the endpoint through the law identity at `k = K_n`; the Hermitian walk `hHerm` gives the a priori bound `duhamelIG_apriori` (`norm_loopFine_crudeNg`).
* The lift `duhamelIG_lift` is the band net lift at a law `μ` and an event `G`; its Hölder input is `LemDecCalELip_LK2gL` (target 1, D2, D3) for `Q = ∅` and the new `duhamelIIG_holder` (`LemDecCalELip_LK_subg` at `a` and `(c, a₂)`, constant `N^{11+c}`) for `Q^{(1)}`.
* Band: `duhamelI_band_gL`, `duhamelII_band_gL` apply the pins to `(seqP, STFlow, bandStep2Mat ∘ STflowE, lemT)` with `gK = lam`; `stDuhamelI_holds`, `stDuhamelII_holds` are corollaries through `STDuhamelI_iff_gL`, `STDuhamelII_iff_gL`; `stDuhamelConcl_engine`, `_engineQ1` (old text, `rep/frozen.lean`) through `bandFM_STDuhamelConcl`.
* Deviations from the ticket text, for the auditor: (i) `hSr` (A7) is not a premise of 8, 9 (unused); (ii) the lift (§8) stays in `DuhamelI` (model-free, `DuhamelI2` would be near the stop size otherwise: 1,699 lines are already used); D1 and the pathwise bound are in `DuhamelI2` as Amend 2 item 5 says; (iii) `hKs` has no `3 ≤ d →` and no `∀ k, 2 ≤ k` (the `k = 2` text; `d ≥ 3` is a premise of the pins).
* Limits: BA owners of `hKer`, `hFM` are U4-BA; `hKs`'s BA twin (`baKsol_two`) and `hLF`'s (U2-BA) are not proved here.  Pieces of the previous round's unverified scratch draft (`r2/all.lean`: the D1 block, `duhamelIG_Phi_STprof`, `_Ugen_le`, `_mart_Ugen`, the drift and martingale terms, `duhamelIG_path_rem`) were copied into the files; they count only as far as `lake build` of the files compiled them.

## (c) Verified Mathlib names
Used and compiling in the new text (not in the replaced band text): `smul_right_injective`, `add_left_cancel`, `sq_le_sq₀`, `lt_trichotomy`, `Finset.sum_const_zero`, `add_neg_cancel`, `norm_zero`, `norm_le_insert'`, `abs_of_nonneg`, `Real.norm_eq_abs`, `Complex.norm_real`, `Finset.measurable_sum`, `measurableSet_lt`, `Nat.le_ceil`.  Names verified absent: none searched (`baStep2Mat_loopForm` is a project name, absent from `main`: `grep -rn` over `RBM3D`).

## (d) Open issues and paper-delta candidates
1. **Premise `hSr` (A7) dropped** from targets 8, 9 (the stop report's list had it; Amend 2 does not require it).  If the dispatcher wants the BA reading to carry it, it can be added without touching a proof.
2. **Layout** (see the narrative): the lift and the counting helpers (`duhamelI_card_le`, `_W_le_size`, `_cardK`, `_measure_le`) sit in `DuhamelI` instead of `DuhamelI2`; the auditor may rule.
3. **Public band declarations removed** (no reader outside the three files, `grep` above): `duhamelI_Phi_STprof`, `_Ugen_le`, `_mart_Ugen`, `_path`, `_imag`, `_apriori`, `_lift`, `duhamelII_path_rem`; replaced by the `duhamelIG_*` generics (Lean-only).  `DuhamelII` no longer carries its own copy of the pathwise remainder.
4. **Probe** `RBM3D/Probe/T2496Pins.lean` stays on the branch, stale, outside the default build, never merged.
5. **Instances**: target 6, 8, 9 and the kernel facts have stand-alone instances; the helper theorems of the proof path (`duhamelIG_apriori`, `_lift`, `_mart_Ugen`, `_path_rem`, `duhamelIIG_holder`) have none.  The BA readings of the heads typecheck (`T2496-check.lean`, part of `rep/auditcheck.lean`, exit 0).
6. **Paper-delta candidates** (Lean-only): **T2496e** (Amend 2 item 8): the law identity `(5.1)` of the grid walk and the Hermitian walk enter the pins as the carrier premises `hGrid` (F9) and `hHerm`; no change of a paper statement.  **T2496f**: `hE` of the engines is the body of `STEtermsMidConclgL` written out (registry scan), and the carrier moduli keep the exponent `N^c` of D2 (`duhamelIIG_holder`: `N^{11+c}` against the band `N^{12}`); the band `c = 1` recovers the old constants.
7. `RBM3D.lean` and `docs/` untouched by the 1b; no push, no merge.
