Auditor model: claude-opus-5-5

# T2496b audit, round 1 (U4s3b: targets 6-10; Amend 1 and Amend 2 apply)
Date (`date -u`): Tue Oct 13 17:50:15 UTC 2026. Branch `t/T2496b` @ 038fbef5; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2496b-audit1` (detached).
Scratch: `$A` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2496b/audit`.

## 0. Diff, layering, hygiene
```
$ git diff --numstat main...t/T2496b
337 1244 RBM3D/Induction/DuhamelI.lean | 1699 0 RBM3D/Induction/DuhamelI2.lean | 420 428 RBM3D/Induction/DuhamelII.lean
375 0 RBM3D/Probe/T2496Pins.lean (t/T2496 probe, never merged) | 2 2 RBM3D/Test/Axioms.lean
$ git diff --name-only main...t/T2496b -- RBM3D/Chain RBM3D/BA RBM3D/Path RBM3D/Induction/{LemDecCalEPrec,PfStep5,PfStep5Alg,PfStep5Grid,NQEndFlowLift,QtXiRoundLift,QtNonzeroFlowLift,ExpIntIQ,ExpWardI,MainIndHolds,MainIndOut,Step5Pins}.lean RBM3D.lean | wc -l
0
$ git merge-base main t/T2496b; git diff --stat <mb> main -- '*.lean'      # no Lean on main since the merge base
7b9e0c4c...   (empty)
$ git diff main...t/T2496b -- RBM3D/Induction RBM3D/Test | grep -E "^[-+](private |noncomputable )*(def|abbrev|structure|class|instance|axiom) "
+private def duhamelIG_Uc   +private def duhamelIG_Tc          # no band def removed or changed
$ import changes:  DuhamelI  -PfStep5Grid +Chain.Step5KerGen +Chain.IniTermIIGen | DuhamelI2 (new) DuhamelI, PfStep5Grid, Chain.GridRepTailGen2 (Amend 2 (4))
                   DuhamelII -DuhamelI +DuhamelI2 | importers of DuhamelI2: DuhamelII only | `import RBM3D.BA`/NQEndFlowGen: 0
$ git grep -nE "\b(sorry|admit|native_decide)\b|^axiom " t/T2496b -- RBM3D/Induction/Duhamel{I,I2,II}.lean | wc -l
0
$ wc -l Duhamel{I,I2,II}.lean      ->   1087  1699  968   (stop size 2,000; 1,800 rule)
```
Registry diff (`Test/Axioms.lean:209-210`): only the owner text of `STDuhamelIgL`, `STDuhamelIIgL` -> "generic: `stDuhamelIgL_of` / `stDuhamelIIgL_of` (T2496, in place, ...); BA: U4-BA (b)", as the ticket's Registry line. No `owedProps` line added.

Public band names removed by the row, and their readers outside the three files (branch, then every other `t/*` branch with `git grep -lw`):
```
duhamelI_apriori / _imag / _lift / _mart_Ugen / _path / _Phi_STprof / _Ugen_le, duhamelII_path_rem : 0 files ; other t/* branches: 0
```

## 1. Build and axioms (audit worktree)
```
$ lake build      # Tue Oct 13 17:44:51 -> 17:47:22 UTC
info: RBM3D.lean:602:0: axiom audit: 14908 theorems, 4618 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4372 jobs).
$ lake build RBM3D.Induction.DuhamelI RBM3D.Induction.DuhamelI2 RBM3D.Induction.DuhamelII | grep -E "error|sorry|Build completed"
Build completed successfully (3943 jobs).
```
The full build compiles every band reader unchanged (`MainIndHolds`, `MainIndOut`, `Main.BandTerminal` through `DuhamelII` -> `DuhamelI2`), H279 (3). `RBM3D.lean` is not edited; `DuhamelI2` is in the closure through `DuhamelII`.
```
$ lake env lean $A/audit.lean      # = docs/tickets/checks/T2496-check.lean verbatim + auditor examples A1-A6 + #print axioms; exit 0, 0 error lines
$ grep "depends on axioms" $A/audit.out      (14 lines, all "[propext, Classical.choice, Quot.sound]")
RBM.BA.duhamelIG_duhamel, RBM.BA.stDuhamelIgL_of, RBM.BA.stDuhamelIIgL_of, RBM.BA.stDuhamelConclgL_engine, RBM.BA.stDuhamelConclgL_engineQ1,
duhamelI_band_gL, duhamelII_band_gL, stDuhamelI_holds, stDuhamelII_holds, stDuhamelConcl_engine, stDuhamelConcl_engineQ1,
duhamelIG_path_rem, duhamelIG_Phi_lam, duhamelIG_Ugen_le
```
The check file itself (Part 3: `#check` of the 3 frozen and the outside-read band names) compiles on the branch.

## 2. Statements against the pins (compiled; `$A/audit.lean`)
```lean
-- A1 target 6 = D1 (check `T2496_DuhamelForm`, binding text of the 1a-audit)
example : ∀ {d} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), GridRepTailGen_Ker C n → T2496_DuhamelForm C n :=
  fun _ _ h => duhamelIG_duhamel h
-- A2 targets 8, 9 conclude the binding heads; hGrid, hHerm typed with the exact Amend 2 text (A10, A11)
example (d) (law) (Flow) (mkM) (T0 E gK) (hF) (hKer) (hGR) (hGM) (hBd) (hK2) (hFM) (hmn) (hKs) (hLF)
    (hGrid : ∀ sz z, Step2EventsGen_Grid (mkM sz z) (law sz))
    (hHerm : ∀ sz z s t K n k ω, ((mkM sz z).Hpath s t K n k ω).IsHermitian) :=
  (⟨stDuhamelIgL_of .. hGrid hHerm, stDuhamelIIgL_of .. hGrid hHerm⟩ :
    T2496_DuhamelIHead d law Flow mkM T0 ∧ T2496_DuhamelIIHead d law Flow mkM T0)
-- A4 the check's D3 shape (∀ C t) implies `hKs` (guarded, t ≤ T0): `fun sz _ _ _ _ z _ _ _ t _ => hD3 (mkM sz z).toFlowFM t`
-- A5 band readings (check example) : fun d hd => ⟨duhamelI_band_gL d hd, duhamelII_band_gL d hd⟩
-- A6 BA discharges of A10/A11 named in Amend 2, at every (sz, z):
--   Step2EventsGenTw_baGrid sz (BAflowLam0 sz z) (BAflowEs sz z) ; baStep2Mat_Hpath_herm _ _ _ s t K n k ω
```
Result: all compile (exit 0).

Premise list of targets 8, 9 (identical signatures, `T2496b-prove.md:108-112`) against the ticket table + Amend 1 + Amend 2:
| premise | ticket row | guard as written | verdict |
|---|---|---|---|
| `hF` `Step5CasesGen_FlowFacts` | 1 | built in | = row |
| `hKer` `IniTermGen_KerFacts` at `gK` | 2 (R1 inside) | built in | = row |
| `hGR` `∀ n, GridRepTailGen_Ker` | 3 | `0 < κ → Flow →` | = row |
| `hGM` `STGridMartgL` (no `STGridRepNgL`) | 4 | pin, `∃ C₀` inside | = row, TN-C4 |
| `hBd` `STBdatagL` | 6 | as merged | = row |
| `hK2` `Step2IterGen_K2` | 7 (A9), Amend 2 (3) | as merged | = amend |
| `hFM` `LemDecCalELipG_FlowMod` | 8 (D2, U4s3a merged) | `∃ c` after `κ ε 𝔡`, before `(sz, 𝔠, z)` | = check's D2 family form |
| `hmn` `‖m n‖ ≤ 1` | 9 | `0 < κ → Flow →` | text = check's spectral example |
| `hKs` D3 at `k = 2` | 9 | `0 < κ → 0 < ε → Flow →`, `∀ t ≤ T0` | weaker than check D3 (A4) |
| `hLF` `StepDecompGen_LoopForm` | 10 | `0 < κ → Flow →` | = row |
| `hGrid` | A10 | unguarded | = Amend 2 text (A2) |
| `hHerm` | A11 | unguarded | = Amend 2 text (A2) |
Not present: A7 `hSr`, row 10's `Step34Gen_LCompat/KCompat`, row 5, row 7's old `STK2decaygL'`/`STNewKLKLgL'`/glue (removed by A9). Absent premises make the statements stronger; no unlisted premise is added. Extra explicit parameters `E` (read by `hLF`) and `gK` (read by `hKer`) only. Pinned `∃`: none after `(sz, z)`. No `3 ≤ d` premise beyond the `hd` inside `STIngR5gL`.

Conclusion heads (`Chain/Step5Gen.lean:236-245`, merged): `STDuhamelIgL` / `STDuhamelIIgL` = `STIngR5gL d STReg5I/II law Flow mk T0 (… STEtermsMidConclgL → STDuhamelConclgL …)`; no field hides a hypothesis. Order of quantifiers is that of the merged pin.

C1 / X1-C1 regex over the statements of every public theorem of the three files (`python3 -I $A/c1.py`):
```
generic statements (duhamelIG_duhamel, duhamelIG_Phi_STprof/_Phi_lam/_apriori/_lift, duhamelIG_path_rem, duhamelIIG_holder,
  stDuhamelConclgL_engine(Q1), stDuhamelIgL_of, stDuhamelIIgL_of): 0 hits
  (duhamelIG_Ugen_le, duhamelIG_mart_Ugen: hit `Ugen` = the declaration name / docstring; the statements use Step2Gen_UN, Step2Gen_thetaKer)
band: duhamelI_Ks_band [STFlow STflowE lemT] | duhamelI_band_gL, duhamelII_band_gL [+ seqP] | stDuhamelConcl_engine(Q1) [Prec STFlow STflowE etaT lemT] (frozen text)
```

## 3. G1: frozen and band corollaries (script diff of the statement text, main vs branch, `python3 -I $A/stmt.py`)
```
stDuhamelConcl_engine      main:DuhamelI  -> DuhamelI2: IDENTICAL (1270 chars)
stDuhamelI_holds           main:DuhamelI  -> DuhamelI2: IDENTICAL (47 chars)
stDuhamelConcl_engineQ1    main:DuhamelII -> DuhamelII: IDENTICAL (1161 chars)
stDuhamelII_holds          main:DuhamelII -> DuhamelII: IDENTICAL (49 chars)
inst_duhamelI_proved       main:DuhamelI  -> DuhamelI2: IDENTICAL (195 chars)
inst_duhamelII_proved      main:DuhamelII -> DuhamelII: IDENTICAL (240 chars)
```
Namespace kept (`RBM.Gauss.Sizes`, `RBM.Gauss.Step5Inst`); they are now proved through `STDuhamelI_iff_gL`, `STDuhamelII_iff_gL`, `bandFM_STDuhamelConcl` from the generic results (Amend 2 (6)).

## 4. Compiled nonempty instances (in the files, built above)
| target | instance | data | deterministic hypotheses |
|---|---|---|---|
| 6 `duhamelIG_duhamel` | `DuhamelI2.lean:1647` | `d = 3`, band kernel `bandStep2Mat sz0 (1/2)`, `n = 0` (`L = 4`, `W = 32`), `σ = (+,-)`, `k = 3`, `Δ = 1/16`, `M = 2`, `A_j ≡ 1 + j/10`, `Mart_j ≡ j/10`, `F_i = -Θ A_i` | all discharged; `GridRepTailGen_Ker` by `gridRepTailGen_ker_band` |
| 8 `stDuhamelIgL_of` | `DuhamelI2.lean:1665` | through `duhamelI_band_gL 3` (all 12 premises discharged by merged band results), read at `(szB, zB, 7/8, 15/16)`, any `C_d > 0` | `STEtermsMidConcl` stays inside the conclusion (another gate's pin) |
| 9 `stDuhamelIIgL_of` | `DuhamelII.lean:962` | through `duhamelII_band_gL 3`, `(szB, zB, 15/16, 31/32)` | same |
| 7 (kernel part) | `DuhamelI2.lean:1673`, `:1692` | `duhamelIG_Phi_lam`, `duhamelIG_Ugen_le` at `(sz0, z0)`, `n = 0`, `w = 1/2` | discharged |
| 10 band corollaries | `DuhamelI2.lean:1608, 1614, 1622`; `DuhamelII.lean:923, 931, 940, 948` | `szB`/`zB`, cases (i), (ii) | `hE` is `STEtermsMidConcl` (other gate) |
None is degenerate: no `N = 0`, no empty index, no collapsed window, no `False` premise.

## 5. No vacuity, no hidden hypothesis, no cycle
- The 12 premises hold together at the band tuple (`duhamelI_band_gL`, `duhamelII_band_gL` compile and print the standard axioms), so the targets are not vacuous.
- A10/A11 BA discharges compile (A6). Dependencies (`Step2IterGen_K2`, `LemDecCalELipG_FlowMod`, `GridRepTailGen2`, `STGridMartgL`, `STBdatagL`) are merged on `main`. The build passes, so there is no import cycle.
- No new external hypothesis. Every premise is a carrier fact with a compiled band discharge; BA owners as in the ticket table.

## 6. Paper deltas
- `T2496e` (Amend 2 (8): the law identity of the grid walk and the Hermitian walk enter as the carrier premises `hGrid`, `hHerm`) is already in `docs/paper-deltas.md:1760` (numbered at merge).
- `T2496f` (the engines' `hE` written as the body of `STEtermsMidConclgL`; carrier modulus `N^{11+c}` against the band `N^{12}`) is proposed in `T2496b-prove.md` (d) 6.
- The removal of the 8 unread public band helpers is Lean-only, listed in (d) 3.
No Lean/paper statement difference is uncovered.

## 7. Verdicts
| target | verdict |
|---|---|
| 6 `duhamelIG_duhamel` (D1) | PASS |
| 7 `DuhamelI` §1-§8 over the carrier (`duhamelIG_*`; `STGridMartgL` only; `duhamelIG_apriori` through `hHerm`) | PASS |
| 8 `stDuhamelIgL_of` (+ `stDuhamelConclgL_engine`) | PASS |
| 9 `stDuhamelIIgL_of` (+ `stDuhamelConclgL_engineQ1`) | PASS |
| 10 band corollaries and instances; registry text | PASS |
**Overall: PASS.** No dispatcher sign-off needed.

## 8. Observations (no RETURN)
1. A7 `hSr` (Amend 1 (2)) and row 10's `Step34Gen_LCompat/KCompat` are not premises of 8, 9 because the proofs do not read them. This makes the statements stronger (prove (d) 1).
2. The lift and the counting helpers stay in `DuhamelI`, while D1 and the pathwise bound are in `DuhamelI2`. Amend 2 (5) asks only for the latter; the sizes are within the 1,800 rule.
3. `RBM3D/Probe/T2496Pins.lean` is in `git diff main...t/T2496b` (stacked from `t/T2496`). It is never merged, so the hub brings in only the three Duhamel files and `Test/Axioms.lean`.
4. The hub must add `import RBM3D.Induction.DuhamelI2` after the last `import` line of `RBM3D.lean` (rule (A) 4).
5. Some target-7 public helpers (`duhamelIG_apriori`, `_lift`, `_mart_Ugen`, `_path_rem`, `duhamelIIG_holder`) have no stand-alone `example`. They are not endpoint theorems; they are applied with discharged hypotheses inside the compiled band instances of targets 8 and 9.
6. Unpinned public helpers in `DuhamelI2` use the prefix `duhamelIG_`/`duhamelI_` (the `DuhamelI` stem), not `duhamelI2_`. There are no clashes (the full build passes).
7. The calibration figure (moved = 783, landing 1,675; with U4s3a 3,086 < 3,540) is the prover's script. The auditor did not recompute the moved-line count.
