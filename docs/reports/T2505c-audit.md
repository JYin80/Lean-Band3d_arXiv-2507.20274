Auditor model: claude-opus-5-5

# T2505c (U3s4c, T2505 row c) audit, round 1 — written Wed Oct 14 13:28:39 UTC 2026 (`date -u`)
Branch `t/T2505c` @ 0d2b65e4 (base b610fbdb); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2505c-audit1` (detached, clean). Scratch files are in the scratchpad `T2505c/` (`audit.lean`, `stmt.py`); none is committed.
Targets 10–15 (ticket `docs/tickets/T2505.md:43-49`). Prove report `docs/reports/T2505c-prove.md`.

## 1. Diff, layering, hygiene
```
$ git diff --name-only main...t/T2505c
RBM3D.lean
RBM3D/Chain/QtNonzeroBootGen.lean
RBM3D/Chain/QtNonzeroFlowGen.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2505c --stat -- RBM3D/Induction RBM3D/BA RBM3D/Graph | wc -l
       0
$ grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide' RBM3D/Chain/QtNonzero{Flow,Boot}Gen.lean | wc -l ; grep -nE '^import' RBM3D/Chain/QtNonzero{Flow,Boot}Gen.lean | grep -E 'RBM3D\.BA|Step2Kern' | wc -l
       0
       0
$ grep -rlE 'import RBM3D\.Chain\.QtNonzero(Flow|Boot)Gen' RBM3D RBM3D.lean
RBM3D/Chain/QtNonzeroBootGen.lean
RBM3D.lean
$ wc -l RBM3D/Chain/QtNonzero{Flow,Boot}Gen.lean
    1145 RBM3D/Chain/QtNonzeroFlowGen.lean
     780 RBM3D/Chain/QtNonzeroBootGen.lean
    1925 total
```
Every touched file is a sole writable file of row c. No band, BA or merged `Chain` file is touched. Each file is under 2,000 lines and the row is under the 1,950 cap.
Registry (`git diff main...t/T2505c -- RBM3D.lean RBM3D/Test/Axioms.lean`, `+`/`-` lines, cut): two `+import` lines (`QtNonzeroFlowGen`, `QtNonzeroBootGen`); `:121` "…; no generic proof" → "…; generic: `STXiRoundgL'` (T2505, `Chain/QtBootGen`)"; `:214` "…conclude it (proofs: U3s3, U3s4)" → "…conclude it: `stOeqQtgL'_of` (T2505a, `Chain/QtXiRoundLiftGen`, from U3s3's `stOeqQtRoundPTgL''_of`) and `stOeqQtNZgL'_of` (T2505c, `Chain/QtNonzeroBootGen`)". These are the ticket's row-c texts (`T2505.md:69`).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Chain.QtNonzeroFlowGen RBM3D.Chain.QtNonzeroBootGen 2>&1 | tail -1 ; echo exit $?
Build completed successfully (3953 jobs).
exit 0
$ grep -c '^error' build.txt ; grep -E '^warning: RBM3D/Chain/QtNonzero(Flow|Boot)Gen' build.txt | grep -vc 'exceeds the 100'
0
0
```
The only warnings in the two new files are long-line warnings (12 + 8).
`lake env lean audit.lean` (scratch file importing `RBM3D.Chain.QtNonzeroBootGen`), the `#print axioms` lines, verbatim:
```
'RBM.BA.STNZConclPTgL''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqNZPTgL''_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqNZgL''_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stXiRoundNZgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqQtNZgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroFlowGenCheck.stOeqNZPTgL''_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroFlowGenCheck.stOeqNZgL''_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroBootGenCheck.stXiRoundNZgL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroBootGenCheck.stOeqQtNZgL'_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqNZPT''_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqNZ''_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqQtNZ'_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroFlowGenCheck.inst_OeqNZPTgL''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroFlowGenCheck.inst_OeqNZgL''' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroBootGenCheck.inst_XiRoundNZgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QtNonzeroBootGenCheck.inst_OeqQtNZgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2505-check.lean ; echo exit $?   (in the audit worktree)
exit 0          (0 error lines)
```

## 3. Statements against the pins (script)
`audit.lean` copies the check's Part-2 texts (`T2505-check.lean:83-140`, `:154-174`) into the scratch namespace `RBM.BA.AuditT2505c`, then:
```
example : @STNZConclPTgL'' = @T2505_NZConclPTgL'' := rfl      -- ok
example : @STOeqNZPTgL'' = @T2505_OeqNZPTgL'' := rfl          -- ok
example : @STNZConclgL'' = @T2505_NZConclgL'' := rfl          -- ok
example : @STOeqNZgL'' = @T2505_OeqNZgL'' := rfl              -- ok
example : @STXiRoundgL' = @T2505_XiRoundgL' := rfl            -- ok (row a, read by target 13)
example : @QtNZGen_KerNZ = @T2505_KerNZ := rfl                -- ok (row b, D1)
example : @QtNZGen_KerNZFam = @T2505_KerNZFam := rfl          -- ok (∃ C5 after (k, κ, 𝔡), before (sz, z))
example : @QtBootGen_FlowModFam = @T2505_FlowModFam := rfl    -- ok (family row 16, ∃ c before (sz, z))
example : @STNZConclPTgL'' = @T2505_NZConclgL'' := rfl        -- control
audit.lean:97:51: error: Type mismatch            <- the control only; no other error in the file
```
Conclusion heads, from a `#concl` meta command (`forallTelescope` on the constant's type), verbatim:
```
RBM.BA.stOeqNZPTgL''_of: 34 binders; conclusion head RBM.BA.STOeqNZPTgL''; args after d,law,Flow,mk,T0? 5
RBM.BA.stOeqNZgL''_of: 36 binders; conclusion head RBM.BA.STOeqNZgL''; args after d,law,Flow,mk,T0? 5
RBM.BA.stXiRoundNZgL_of: 36 binders; conclusion head RBM.BA.STIngRgL; args after d,law,Flow,mk,T0? 7
RBM.BA.stOeqQtNZgL'_of: 36 binders; conclusion head RBM.BA.STOeqQtNZgL'; args after d,law,Flow,mk,T0? 5
```
Binder counts are of the elaborated type (`forallTelescope`); the source text of each conclusion is `… d law Flow (fun sz z => (mkM sz z).toFlowFM) T0`. Target 13 concludes `STIngRgL d STCaseII … (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t)` (`QtNonzeroBootGen.lean:488-490`). By the rfl lines, targets 11 and 12 conclude `T2505_OeqNZPTgL''` and `T2505_OeqNZgL''`, and target 14 concludes the merged `STOeqQtNZgL'` under its own name.

The premises are checked against the family-premise table (`T2505.md:52-60`) by a script diff of the signature of `stOeqNZPTgL''_of` against the merged `stOeqQtRoundPTgL''_of` (T2498 rows 1–13), with comment lines dropped:
```
46,48c46,48
<     (hKerFam : NQGoodGen_KerNALFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
<     (hR1 : … 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
<       1 ≤ Aof κ ∧ ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
---
>     (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
>     (hKerFam : QtNZGen_KerNZFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK Aof)
>     (hR1 : … 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
50,55c50,51  (removed: hEK4 : QProxyG_KerEK4Fam …, hTh : … Step5KerGen_ThDecay …; hB45 moved up)
```
- Rows 1–7, 9, 10–12 are T2498's texts unchanged. D1 (row 14) replaces the NAL kernel class. `hEK4` and `hTh` are dropped, as the ticket says ("no D1 EK-4, no NAL kernel, no `hTh`").
- R1 is only the single inequality `lam² ≤ Aof κ gK²`. This is weaker than T2498's conjunction, so the theorem is more general. It is guarded by `0 < κ → Flow`.
- Targets 12–14 add exactly rows 15 (`NQEndFlowGen_KLipFam`, merged) and 16 (`QtBootGen_FlowModFam` = `T2505_FlowModFam`, shown by rfl).
- No `∀ n` drift or hierarchy premise: `hExp`, `hKL`, `hKT`, `hU` are `∀ᶠ n`.
- Every pinned `∃` sits before `(sz, z)`: `C5` and `c` by the rfl lines, `C₆` inside `B45Gen_Facts`.

Hypothesis-rule scan (`python3 -I stmt.py`, ticket regex C1/X1-C1 over each public statement, `KLloopOf` excepted):
```
def STNZConclPTgL'' [QtNonzeroFlowGen.lean:72-72] X1-C1 hits: []      def STOeqNZPTgL'' [QtNonzeroFlowGen.lean:88-90] X1-C1 hits: []
def STNZConclgL'' [QtNonzeroFlowGen.lean:94-94] X1-C1 hits: []        def STOeqNZgL'' [QtNonzeroFlowGen.lean:110-112] X1-C1 hits: []
theorem stOeqNZPTgL''_of [QtNonzeroFlowGen.lean:523-577] X1-C1 hits: []
theorem stOeqNZgL''_of [QtNonzeroFlowGen.lean:846-902] X1-C1 hits: []
theorem stXiRoundNZgL_of [QtNonzeroBootGen.lean:433-490] X1-C1 hits: []
theorem stOeqQtNZgL'_of [QtNonzeroBootGen.lean:507-563] X1-C1 hits: []
$ grep -cE '(def|abbrev|structure) (STXiBootgL'|…|SubGaussStopNg)\b' (X1-C4) ; grep -cE 'STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds|withLam'
QtNonzeroBootGen.lean:0 QtNonzeroFlowGen.lean:0 ; QtNonzeroBootGen.lean:0 QtNonzeroFlowGen.lean:0
```
The texts of the four `def` bodies are covered by the rfl equalities above. The band names occur only in the band bridges and re-derivations, as the ticket allows.

## 4. Vacuity, hidden hypotheses, cycles
- No hidden field in a public statement: `QtNZFlowGen_Facts` is a `private structure` (`QtNonzeroFlowGen.lean:228`) in no public signature; `B45Gen_Facts` is the merged row-9 class the ticket names.
- Acyclic, merged dependencies (`QtNonzeroBootGen.lean:563-572`): t14 = row a's `stXiBootRgL'_of_round d STCaseII` ∘ t13; t13 → t12 → t11 → row b's `nzGridEndNg`, `gridGoodNgL_of`, `nqLinGoodgL_of`. Band names in the generic sections occur only in docstrings (`QtNonzeroFlowGen.lean:24, 249, 773`; `QtNonzeroBootGen.lean:215, 430`); band facts enter only via model-free `open private` helpers (allowed). Re-derivations go generic → band, every premise discharged by merged band lemmas (`QtNonzeroFlowGen.lean:937-1006`; `QtNonzeroBootGen.lean:589-661`).
- No external input: each family premise has a band discharge (§5); BA discharges are U3-BA (a)/(b), T2501 (ticket decision (4)).

## 5. Compiled nonempty instances (all compile in the §2 build)
Each endpoint theorem is applied with no open hypothesis (`*_band3` = the target with every family row discharged at the band family) at `d = 3`, `szB` (`L = 4`, `W = n + 4`, `lam ≡ 1`), flow `zB` (`z = 1/2 + i/64`, `flow_zB`), window `s ≡ 15/16 < t ≡ 31/32` (not collapsed), `STCaseII` = `szB_caseII`, `(κ, ε, 𝔡) = (1/10, 1/10, 1/10)`, `C_d = 1`, `𝔠 = 1/6`; `STKboundgL`, `STKwardgL`, `conStInd` discharged:
- t11 `inst_OeqNZPTgL''` (`QtNonzeroFlowGen.lean:1043`), t12 `inst_OeqNZgL''` (`:1055`): `∃ 𝔠d, 0 < 𝔠d ∧ 𝔠d ≤ 1/100 ∧ STNZConcl(PT)gL'' (bandFM szB (STflowE zB)) … (15/16) (31/32)`; t13 `inst_XiRoundNZgL` (`QtNonzeroBootGen.lean:699`), t14 `inst_OeqQtNZgL'` (`:711`): same with `STXiRoundgL'` / `STXiBootgL'`.
- t10: index type nonempty at every `n` (`QtNonzeroFlowGen.lean:1119`, `σ = sig3`, `A = {0,1}`), bridges at `d = 3` (`:1133`, `:1136`); t15: band corollaries via `inst_ing` (`:1068`, `:1073`; `QtNonzeroBootGen.lean:753`, `:758`).
Only `hLK : STLKgL … (15/16)` and `hStep2 : STStep2ConclgL …` stay hypotheses: premises of the merged `STIngRgL` pin (other gates' stochastic pins), allowed by CLAUDE.md §4. No `N = 0`, empty index, collapsed window, `False` premise or astronomically large witness.

## 6. Paper deltas
Candidates in the report (`T2505c-prove.md:213-215`): case-(ii) lift mesh `N^{-(6n_+18+2c)}` with factor `2^{n_}`; `𝔠_d = min 𝔠G 𝔠L` with the pinned `∃ C5`, `∃ c`; lower-term constant `κm⁻¹` (band `(√(κ/2))⁻¹`). Family-premise form and D1 are covered by D729 (row a) and D730 (row b) (`docs/paper-deltas.md:1819-1825`). Every Lean/paper difference of targets 10–15 is proposed or recorded.

## 7. Verdicts
| target | verdict |
|---|---|
| 10 `STNZConclPTgL''`, `STOeqNZPTgL''`, `STNZConclgL''`, `STOeqNZgL''` + bridges | PASS (rfl = `T2505_*`) |
| 11 `stOeqNZPTgL''_of` | PASS |
| 12 `stOeqNZgL''_of` | PASS |
| 13 `stXiRoundNZgL_of` | PASS |
| 14 `stOeqQtNZgL'_of` | PASS (concludes merged `STOeqQtNZgL'`) |
| 15 band re-derivations, instances, registry | PASS |
**Ticket verdict: PASS.** No dispatcher sign-off is needed.

## 8. Observations (no RETURN)
- O1. Candidate tags `T2505c`, `T2505d`, `T2505e` (`T2505c-prove.md:213-215`): `T2505c` and `T2505d` collide with row a's tags `T2505a`–`d`, already numbered as D729. Coverage is unaffected; the dispatcher should retag them when numbering (for example `T2505ca`–`cc`).
- O2. Registry `:217` (row a's `STXiRoundgL'` line) still ends "case (ii): T2505 row c". The line is outside row c's binding text; the prover flagged it (Observation 1).
- O3. `import RBM3D.Chain.Step6KitGen` in `QtNonzeroBootGen` is listed by the ticket but not read (prover Observation 2).
- O4. `main` has advanced to 4845a70f (T2506 merge) since the base b610fbdb. `RBM3D.lean` and `Test/Axioms.lean` merge as a union (CONTROL H304 (3)); the hub's full `lake build` at merge covers this.
- O5. The audit worktree's copied cache was stale, so the targeted build re-elaborated merged `Chain` modules. That build had no errors.
