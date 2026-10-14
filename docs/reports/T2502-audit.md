Auditor model: claude-opus-5-5

# T2502 row a audit (round 1) — Wed Oct 14 07:07:59 UTC 2026

Branch `t/T2502` at b0d28f34; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2502-audit1` (detached, b0d28f34). Scratch: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2502/`.
Scope: row a only (targets 1-9: `Chain/Step6Gen.lean`, `Chain/Step6KitGen.lean`, `RBM3D.lean` import lines, row-a registry text).

## 1. Diff scope (sole writable files, no band/merged file)
```
$ git diff --name-only main...t/T2502
RBM3D.lean
RBM3D/Chain/Step6Gen.lean
RBM3D/Chain/Step6KitGen.lean
RBM3D/Test/Axioms.lean
$ git diff --stat main...t/T2502 -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Gauss RBM3D/Evolution   -> (empty)
$ git diff --name-only main...t/T2502 -- RBM3D/Chain | grep -vE "Step6(Kit)?Gen.lean"                    -> (empty)
$ git diff main...t/T2502 -- RBM3D.lean   (2 lines, after the last import, before #assert_rbm_axioms)
+import RBM3D.Chain.Step6Gen
+import RBM3D.Chain.Step6KitGen
```
`Test/Axioms.lean`: +32/-1, owner text of `STExp2U` extended, 13 owed, 15 structural, 1 superseded (`STStep6gL`) lines, all under a "T2502" header.

## 2. Build (forced recompile of the two modules: their `.trace` files deleted in the audit worktree first)
```
$ lake build RBM3D.Chain.Step6Gen RBM3D.Chain.Step6KitGen
⚠ [3859/3860] Built RBM3D.Chain.Step6Gen (16s)
⚠ [3860/3860] Built RBM3D.Chain.Step6KitGen (4.9s)
Build completed successfully (3860 jobs).          ("error" lines in the log: 0; warnings are longLine only)
$ lake build   (whole library, extra evidence; the hub reruns it at merge)
✔ [4381/4384] Built RBM3D.Test.Axioms (4.0s)
ℹ [4383/4384] Built RBM3D (76s)
info: RBM3D.lean:614:0: axiom audit: 15118 theorems, 4687 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 124 premises in the two ledgers; ...
Build completed successfully (4384 jobs).
```
Sizes: `wc -l` 902 + 1,248 = 2,150 (stop line 2,150; each file < 2,000).

## 3. Axioms and hygiene
```
$ ax.lean: one "#print axioms RBM.BA.<n>" per column-0 theorem/def/abbrev of the two files; lake env lean ax.lean
#print lines: 122   exit 0   lines "[propext, Classical.choice, Quot.sound]": 122   other lines: 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " (both files, on t/T2502)   -> 0 hits
$ grep -E "^import RBM3D\.(BA\.|Chain\.Step2Kern)" (both files)  -> 0 / 0
imports: Step6Gen <- Induction.Step6Pins, Chain.Step5Gen, Chain.LWGen, Chain.Step34Gen;
         Step6KitGen <- Chain.Step6Gen, Induction.Step6Kit, Chain.Step2EventsGen, Chain.Step5CasesGen   (= ticket layering)
importers (grep in RBM3D/, RBM3D.lean): RBM3D/Chain/Step6KitGen.lean, RBM3D.lean
column-0 def/abbrev/structure in Step6KitGen: 0   (X1-C4: new public defs only in Step6Gen)
C1/X1-C1 token grep (ticket regex + STGridRepNgL), code lines of Step6Gen 1-388 and Step6KitGen 1-893 (before bridges/instances): 0 / 0
```

## 4. Statements against the binding pins (uncommitted scratch `audit_chk.lean` = the check file + `import RBM3D.Chain.Step6KitGen` + 14 examples)
```
example : T2502_Exp2UgL C μ s t = STExp2UgL C μ s t := rfl
example : T2502_Step2CoregL C μ s t = STStep2CoregL C μ s t := rfl
example : T2502_IngR6gL d R law Flow mk T0 Concl = STIngR6gL d R law Flow mk T0 Concl := rfl
example : T2502_Step6RgL d R law Flow mk T0 = STStep6RgL d R law Flow mk T0 := rfl
example : T2502_ExpAvgAtgL C μ u = STExpAvgAtgL C μ u := rfl
example : T2502_ImproveExpAvergL d law Flow mk T0 = STImproveExpAvergL d law Flow mk T0 := rfl
example : T2502_ExpHierAtgL C μ n = STExpHierAtgL C μ n := rfl
example : T2502_ExpDuhamelZAtgL C μ n = STExpDuhamelZAtgL C μ n := rfl
example : T2502_ExpDuhamelQAtgL C μ n = STExpDuhamelQAtgL C μ n := rfl
example : T2502_ExpDuhamelZgL d law Flow mk = STExpDuhamelZgL d law Flow mk := rfl
example : T2502_ExpDuhEqgL C μ s t = STExpDuhEqgL C μ s t := rfl
example : T2502_EGtHiConclgL C μ s t = STExpEGtHiConclgL C μ s t := rfl
example : T2502_EGtHiOfLW C μ s t := st6_EGtHi_of_LWg C μ s t
example : T2502_Step6RgL_band 3 STReg5III ↔ STStep6R 3 STReg5III := (STStep6R_iff_gL 3 STReg5III).symm
$ lake env lean audit_chk.lean; echo exit $?      -> exit 0; "error"/"sorry" lines: 0
```
All variables are free (`variable` binders), so each equality is the pin text at every argument; the check file itself compiles on the branch (it is the prefix of the scratch file).
Non-binding texts (target 3, renamed band texts): equivalence to the band at the band tuple is a compiled bridge for each:
`bandFM_*` (`Iff.rfl`/rewrites through `bandStep2_Ugen`, private `Step6Gen_STthetaOp_eq`), `STIngR6_iff_gL`, `STStep6R_iff_gL`,
`STStep6{,I,II,III,IV}_iff_gL`, `STImproveExpAver_iff_gL`, `STExpLKLKHi/DriftLo/DriftDecay/WardI/WardII/IniI_iff_gL`; one-way
(eventual twins, ticket answer (5)): `STExpDuhamelZ/Q_to_gL`, `bandFM_STExpDuhEq_to_gL` (band => generic), `STExpInt{I..IV}_of_gL`
(generic => band, because the generic integrated pins read the weaker eventual `STExpDuhEqgL` premise).
Quantifier order of `STIngR6gL`: `3 ≤ d → ∀ κ ε 𝔡 > 0, ∃ 𝔠d ∈ (0, 1/100], ∀ 𝔠 sz z, Flow → ∀ s t …` (pinned `∃` before `(sz, z)`), band premise list, no `STKboundgL`/`STKwardgL` (answer (6)).

## 5. Hidden hypotheses, vacuity, cycles
- No `structure` or `class` in the two files; no new kernel, no `FlowFM`/`Step2Mat` field; every premise is a named argument.
- Dependencies are merged modules only (imports above); no cycle (the two files are leaves; importers listed in §3).
- Family premises of the wrappers (`grep -nE "∀ \(sz : Sizes d\)"`): hits at `Step6KitGen.lean:676-797` are `gK`, `hK1`, `hKer`; the rest are tuple binders of defs and bridge helpers (`Step6Gen.lean:101-138, 312-329, 501-523`). `hKer` is guarded (`∀ κ > 0, ∃ κm > 0, ∀ sz ε 𝔠 𝔡 z, Flow → …`, `κm` before `(sz, z)`, as the ticket's pinned-`∃` rule). `hK1` is unguarded: see Observation O1.
- Cores `st6_case{I..IV}_coreg` take the ingredient conclusions at `(C, μ, s, t)` and `STExpEGtHiConclgL` explicitly (target 8 as specified); no `hK1`, no `LWtermEXPG`.

## 6. Compiled nonempty instances (target 9)
```
$ coverage script (public theorems vs names inside example bodies)
Step6Gen.lean     public theorems: 47 examples: 37 | not in a same-file example: ['Step6Gen_ingR6_iff_congr', 'Step6Gen_ingR6_of_gL', 'STExpLKLKHi_iff_gL'] | not in any example: ['Step6Gen_ingR6_iff_congr', 'Step6Gen_ingR6_of_gL']
Step6KitGen.lean  public theorems: 30 examples: 26 | not in a same-file example: [] | not in any example: []
```
Data: `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `sz0` (`L₀ = 4`, `W₀ = 32`, `lam₀ = 1/64`, `(s,t) = (0, 1/16)`, regime III), `szB` (`(7/8, 15/16)` I, `(15/16, 31/32)` II), `szG` (`(5/8, 3/4)` IV), law `seqP`, carrier `bandFM`.
Read in the file (`Step6KitGen.lean:928-1243`):
- cores at 1084/1097/1113/1138: admissibility (`sz0/szB/szG_admissible`), time ranges (`norm_num`), regimes (`sz0_reg5III`, `szB_reg5I/II`, `szG_reg4`) discharged; only conclusions of other gates' pins remain hypotheses.
- wrappers at 1162/1177/1191/1210: `hμ` (`inferInstance`), `hFF` (`step5CasesGen_flowFacts_band 3`), `hRot` (`Step2EventsGen_bandRot3`), `hK1` (`ST_Kloop_one`), `hSum`/`hNZ` (proved `stek_sumNdecaygL_band`/`stek_nonzerogL_band`), `hKer` (`κm = √(2κ)/2`, `STEKBandKer`, `gK = lam`, R1 at `Aof = 1`) discharged; `LWtermEXPG`, the ingredient pins and the Duhamel families stay hypotheses (other gates); conclusion read at concrete data by the merged `inst_step6I..IV`.
- targets 5-7: `LWAvgLawgL_of_STAvgUgL_at` etc. at `u ≡ 1/32 ∈ [0, 1/16]`; `st6_EGt_eq_LWEg` at `n = 0`, loop `((+,-),(0,e₁))`; `st6_ini_sumNdecayg`, `st6_ini_nonzerog` with every deterministic premise discharged (II boundary `1-s = lam²/L²` hit).
No `N = 0`, empty index type, collapsed window or `False` premise. Verdict on instances: present for every target theorem of the ticket (see O2 for location).

## 7. Paper deltas
Lean/paper differences in row a: (i) the generic Duhamel texts `STExpDuhEqgL`, `STExpDuhamelZgL/QgL` are eventual in `n` (paper and band: every `n`); ticket decision (5), DECISIONS §314. Prove report (d) 8 proposes it as optional `T2502a` — covered as a candidate (not yet in `docs/paper-deltas.md`: `grep -n T2502` 0 hits; dispatcher numbers it). (ii) `H₀ ≠ 0` generality: covered by `6:12-21` per the ticket. No other statement difference found; the remaining texts are renamings of band texts, bridged in §4.

## 8. Verdict per target
| target | verdict |
|---|---|
| 1 vocabulary twins | PASS |
| 2 `STExp2UgL`, `STStep2CoregL`, `STIngR6gL`, `STStep6RgL` (binding), `STStep6IgL`..`STStep6gL`, `STStep6ConclgL` | PASS |
| 3 ingredient texts and pins (binding ones `rfl`) | PASS |
| 4 bridges, `STExp2gL_of_STExp2UgL`, `ST_step6R_of_anygL` | PASS |
| 5 glue at a law | PASS |
| 6 LW readings incl. `st6_EGtHi_of_LWg` (= `T2502_EGtHiOfLW`) | PASS |
| 7 initial terms | PASS |
| 8 cores + wrappers, §7b | PASS |
| 9 instances | PASS |

**Overall: PASS.** No dispatcher sign-off needed for the merge.

## 9. Observations (no statement, instance, build, axiom or delta-coverage defect)
- O1. `hK1` of the four wrappers is quantified over every `(sz, z)` without the `Flow` guard. Band: discharged for all `(sz, E)` by `ST_Kloop_one` (compiled). BA: the named candidate `baKsol_one` (`BA/KInduct:77`) needs `BAReal d L g κ E m` and `3 ≤ L`, so the unguarded form is not shown dischargeable at the BA tuple. Per ticket decision (4) the wrappers serve the band and V1-BA uses the cores (which do not take `hK1`), so no planned consumer is affected; if a BA wrapper is ever wanted, guard `hK1` by `0 < κ → Flow sz κ ε 𝔠 𝔡 z →` (V1-BA note).
- O2. `STExpLKLKHi_iff_gL` (Step6Gen) is instanced only in `Step6KitGen.lean:1078` (the importing file of the same row), not in Step6Gen itself; the stem-prefixed public helpers `Step6Gen_ingR6_iff_congr`, `Step6Gen_ingR6_of_gL` have no own example (they are used by the instanced bridges `STIngR6_iff_gL` .. `STExpInt*_of_gL`).
- O3. `hKer` merges draft rows 5 and 6 with the bulk datum `κm` and `Aof κm`; the BA choice (`κm = κ`, `Aof κ = (κ+1)/κ`) is not checked here (prove report (d) 3; V1-BA).
- O4. Registry: `STStep6gL` placed in `supersededProps` (as band `STStep6`); unprimed generic `STExpIniIgL`/`STExpIntIgL` are owed (report (d) 4, 5): dispatcher classification items.
