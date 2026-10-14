Auditor model: claude-opus-5-5

# T2506b audit (round 1) — row b: `Chain/ExpIniIGen`, `Chain/ExpWardIGen`, `Chain/ExpIntIIGen` (targets 6-13)
Written Wed Oct 14 12:22 UTC 2026 (`date -u`). Branch `t/T2506b` at 5d0d47e4 (merge-base d3104f3b = ticket base). Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2506b-audit1` (detached). Scratch: `T2506b/Audit.lean` in the auditor scratchpad (uncommitted).

## Verdict
| target | decl(s) | verdict |
|---|---|---|
| 6 | `STExpIniIConclgL'`, `STExpIniIgL'`, `bandFM_STExpIniIConcl'`, `STExpIniI'_iff_gL'` | PASS |
| 7 | `expIniI_fastDecayg`, `expIniI_sameg`, `expIniI_Qopg`, `expIniI_mixedg` | PASS |
| 8 | `stExpIniIgL'_of` (+ re-derivation `stExpIniI'_gen_band`) | PASS |
| 9 | `STExpWardIConclgL'`, `STExpWardIgL'`, bridges, `expWIg_concl_prime` | PASS |
| 10 | `expWI_Psum_eqg`, `expWI_Psum_precg` | PASS |
| 11 | `expWI_coreg`, `stExpWardIgL_of`, `stExpWardIgL'_of` (+ `stExpWardI(')_gen_band`) | PASS |
| 12 | `expIntII_drift_integral_leg`, `expIntII_kernel_unifg`, `STExpIntConclgL_of_kernel`, `STExpIntIIConclgL_of_flow` | PASS |
| 13 | `stExpIntIIgL_of` (+ `stExpIntII_gen_band`) | PASS |

## 1. Statements against the pins
Binding texts (the four `T2506_*` defs of `docs/tickets/checks/T2506-check.lean`), text diff (whitespace collapsed, `T2506_` → `ST`):
```
$ python3 (grab def body from check and from Chain/<file>.lean; compare)
STExpIniIConclgL' IDENTICAL 666 666
STExpIniIgL' IDENTICAL 316 316
STExpWardIConclgL' IDENTICAL 1060 1060
STExpWardIgL' IDENTICAL 355 355
```
Elaborated equality (scratch `Audit.lean` = check-file Part 2 + the three new modules; compiled with `lake env lean`, exit 0):
```
example ... : STExpIniIConclgL' C μ s t = T2506_ExpIniIConclgL' C μ s t := rfl
example ... : STExpWardIConclgL' C μ s t = T2506_ExpWardIConclgL' C μ s t := rfl
example (d : ℕ) law Flow mk T0 : STExpIniIgL' d law Flow mk T0 = T2506_ExpIniIgL' d law Flow mk T0 := rfl
example (d : ℕ) law Flow mk T0 : STExpWardIgL' d law Flow mk T0 = T2506_ExpWardIgL' d law Flow mk T0 := rfl
example (d : ℕ) : T2506_ExpIniIgL'_band d ↔ STExpIniI' d := (STExpIniI'_iff_gL' d).symm
```
Merged pins: `stExpWardIgL_of : … STExpWardIgL d law Flow mk T0`, `stExpIntIIgL_of : … STExpIntIIgL d law Flow mk T0` conclude the
merged `Chain/Step6Gen` texts verbatim (no restatement). `V1L-C1`: no statement reads `STImproveExpAvergL`/`st6_expAvgU_of_ping`;
the Ward pins read `STExpAvgUgL` on `[s,t]` (as merged `STExpWardIgL`).

Non-binding row shape `T2506_RowBOf` (conjuncts 1-3) — compiled in the scratch file from the theorems (exit 0):
```
example (d) (law) (Flow) (mk) (T0) (Ker) (gK) (Aof) (hFB : T2506_FamBase d law Flow mk T0)
    (hKb : ∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow … → STKboundgL (mk sz z) (law sz)) (hAof : ∀ κm, 0 < κm → 1 ≤ Aof κm)
    (hKer : ∀ κ, 0 < κ → ∃ κm, 0 < κm ∧ ∀ sz ε 𝔠 𝔡 z, Flow … → (∀ n, κm ≤ Im m) ∧ Ker … κm ∧ (∀ᶠ n, 0 < gK ≤ 𝔡⁻¹) ∧ R1 at Aof κm)
    (hRep : ∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow … → ∃ H₀ g' E, CltRepg (mk sz z) (law sz) H₀ g' E) (hB45 : B45Gen_Facts d Flow mk) :
    (STEKSumRes2NALgL d law Ker → STEKSumRes2gL d law Ker → T2506_ExpIniIgL' d law Flow mk T0) ∧
    (T2506_FamWard d Flow mk → STExpWardIgL d law Flow mk T0 ∧ T2506_ExpWardIgL' d law Flow mk T0) ∧
    (STEKNonzerogL d law Ker Aof → STExpIntIIgL d law Flow mk T0) := …   -- exit 0
```
So the producers fit the row shape with the following premises beyond `FamBase`/`FamWard` (all explicit, guarded, before no
pinned `∃` after `(sz, z)`; each has a merged BA discharge, checked by `#check` / a compiled example):
| premise | used by | merged BA discharge (compiled) |
|---|---|---|
| `hKb : STKboundgL` (row 17) | 8 | `baKbound_holds : ∀ d, BAKbound d` (`BA/KBound:245`) |
| `hKer` in the `∃ κm` form (rows 6/16; FamKerData uses `κ`) | 8, 13 | same text as hypothesis `hKer` of merged `ST_step6_caseII_of_pinsgL` (`Step6KitGen:752`); band `Step6KitGen_KerFR1_band` |
| `hRep : ∃ H₀ g' E, CltRepg` (T2502 row 9) | 11 | `example : … BAFlow … → ∃ H₀ g' E, CltRepg (baFMz sz z) (seqP (sz.withLam 0)) H₀ g' E := ⟨_,_,_, baCltRepg_holds sz z⟩` (exit 0) |
| `hB45 : B45Gen_Facts d Flow mk` (contains row 19's `ZeroModeGen_WardCls`) | 11 | `baB45Gen_facts : ∀ d, B45Gen_Facts d BAFlow baFMz` (`BA/B45BA:205`) |
These are disclosed in the prove report ((a′) 3-4, (d)); the ticket's shapes/family table are "not binding (fixed at the 1a)".

## 2. Hidden hypotheses, vacuity, cycles
- Only four new defs (Prop texts, X1-C4), no structure/class/instance (`grep -nE "^(noncomputable )?(def|abbrev|structure|class|inductive|instance) "`:
  `ExpWardIGen:52,70`, `ExpIniIGen:58,70`). No kernel def (U-C4).
- C1 / V1L-C1 / UBA tokens over public statements (script over the text up to `:=`):
```
ExpIniIGen bandFM_STExpIniIConcl' ['seqP']
ExpIniIGen STExpIniI'_iff_gL' ['STFlow', 'STflowE', 'lemT', 'seqP']
ExpWardIGen bandFM_STExpWardIConcl' ['seqP']
ExpWardIGen STExpWardI'_iff_gL' ['STFlow', 'STflowE', 'lemT', 'seqP']
```
  (bridges only; 0 hits of `STImproveExpAver|st6_expAvgU_of_pin|sz.withLam|STGridRepNgL` in public statements.)
- Dependencies are merged modules only; imports: `Step6KitGen`, `Induction/ExpIniI`, `Induction/QopNorm`, `CltFarUGen`
  (IniI); `Step6KitGen`, `Induction/ExpWardI`, `B45Gen`, `Step2IterGen`, `CltGen` (WardI); `Step6KitGen`, `Induction/ExpIntII` (IntII).
  `grep -nE "^import RBM3D\.(BA|Chain\.Step2Kern|Chain\.ExpAvgGen)"`: 0. No band file imports a new file (importer: `RBM3D.lean` only).

## 3. Compiled nonempty instances (in the same files; `d = 3`, `szB` with `L = 4`, `W_n = n+4`, `lam = 1`; `zB`, `flow_zB` at
`(κ,ε,𝔠,𝔡) = (1/10,1/10,1/6,1/10)`; regime (i) `(s,t) = (7/8, 15/16)` with `szB_reg5I`; regime (ii) `(15/16, 31/32)` with `szB_reg5II`)
| public theorem | example (file:line) | hypotheses left |
|---|---|---|
| `bandFM_STExpIniIConcl'`, `STExpIniI'_iff_gL'` | Ini 866, 870 | bridge input |
| `expIniI_fastDecayg`, `_sameg`, `_Qopg`, `_mixedg` | Ini 876, 887, 903, 922 | `STDecaygL`, `STExp2gL` (stochastic pins) |
| `stExpIniIgL'_of` | Ini 941 (pin at band tuple) | none |
| `stExpIniI'_gen_band` | Ini 950 (`InstIng6Concl` at `szB, zB, 7/8, 15/16`) | none |
| `bandFM_STExpWardIConcl'`, `expWIg_concl_prime`, `STExpWardI'_iff_gL'` | Ward 494, 498, 502 | bridge input |
| `expWI_Psum_eqg` | Ward 510 (`n = 0`, `u = 7/8`, `σ = (+,-)`) | none |
| `expWI_Psum_precg`, `expWI_coreg` | Ward 524, 537 | `STExpAvgUgL` (stochastic pin) |
| `stExpWardIgL_of`, `stExpWardIgL'_of` | Ward 555, 561 | none |
| `stExpWardI(')_gen_band` | Ward 569, 573 | none |
| `expIntII_kernel_unifg`, `_drift_integral_leg`, `STExpIntConclgL_of_kernel`, `STExpIntIIConclgL_of_flow` | IntII 356, 372, 394, 408 | `STExpDriftHiConclgL` (drift pin) |
| `stExpIntIIgL_of` | IntII 422 | none |
| `stExpIntII_gen_band` | IntII 429 | none |
Every deterministic hypothesis is discharged (`s < t`, `t < 1`, regimes, admissibility, window `1 - s = lam²/L² = 1/16`,
`lam²/L³ = 1/64 ≤ 1 - u`, `STEKBandKer` with R1 at `Aof = 1`, `𝔠d = 1/300`). Not degenerate: `L = 4`, `W_n → ∞`, open windows,
mollifier class nonempty (Ward 549). The mollifier family is nonempty with `Cq, c > 0` (`st6_mollifier_familyg`).

## 4. Build, axioms, diff
```
$ lake build RBM3D.Chain.ExpIniIGen RBM3D.Chain.ExpWardIGen RBM3D.Chain.ExpIntIIGen   # audit worktree
⚠ [3951/3951] Built RBM3D.Chain.ExpIniIGen (16s)
Build completed successfully (3951 jobs).
$ grep -c "^error" build.log ; grep "^warning: RBM3D/Chain/Exp(IniI|WardI|IntII)Gen" | grep -vc "100 character"
0
0
$ lake env lean Audit.lean   # #print axioms of the 28 public declarations
exit=0 ; 28 of 28 lines "depends on axioms: [propext, Classical.choice, Quot.sound]"; 0 other
$ grep -nE "sorry|admit|native_decide|^axiom" <3 files> | wc -l
0
$ git diff --name-only main...t/T2506b
RBM3D.lean
RBM3D/Chain/ExpIniIGen.lean
RBM3D/Chain/ExpIntIIGen.lean
RBM3D/Chain/ExpWardIGen.lean
RBM3D/Test/Axioms.lean
$ git diff --name-only main...t/T2506b -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Defs | wc -l
0
$ wc -l <3 files>
957 / 581 / 438 = 1976 (per-file stop 2,000; row stop 2,700)
```
Only sole writable files touched; no band or merged file in the diff; no frozen signature touched. `RBM3D.lean`: three
`import` lines inserted before `#assert_rbm_axioms` (which stays last). `Test/Axioms.lean`: three owed comments
(`STExpWardIgL`, `STExpIniIgL`, `STExpIntIIgL`) name their producers; `structuralProps` += `STExpIniIConclgL'`,
`STExpWardIConclgL'`. Name clash (`git grep -F -w` on `main`) of the four `*_gen_band` names: 0 each.

## 5. Paper deltas
No new Lean/paper statement difference: the four primed texts are verbatim twins of the band texts `STExpIniIConcl'`,
`STExpIniI'`, `STExpWardIConcl'`, `STExpWardI'` (bridges compiled); the eventual Duhamel form is D725 and the per-flow
average is D727 (both in `docs/paper-deltas.md:1808, 1813`). The extra producer premises (§1 table) and the constants
(`2·Aof`, `N^6`, `K₆`, `𝔠d`) are Lean-internal hypotheses of producers, not of the paper's statements. Coverage complete.

## Observations (no statement, instance, build, axiom or delta effect)
- O1. The re-derivations `stExpIniI'_gen_band`, `stExpWardI_gen_band`, `stExpWardI'_gen_band`, `stExpIntII_gen_band` are
  public and neither pinned by name nor prefixed with a file stem (CLAUDE.md §3 (E)); merged precedent
  `stKbound_timeIcc_gen_band`; 0 clashes. Dispatcher may ask for a rename; disclosed in the prove report (d).
- O2. The ticket's family table needs the file columns of rows 17 (`ExpIniIGen`) and 9/19 (`ExpWardIGen`: `hRep`,
  `B45Gen_Facts`) updated; all have merged BA discharges (§1 table). Disclosed in the prove report (a′), (d).
- O3. The ticket's registry instruction to retitle the header at `Test/Axioms:224` was not applied on this row (likely
  row a's or the merge union's); no effect on `#assert_rbm_axioms`.
- O4. `ExpWardIGen` imports `RBM3D.Chain.CltGen` (merged; defines `CltRepg`), one module beyond the ticket's layering line.
- O5. Prove report (b) line "warn=0" refers to `lake env lean`; `lake build` replays long-line linter warnings for lines
  before `set_option linter.style.longLine false` in the three files (style only).
