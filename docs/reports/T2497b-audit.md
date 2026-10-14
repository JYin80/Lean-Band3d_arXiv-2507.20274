Auditor model: claude-opus-5-5

# T2497b audit (row b, U1s2b, Iterations, targets 10-15), round 1. Wed Oct 14 01:14:18 UTC 2026

Worktree `RBM3D-wt/T2497b-audit1`, detached at `t/T2497b` HEAD `351c0e05`. Ticket `docs/tickets/T2497.md`, check `docs/tickets/checks/T2497-check.lean`.
Scratch files (uncommitted): `<scratchpad>/T2497b/{pincheck.lean,sig.py,sig10.py,c1.py}`.

## 1. Build and axioms
```
$ lake build RBM3D.Chain.IterationsGen RBM3D.Chain.IterationsGen2
⚠ [3894/3895] Built RBM3D.Chain.IterationsGen (7.2s)
⚠ [3895/3895] Built RBM3D.Chain.IterationsGen2 (4.8s)
Build completed successfully (3895 jobs).        # exit 0; errors: 0; warnings are linter-only (longLine 253, show 37, unused binder 24, ...)
$ lake build        # full library incl. #assert_rbm_axioms (Test/Axioms registry text of this branch)
non-vacuity certificates: 0 of 122 premises in the two ledgers; ...
Build completed successfully (4374 jobs).        # exit 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/Chain/IterationsGen*.lean ; echo $?
1
$ lake env lean pincheck.lean   # 22 #print axioms (every public target of 10-14) appended to the check
exit 0, error lines 0
  22 [propext, Classical.choice, Quot.sound]
```
The module build itself prints 9 `#print axioms` (targets 11, 12, 13, 14 and the two instance theorems), all with the same three axioms.

## 2. Diff scope and layering
```
$ git diff --name-only main...t/T2497b
RBM3D.lean
RBM3D/Chain/IterationsGen.lean
RBM3D/Chain/IterationsGen2.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2497b -- RBM3D/Induction/{IterationsA,IterationsB,QGridA,QGridB,NQEndFlow,Step3,Step4,MainIndRegimes,QDriftA,QDriftB,QBudgetB,QLevelsB,QEndA,QEndGrid,QProxy}.lean RBM3D/Chain/{Step34Gen,HierDriftGen,GridEnvelopeGen,ZeroModeGen,NQGood1Gen,KDecayGen}.lean RBM3D/BA | wc -l
       0
$ git diff main...t/T2497b -- RBM3D/Test/Axioms.lean | grep -E "^[-+] " | cut -c1-60
-   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:it
+   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:it      (now ends "...; generic: `stIterationsgL'_of`, `stIterationsIIgL'_of` (T2497, `Chain/IterationsGen2`); BA: U1-BA")
+   `RBM.BA.STXiBootgL', -- `(am;asoi222)` at `B_s` (DECISIO      (owedProps line: hypothesis of public `iterationsB_stepg`)
RBM3D.lean: +import RBM3D.Chain.IterationsGen, +import RBM3D.Chain.IterationsGen2 (after the last import; #assert_rbm_axioms stays last)
imports: IterationsGen <- IterationsA, Step34Gen, KDecayGen, StepDecompGen, GridEnvelopeGen, NQGood1Gen
         IterationsGen2 <- IterationsGen, IterationsB, NQEndFlowGen
$ git grep -n "import RBM3D.Chain.IterationsGen" t/T2497b -- RBM3D RBM3D.lean
t/T2497b:RBM3D.lean:600 / :601 ; t/T2497b:RBM3D/Chain/IterationsGen2.lean:6
```
All four files are sole writable files of row b; no band file, no `BA/*` import; the new files are leaves (imported only as the ticket allows): no cycle. `NQGood1Gen` is an extra merged `Chain/*` import, allowed by the ticket (`:23`).

## 3. Statements against the pins (compiled; check file + appended examples)
```
$ { echo "import RBM3D.Chain.IterationsGen2"; cat docs/tickets/checks/T2497-check.lean; cat <audit examples>; } > pincheck.lean
example : T2497_IterationsOf T2497_IterFam := stIterationsgL'_of
example : T2497_IterationsIIOf T2497_IterFam := stIterationsIIgL'_of
example : @IterationsGen2_Fam = @T2497_IterFam := rfl
example ... : IterationsAScaleg Cf s t A T cB cv K ↔ T2497_IterScaleg Cf s t A T cB cv K := IterationsGen_scaleg_iff ...
example ... : IterationsAScale sz E s t A T cB cv K ↔ T2497_IterScaleg (bandFM sz E) s t A T cB cv K :=
  (bandFM_IterationsAScale ..).trans (IterationsGen_scaleg_iff ..)
example (d) : T2497_IterFam d seqP STFlow (bandStep2Mat (STflowE z)) seqHflow STflowE lemT := IterationsGen2_famBand d
$ lake env lean pincheck.lean -> exit 0, 0 error lines (the whole check, incl. Part 3 band-name #checks, also compiles on the branch)
```
Targets 14 conclude the merged `STIterationsgL'`, `STIterationsIIgL'` (`Chain/NQEndFlowGen.lean:140`) by name; `𝔠d = 1/100` is the `∃` before `(sz, z)` (`refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩` right after `κ ε 𝔡 Cd`). No local def of an R2* text.

Target 10 (verbatim ports), mechanical signature diff band → generic (rename `…g`, `sz.Prec`/`Prec sz` → `PrecL sz μ`, drop `(sz : Sizes d)`):
```
$ python3 -I sig10.py
st_prec_one_add_sup: band :103 gen :47 identical-after-rename=True
st_prec_of_xi: band :129 gen :73 identical-after-rename=True
iterationsA_prec_mono_right: band :818 gen :119 identical-after-rename=True
iterationsA_prec_mono_left: band :826 gen :127 identical-after-rename=True
iterationsA_prec_absorb: band :834 gen :135 identical-after-rename=True
iterationsA_prec_rpow: band :850 gen :151 identical-after-rename=True
iterationsA_prec_one_add_mul: band :865 gen :166 identical-after-rename=True
st_one_le_XiL:  B: {n} {E v} (k) (ω) (hB : 0 < sz.Bctl n v) : 1 ≤ STXiL sz n E v k ω
                G: (Cf : FlowFM sz) {n} {v} (k) (ω) (hB : 0 < sz.Bctl n v) : 1 ≤ STXiLg Cf n v k ω
st_one_le_XiLK: same shape with STXiLK / STXiLKg
```
Target 11 (`python3 -I sig.py`): band `iterationsA_xiL_odd_le` (`IterationsA:740`) and `iterationsA_xiL_odd_leg` (`IterationsGen:211`) have the same conclusion with `STXiL sz n E v` → `STXiLg Cm.toFlowFM n v`, same `hB`, `hN : 3 ≤ N`; added hypotheses exactly the ticket's loop class (decision (5)): `Step34Gen_LCompat Cm Hf`, `StepDecompGen_LoopForm Cm E`, `∀ n u ω, (Hf n u ω).IsHermitian`.
Target 12: `IterationsAScaleg` = `T2497_IterScaleg` (above). `iterationsA_scale_Ig/IIg` keep the band hypotheses (`2 ≤ d`, `0 < 𝔠d ≤ 1/16` resp. `≤ 1/24`, `STRegIterI`, `STConStInd`, `WO`, `t < 1`) and replace `|E| < 2` by `LoopForm` + inline `‖m n‖ ≤ 1` (ticket rows 3-4; E′ route, private `IterationsGen_Ep`). `avg/apriori/rela` drop `hE` (apriori: `LoopForm` replaces it, as pinned).
Target 13: band `iterationsB_step` (`IterationsB:454`) vs `iterationsB_stepg` (`IterationsGen2:272`): same `hsize, hS, hboot, hrela, havg, hapri, hN : 2 ≤ N, hk : 1 ≤ k, IH1 (r+1 ≤ N, level k), IH2 (r ≤ N+2, level k-1)` and conclusion, with `IterationsAScale`→`IterationsAScaleg`, `STXiBoot'`→ merged `STXiBootgL'`, `etaT (E n)`→`Cm.eta n`, `STIterHyp`→`STIterHypgL`; plus the loop class `hLC, hL, hHf` (needed by the odd chain bound, target 11).

## 4. Hypothesis rules, vacuity, cycles
```
$ python3 -I c1.py      # C1/X1-C1 regex of the ticket over the statement text of every public decl (non-instance region)
RBM3D/Chain/IterationsGen.lean: public decls 19, C1/X1-C1 hits in statements: 0
RBM3D/Chain/IterationsGen2.lean: public decls 5, C1/X1-C1 hits in statements: 3
   (432, 'IterationsGen2_Fam d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)')
   (432, '(fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z)')
   (432, '(fun _ z n => lemT (z n)) := by')
$ grep -nE "(def|abbrev|structure) (STXiLg|...|DecayGen_Spec)\b|STGridRepNgL|sz\.withLam|\bgK\b|import RBM3D\.BA" <new files>; echo $?
1
$ grep -c "∀ (sz : Sizes d)" IterationsGen.lean IterationsGen2.lean
IterationsGen.lean:0   IterationsGen2.lean:11   (all in IterationsGen2_Fam and the two target-14 statements)
```
The 3 C1 hits are the band bridge `IterationsGen2_famBand` (label: band reading, check shape `:400`), not a generic statement.
- Structure fields: `IterationsAScaleg` is the pinned scale record; it is concluded by `iterationsA_scale_Ig/IIg` (not an unproved hidden hypothesis). `IterationsGen2_Fam` is definitionally `T2497_IterFam` (rfl above), every row discharged at the band by `IterationsGen2_famBand` (for every `d`).
- Family guards: rows 3-4 under `0 < κ → Flow …`, rows 5-6 unguarded, row 1 own, row 2 unguarded, as in the ticket table.
- Dependencies are merged (`NQEndFlowGen` c72bc745 etc.); no new file is imported by a band file; no cycle.
- External/eventual hypothesis limit check: `STConStInd 𝔠d s t` at `szB` is discharged in Lean by `conStInd_const szB szB_W_tendsto …` (limit `W → ∞`), not assumed; preflight's numeric thresholds (`n ≥ 1.15e10`, `1.23e10`) are thresholds of an `∀ᶠ n`, not a witness size.

## 5. Compiled nonempty instances (in the same files; built above)
| target | instance (file:line) | data | deterministic hyps discharged | stochastic pins left as hyps |
|---|---|---|---|---|
| 10 | `IterationsGen:545-587` (9 examples) | `szB`, `seqP szB`, `n=0`, `v=1/2`, `k=3`, `U=Unit`, `V=Fin 2`, `ξ=1/2, ζ=1`, `c=2`, `θ=1/2` | `szB_hsize`, `st_Bctl_pos`, `prec_of_le` | none |
| 11 | `IterationsGen:589` | `N=3`, `szB`, `zB`, `n=0`, `v=1/2` | `bandStep34_LCompat`, `zB_loopForm`, `seqHflow_isHermitian`, `hB` | none |
| 12 | `IterationsGen:599, 604, 610, 615, 621` | `(7/8,15/16)` case (i), `(15/16,31/32)` case (ii), `𝔠d=1/100`, `𝔡=1/10`, `d=3`, `m=3`, `m=2` | `szB_regIterI`, `conStInd_const`, `szB_WO`, `t<1`, loop class, `‖m‖≤1` | `STAvgUgL`, `STStep1LoopgL`, the `𝒦` `≺` bound |
| 13 | `IterationsGen2:532, 553, 574` | case (ii) `(N,k)=(3,2)` and `(2,1)`, case (i) `(3,2)` | scale record (`szB_scaleI/II`), loop class, `hsize`, `2≤N`, `1≤k` | `STXiBootgL'`, rela/avg/apriori `≺`, `IH1`, `IH2` |
| 14 | `IterationsGen2:468` `inst_iterationsgL'`, `:490` `inst_iterationsIIgL'`, `:513` | `d=3`, `szB`, `zB`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, bundle `IterationsGen2_famBand 3` | `flow_zB`, `0≤s`, `s<t`, `szB_flow_ht` (`t ≤ lemT`), `szB_regIterI`/`szB_caseII`, `conStInd_const`, the bundle; `:513` also `STKboundgL` via `stKbound_of_flow` | `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'`, `IH1/IH2` |
None degenerate: `size szB ≥ 4096`, `d = 3`, nonempty `STPair` windows (`s < t`), `IH1`/`IH2` ranges nonempty at `(3,2)`, no `False` premise.

## 6. Paper deltas
The prove report proposes no new candidate and cites inherited deltas; present in `docs/paper-deltas.md`: D170 (`:689`, T2087a, `Ψ` at `d ≥ 3`), D171 (`:693`, `p ≥ 2` vs paper `p ≥ 4`), D563 (`:1522`, T2246a, R2* `B_s` in the martingale term). The carrier-form premises (`LoopForm`, `‖m‖ ≤ 1`, `LCompat`, Hermitian `Hf`) are model-interface hypotheses discharged at the band (`IterationsGen2_famBand`); they change no paper statement at the model. No uncovered Lean/paper statement difference found.

## 7. Verdicts
| target | verdict |
|---|---|
| 10 `≺` helpers, `st_one_le_XiLg/XiLKg` | PASS |
| 11 `iterationsA_xiL_odd_leg` | PASS |
| 12 `IterationsAScaleg`, `iterationsA_scale_Ig/IIg`, `avg/apriori/rela` | PASS |
| 13 `iterationsB_stepg` | PASS |
| 14 `stIterationsgL'_of`, `stIterationsIIgL'_of` | PASS |
| 15 instances | PASS |

## 8. Observations (no statement, instance, build, axiom or delta effect)
- O1: one `owedProps` line `RBM.BA.STXiBootgL'` added (ticket expected none, but allows "new `owedProps` lines only for what the scan reports"); the full build passes with it. Dispatcher may want to note it in the U3s3/U3s4 ledger text.
- O2: landed 633 + 601 = 1,234 lines vs forecast 865-1,020 (row b); far below the 2,000 stop line.
- O3: the prove report's "26 new public declarations" = 24 non-instance + 2 named instance theorems; consistent with `grep`.

Overall: **PASS** (row b, targets 10-15). No dispatcher sign-off needed.
