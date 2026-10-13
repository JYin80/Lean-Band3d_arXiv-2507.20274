Auditor model: claude-opus-5-5
# T2478 (ST T1): 1a-audit round 2 of section (a) + (a′) (design gate; no Lean on `t/T2478`)

Written: Mon Oct 12 23:42:05 UTC 2026. Inputs: ticket `docs/tickets/T2478.md` (dispatcher answers (1)-(7), DECISIONS §279 (3)), check `docs/tickets/checks/T2478-check.lean`, `docs/reports/T2478-prove.md` section (a) (lines 2-67) and (a′) (lines 69-94, rule-(B) repair of round 1's Required items 1-3). Branch `t/T2478` = 2dcfcda5 (base), `main` = 08daf959. Scratch: `<scratchpad>/T2478/audit2/`. This round-2 report replaces round 1 (RETURN; its findings are summarised in §2).

## 1. Rerun of the section (a) scripts (copied unchanged to `audit2/`, run with `python3 -I`)
```
$ for f in instance lines gfsem cone t9check; do python3 -I $f.py > out_$f.txt; echo "$f exit $?"; done
instance exit 0
lines exit 0
gfsem exit 0
cone exit 0
t9check exit 0
$ for f in instance gfsem cone lines; do diff -q out_$f.txt ../audit/out_$f.txt && echo "$f identical to round 1"; done
instance identical to round 1
gfsem identical to round 1
cone identical to round 1
lines identical to round 1
$ grep -E "central lines|^T1a|2.6x" out_lines.txt; tr ';' '\n' < out_cone.txt
central lines: Step2IterGen 1115, Step2IterGen2 471, OptL2Gen 1098, Step2CloseGen 281; target 9 itemised 525 (ticket cap 300)
T1a (targets 1-6) 1586; T1b without 9 1379, with 9 1904; row 2965 without 9, 3490 with 9; ticket 1550/1300/2850; split 1,950 fires: True; each half <= 1,950: True; REQ line 3,900: False
2.6x ticket central: T1a 4030 T1b 3380 row 7410; 2.6x own central: Step2IterGen 2899 OptL2Gen 2854 (stop line 2,000; reserve line 1,800 on central: False)
cones (transitive imports): Step2IterGen: 106 modules, 84293 lines, RBM3D.BA.* modules: 0
 OptL2Gen: 113 modules, 91507 lines, RBM3D.BA.* modules: 0
 Step2CloseGen (T10, T11): 137 modules, 120842 lines, RBM3D.BA.* modules: 0
 +FarEntry,CltGen (if target 9 stayed): 148 modules, 131053 lines, RBM3D.BA.* modules: 0
$ cat out_t9check.txt   # independent brute-force check of row 18 step (4) (round-1 auditor script)
d=3 L=7 c'=1.0 g=0.01 |1-u|=0.001: max LHS/(S^2 sqrtSTWB(r))=0.0484 ok=True; max W^-d e^-2c'r/(M/cB STWB(r))=1.0000 ok=True
d=3 L=7 c'=0.3 g=0.01 |1-u|=1e-05: max LHS/(S^2 sqrtSTWB(r))=0.0000 ok=True; max W^-d e^-2c'r/(M/cB STWB(r))=0.9529 ok=True
d=3 L=7 c'=0.1 g=1.0 |1-u|=0.5: max LHS/(S^2 sqrtSTWB(r))=0.0000 ok=True; max W^-d e^-2c'r/(M/cB STWB(r))=0.9665 ok=True
d=4 L=5 c'=0.5 g=0.01 |1-u|=0.0001: max LHS/(S^2 sqrtSTWB(r))=0.0000 ok=True; max W^-d e^-2c'r/(M/cB STWB(r))=0.9905 ok=True
d=1 L=60 c'=0.2 g=0.01 |1-u|=0.001: max LHS/(S^2 sqrtSTWB(r))=0.0327 ok=True; max W^-d e^-2c'r/(M/cB STWB(r))=1.0000 ok=True
d=2 L=15 c'=0.2 g=0.01 |1-u|=0.001: max LHS/(S^2 sqrtSTWB(r))=0.0065 ok=True; max W^-d e^-2c'r/(M/cB STWB(r))=1.0000 ok=True
```
The instance-script output matches (a) lines 39-51 verbatim (instance `sz0`, n=100, d=3, L=404, W=202^5, E=0, s=0, t=1/16, K=16: nondegenerate). Every number in (a) and (a′) reproduces.

## 2. Round-1 Required items against (a′)
| round-1 item | (a′) entry | check | status |
|---|---|---|---|
| 1. target 9 go, stays in `Chain/Step2CloseGen.lean`, pins `T2478_LocalReaderDec`, `T2478_LocalAvgOfL2Dec`; cite answer (3) and row 18; strike "moves to T1-BA" at lines 4, 26, 66 | (a′) 1 (lines 72-76) | answer (3)'s only fallback trigger is mathematical non-closure; row 18 closes (reproduced §1, round-1 §2 step check); pins exist (grep below); the three struck phrases are named; line 66 restated as "go, generic reader in T1b"; BA reading stays T1-BA (ticket `:43`) | met |
| 2. split T1a = 1-6 (1,586) / T1b = 7-11 (1,904; `Step2CloseGen` 806), row 3,490; strike "targets 7, 8, 10, 11" and the folding remark | (a′) 2 (lines 77-80) | figures from `lines.py` (above) and the sum below; T1b stacked on `t/T2478`, merged after T1a | met |
| 3. T1b layering with target 9: `Step2CloseGen` imports `Evolution/FarEntry` (→ `Chain/CltGen`); cone 148, BA 0 | (a′) 3 (lines 81-94) | grep below; cone reproduced | met |
```
$ grep -n "^import" RBM3D/Evolution/FarEntry.lean | grep CltGen
12:import RBM3D.Chain.CltGen
$ grep -nE "T2478_LocalReaderDec|T2478_LocalAvgOfL2Dec" docs/tickets/checks/T2478-check.lean
363:def T2478_LocalReaderDec : Prop :=
378:def T2478_LocalAvgOfL2Dec : Prop :=
$ grep -n "def STGijDecgL" RBM3D/Chain/CltGen.lean; grep -n "theorem bandFM_STGijDecgL_of_three_le" RBM3D/Evolution/FarEntry.lean
94:def STGijDecgL (t : ℕ → ℝ) : Prop :=
1724:theorem bandFM_STGijDecgL_of_three_le (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
$ python3 -I -c 'print(281+525, 1379+525, 1586+1904, round(2.6*806), round(2.6*1904))'
806 1904 3490 2096 4950
$ git diff main...t/T2478 | wc -l
       0
$ grep -n "StepDecompGen_LoopForm" RBM3D/Chain/StepDecompGen.lean | sed -n 3p; git merge-base --is-ancestor eaa247c4 main && echo "eaa247c4 on main"
60:def StepDecompGen_LoopForm {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E : ℕ → ℝ) : Prop :=
eaa247c4 on main
```
The last two lines confirm that answer (5)'s one-line `ListLink` bridge input (T2474) is merged and available to target 10.

## 3. Stage-1a deliverables (ticket "Preflight (stage 1a)")
| item | where | status |
|---|---|---|
| (i) exponent table | (a) rows 1-14 | met; rows 1-3, 7-12 reproduced by `instance.py` |
| (ii) concrete instance | (a) lines 35-60 | met; nondegenerate (`sz0` n=100); rows 4, 12 thresholds are internal `∀ᶠ n` steps |
| (iii) hypothesis table | row 20 | met; every class field has a band discharge |
| (iv) shapes of targets 3, 4, 5, 7; copy table; `open private` | row 22 | met (substitution map + spans; `open private` empty) |
| (v) site-1 obligations, J form | row 21 | met; Ĵ form suffices, no T1-BA twin |
| (vi) target 1 at BA under R1 | rows 13, 14, 17 | met; forward comparison from R1 exact; UBA-C1 not triggered (no coupling in T1 statements) |
| (vii) target 9 argument; go / move | rows 10-12, 16, 18 + (a′) 1 | met; **go** (answer (3)) |
| (viii) tripwire | row 19 | met; g 0.195 < 0.50, f_sem 0.003 < 0.30 (reproduced) |
| (ix) lines, split, imports, closure | row 15, 24 + (a′) 2-3 | met; no `RBM3D.BA.*` in any cone, including `Step2CloseGen` with `FarEntry`/`CltGen` (148 modules) |
| (x) premise scan, registry | row 23 | met; no new registry line; answer (6) owner texts named |

## 4. Binding stop lines
- Per file ≤ 2,000 on central (max `Step2IterGen` 1,115; `Step2CloseGen` with target 9 806): not hit.
- Reserve 1,800 on central: not hit.
- No `T2478_*` conclusion found unprovable as stated, no class field without a band discharge, no forbidden item.
- None planned: a new kernel, a new `FlowFM`/`Step2Mat`/`Step2Data` field, a `BA/*` import, an `STGridRepNgL` premise.
- No band or merged-file edit (G1 by construction).
- No unregistered unproved public premise.
- C6/I1 tripwire not fired.
- (vi) R1: no failure.

No stop line is hit.

## 5. Split (answer (1)): **confirmed as pre-signed**
- T1a = `Step2IterGen` + `Step2IterGen2`: targets 1-6, central 1,586 ≤ 1,950.
- T1b = `OptL2Gen` + `Step2CloseGen`: targets 7-11 with target 9 in `Step2CloseGen`, central 1,904 ≤ 1,950 (slack 46). T1b goes on `t/T2478b`, stacked on `t/T2478`, and merges after T1a.
- Row 3,490 < 3,900: no third row, no REQ.
- Role of 1b: `prover-hard` (answer (2)).
- The 1b also rewrites the owner texts of `BATwistAvgLaw`/`BATwistLoopLaw` (answer (6)).

## 6. Verdict: **PASS** (section (a) with (a′); no dispatcher sign-off needed: answers (1), (3) decide)
Target 9 is go under answer (3), and the pre-signed split T1a (targets 1-6) / T1b (targets 7-11) is restored and confirmed. Every stage-1a deliverable is met and no binding stop line is hit.

## 7. Observations (no RETURN)
- O1 (T1-BA ticket, carried from round 1): the check-file BA shape for target 1 (`stNewKLKgL'_ba` at `sz.withLam g₀` with `STprof(g₀) ≤ A·STprof sz`) does not transport the Ĵ-form conclusion: the reverse ratio grows with `L` (3.6 → 3.8e48, reproduced §1). (a) row 17's route through F7 (≈60 lines) is a T1-BA obligation, not verified here. T1's pins are unaffected.
- O2: (iv) gives the shapes as a substitution map over band statements; the stage-2 auditor diffs target 7 through that map.
- O3: the ticket's registry line numbers are stale on `main` 08daf959. `BATwistAvgLaw`/`BATwistLoopLaw` are at `Test/Axioms.lean:192-193`, not `:195-196` (grep in round 1, re-run now: `192:`, `193:`). The 1b edits them by name.
- O4: under the TLC-4 upper reference of 2.6× own central, three files exceed 2,000: `Step2IterGen` 2,899, `OptL2Gen` 2,854, and now `Step2CloseGen` with target 9 at 2,096. T1b at 2.6× is 4,950. The stop line and the reserve rule are central-based. In T1b, `Step2CloseGen` is the last file of the row and has no reserve sibling; if it runs past 1,800 during 1b, the reserve rule cannot hand target 11 on, so the 1b stops and reports. This is a risk note, not a stop.
- O5: T1b's 1,904 against the 1,950 split threshold leaves 46 lines of slack. Target 9's itemised range is 400/740 (row 16). At the high end T1b is about 2,120 centrally, which is still below the 3,900 REQ line.
