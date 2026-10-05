Auditor model: claude-opus-5-5

# T2204 (S6-01) audit, round 1 — `RBM3D/Induction/Step6Pins.lean` + registry

Written Mon Oct  5 19:38:59 UTC 2026. Branch `t/T2204` at a0e4ad8 (base b3c37aa); audit worktree `RBM3D-wt/T2204-audit1` (detached a0e4ad8).

**Verdict: PASS** (every target). Observations O1–O2 change no statement, instance, build, axiom or paper-delta coverage.

## 1. Scope: files touched
```
$ git diff --stat main...t/T2204
 RBM3D/Induction/Step6Pins.lean | 734 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |  44 ++-
 2 files changed, 776 insertions(+), 2 deletions(-)
$ git merge-tree --write-tree main t/T2204 >/dev/null; echo $?   # main = 98e6d5b
0
```
Only the two sole writable files. No frozen signature touched (Axioms.lean: only `]`→`,` on the two former last entries plus 40 appended lines, §4).

## 2. Statement: verbatim move of the ten signed probe blocks (Targets 1)
```
$ git show 96c6b4c:RBM3D/Probe/T2191Pins.lean > probe.lean; python3 verb.py   # block in text, in order; uncovered nonblank lines as ranges
:46-165 True in-order lines 120
:401-717 True in-order lines 317
:1644-1646 True in-order lines 3
:1737-1836 True in-order lines 100
:1838-1843 True in-order lines 6
:1860-1906 True in-order lines 47
:2077-2127 True in-order lines 51
:2226-2229 True in-order lines 4
:2259-2279 True in-order lines 21
:2281-2289 True in-order lines 9
file lines 734
--- lines of file not in any block: 1-9, 11-12, 14-17, 19-26, 29, 31, 33-34, 475, 477, 479, 485, 643, 734
$ diff <(sed -n 39,44p probe.lean) <(sed -n 29,34p file.lean) && echo ...; (same for 1550-1554 / 475-479, 1-5 / 1-5)
probe:39-44 == file:29-34
probe:1550-1554 == file:475-479
copyright equal
```
Every non-block line is in the allowed set (copyright, 4 imports per Targets 2, module docstring, `:39-44`, scaffolding `:1550-1554`, `end` lines). Imports: `Step5Pins`, `LWPins`, `ZeroModeCalc`, `QopAlgebra` (Targets 2 minimum; never `RBM3D`/`Probe`).

### Check-file equality (46 vocabulary/pin defs, compiled)
```
$ { sed -n 21,31p T2204-check.lean; echo "import RBM3D.Induction.Step6Pins"; sed -n 32,416p T2204-check.lean;
    for X in $(defs of section 2): echo "example : @RBM.Gauss.Sizes.T2204Check.X = @RBM.Gauss.Sizes.X := rfl"; } > T2204AuditEq.lean
$ grep -c ^example T2204AuditEq.lean; lake env lean T2204AuditEq.lean; echo exit $?
46
exit 0   (no output)
```
Defs: STExpErr STExpELKLK STExpEGt STExpDrift STExpTarget STExp2U STStep2Core STIngR6 STStep6Concl STStep6R STStep6I STStep6II STStep6III STStep6IV STStep6 STExpAvgAt STImproveExpAver STExpAvgU STExpHier STExpDuhamelZ STExpQsrc STExpDuhamelQ STExpDuhEq STExpDuhEqQ STDriftHi STExpLKLKHiConcl STExpLKLKHi STExpEGtHiConcl STExpDriftHiConcl STExpDriftLoConcl STExpDriftLo STExpDriftDecayConcl STExpDriftDecay STExpWardIConcl STExpWardI STExpWardIIConcl STExpWardII STExpIntConcl STExpIntQConcl STExpIntIII STExpIntIV STExpIntII STExpIntI STExpIniIConcl STExpIniI STRegSeq 

### Pin content spot checks against the paper
```
$ python3 difflib on whitespace tokens: Defs.lean:159-165 (STExp2) vs Step6Pins STExp2U (6 lines); non-equal opcodes
replace: 'STExp2' -> 'STExp2U'
replace: 'τ' -> 's t'
insert: '' -> 'TimeIcc s t n ×'
replace: '(τ n) p.1 p.2' -> '(p.1 : ℝ) p.2.1 p.2.2'
replace: '(τ n) p.1 p.2‖)' -> '(p.1 : ℝ) p.2.1 p.2.2‖)'
replace: '_' -> 'p'
replace: '(τ n))' -> '(p.1 : ℝ))'
replace: '(τ n)))' -> '(p.1 : ℝ)))'
```
`STExp2U` = merged `STExp2` with `τ n` replaced by `u ∈ TimeIcc s t n` inside the index set: `(Eq:Gtlp_exp_flow)` `1_2:1392-1396` "∀ u ∈ [s,t]" (D489). `STExp2_of_STExp2U` = "Hence (Eq:Gtlp_exp) holds at time t" (`1_2:1396`). `STExpLKLKHiConcl`: `(1-u)⁻¹ (Bctl)^{11/5}` = `(eq:Exp(L-K)1)` `6:60-61` (`Bctl n u = W^{-d} B_{u,0}`, `Defs/Sizes.lean:214-215`); `STDriftHi` `λ²/L^d ≤ 1-t` = window `6:58` (`1-u ≥ 1-t`). `STIngR6`: quantifier order `3 ≤ d → ∀ κ ε 𝔡 → ∃ 𝔠d ∈ (0,1/100] → ∀ 𝔠 sz z, STFlow → ∀ s t, 0 ≤ s, s < t, t ≤ lemT z, R, premises at s, con_st_ind, Steps 2–5 → Concl` (`lem:main_ind` order, `1_2:1281`); differences from `STIngR5` = D486. `STStep6I..IV` = `STStep6R d STReg5I..IV` (merged regimes, `6:94-97`); `STStep6 = STStep6R d STAny`. All pins were signed under DECISIONS §67 after the T2191 audit; the preflight (prove report (a)) records PASS for all 40.

## 3. No vacuity, hidden hypothesis or cycle
- No `structure`/`class` declared in the file; every pin is a `def … : Prop` whose hypotheses are in its body (read: `STIngR6`, `STStep6*`, `STExp2U`, `STDriftHi`, `STRegSeq`).
- Dependencies are merged files only (4 imports, all on `main`); the file references no S6-02 name (verbatim blocks; ticket dependency check; compiles against `main` closure).
- External/other-gate premises are carried as hypotheses of instances only (`STStep6*`, ingredient pins, `LWAvgLaw`, `STLK` at `tInst`); none asserted.

## 4. Compiled nonempty instances
30 instance theorems compile in the file (build §5). Deterministic hypotheses discharged at concrete data: `inst_ing6_I` (`szB`: L=4, W_n=n+4, λ=1; s,t = 7/8,15/16; `flow_zB`, `szB_flow_ht`, `conStInd_const` for every 𝔠_d>0), `_II` (15/16, 31/32), `_III` (`sz0, z0, sInst, tInst` = 0, 1/16; `sz0_hs0/hst/ht/con`), `_IV` (`szG`, 5/8, 3/4); regime facts by merged `szB_reg5I`, `szB_reg5II`, `sz0_reg5III`, `szG_reg4`; `inst_duhamelZ` at s = 1/4 < t = 1/2, A = univ (Fin 2); `inst_duhamelQ` with the mollifier of `stMollifierEx_holds`; `inst_A_value` (λ²W³ = 8); index sets nonempty (`st6_idx*_nonempty`). No `N = 0`, empty index, collapsed window or `False` premise.

Theorems without an in-file instance by the ticket (`STExp2U_iff`, `STExp2_of_STExp2U`; pins `STExpLKLKHi`, `STRegSeq`): auditor scratch check (not a source edit), compiled against the branch:
```
$ cat T2204AuditInst.lean
import RBM3D.Induction.Step6Pins
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Gauss.Step6Inst
-- (A) STExp2_of_STExp2U at (sz0, z0, s = 0, t = 1/16): hst discharged; the pin STExp2U stays a hypothesis
example (h : STExp2U sz0 (STflowE z0) sInst tInst) : STExp2 sz0 (STflowE z0) tInst :=
  STExp2_of_STExp2U sz0 (fun n => (sz0_hst n).le) h
example (h : STExp2U sz0 (STflowE z0) sInst tInst) := (STExp2U_iff sz0 (STflowE z0) sInst tInst).mp h
-- (B) STExpLKLKHi at regime-(i) data, window STDriftHi discharged: lam^2/L^3 = 1/64 ≤ 1 - 15/16
example (h : STExpLKLKHi 3) :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_ing6_I STDriftHi _ h (fun n => by norm_num [szB])
-- (C) STRegSeq STReg5I STReg5II at szB, cut m = 15/16 between 7/8 and 31/32
example : STRegSeq STReg5I STReg5II szB (fun _ => 7 / 8) (fun _ => 31 / 32) :=
  ⟨fun _ => 15 / 16, fun _ => by norm_num, fun _ => by norm_num, szB_reg5I, szB_reg5II⟩
$ lake env lean T2204AuditInst.lean; echo exit $?
exit 0   (no output)
```

## 5. Build, axioms, hygiene, registry
```
$ lake build RBM3D.Induction.Step6Pins  (audit worktree; error lines / Step6Pins lines / tail)
✔ [3804/3804] Built RBM3D.Induction.Step6Pins (10s)
Build completed successfully (3804 jobs).
exit 0
$ #print axioms for the 33 theorems of the file (script-extracted names) | grep -c '[propext, Classical.choice, Quot.sound]'; other lines
33   (lines differing: 0)
$ grep -nE '(sorry|admit|native_decide)|^\s*axiom ' Step6Pins.lean; echo $?
1
$ printf 'import RBM3D\nimport RBM3D.Induction.Step6Pins\n#assert_rbm_axioms\n' > R.lean; lake env lean R.lean; echo $?   (summary lines; 254 lines total)
axiom audit: 6094 theorems, 2163 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
premises found by scanning: 129 (borrowed 1, owed 100, structural 24, refuted 4).
registry: 2 borrowed + 144 owed + 79 structural + 4 refuted; 100 registered premise(s) carry nothing yet: [...]
exit 0  (no "unregistered" line; InstIng6Concl not flagged)
$ registry diff vs ticket Targets 3 lists (python, order-sensitive); new public names vs main (git grep -lwF)
owed seq equal ticket: True | structural seq equal ticket: True | Prop pins in file: 40, registered 40, unregistered []
80 new public names, hits on main: 0
```

## 6. Paper deltas
Lean/paper differences of this file are D485–D489 (T2191a–e), present in `docs/paper-deltas.md:1444-1448`; prove report (d) cites them and proposes no `T2204a` (verbatim move, no statement change). Coverage complete.

## 7. Verdict per target and observations
- Target 1 (verbatim blocks, 46 defs equal to check file): **PASS**. Target 2 (imports): **PASS**. Target 3 (registry 20 owed + 20 structural): **PASS**. 30 instances: **PASS**.
- O1. `STExp2U_iff`, `STExp2_of_STExp2U` (theorems of Targets 1) and the pins `STExpLKLKHi`, `STDriftHi`, `STRegSeq`, `STExpEGtHiConcl` have no in-file instance, as the ticket fixes (Instances paragraph; S6-02 owes `inst_endpoints`, `inst_hiI..III`, `inst_expLKLK_I..III`, `inst_compose`). §4 scratch check shows they apply at nondegenerate data with deterministic hypotheses discharged; S6-02 must copy those instances. Same handling as T2138 audit O1.
- O2. Branch base b3c37aa ≠ main 98e6d5b; no change to `Test/Axioms.lean` or imports in between, `merge-tree` clean.
