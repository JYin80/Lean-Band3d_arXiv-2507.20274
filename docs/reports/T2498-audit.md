Auditor model: claude-opus-5-5

# T2498 audit, round 2: row a, first part (U3s3a: `QProxy`, `QProxy2`, `QDriftA`, `QDriftB`, `QLevelsA`, `QLevelsB`; targets 1-6 and their part of 9)
Written Wed Oct 14 04:16:37 UTC 2026. `t/T2498` 5e8ef75a (unchanged since round 1; the repair was report-only), merge-base 3f945e60,
`main` bbb1fd30; fresh worktree `RBM3D-wt/T2498-audit2`; scratch `$S` = scratchpad `T2498/`. Scope as round 1: U3s3a′ (`QBudgetA/B`,
`QEndA`, `QEndA2`: targets 7, 8, the rest of 9, D2) and rows b, c are later stacked rows and are not audited here. Amend 1 applies.

## 0. Round-1 item (paper-delta gap for D1): `T2498f` in prove report (d), line 296
```
$ python3 -I $S/t2498f.py      # each item of round-1 "Required" item 1 searched in the `T2498f` line
present `1 < W` | `L^d ≤ W^{KL}` | `0 < ε < 1` | `1 < D` | `4 ≤ W^ε` | `log L ≤ W^ε` | `0 ≤ s ≤ t ≤ 1 - gK²/L²` | `W⁻¹ ≤ (1-t)/(1-s)`
present every `σ : Fin k → Bool` | `EKFastDecay (gK n) s W ε D A` | `EKSumZero` | W^{C4 ε} ((gK²+|1-s|)/(gK²+|1-t|))^k ‖A‖ + W^{-D+C4}
present `∃ C4` after `(k, κ, ε, 𝔡, KL)` and before `(sz, z)` | ∀ᶠ n | `qProxyG_kerEK4_band` | qProxy4C d k 𝔡⁻¹ (min κ (4/5)) KL
present `baEKSumDecay2_holds` | D717 (a) | 3_5_Loop_Hierarchy.tex:1659            (19 / 19 present)
$ grep -n "label{sum_res_2}" paper/tex/3_5_Loop_Hierarchy.tex  ->  1659:  \begin{align}\label{sum_res_2}
$ sed -n 1770,1772p RBM3D/BA/EKSum.lean  ->  theorem baEKSumDecay2_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecay2 d n Λ κ := by
$ sed -n '88p;241p' RBM3D/Probe/T2498Pins.lean  ->  both lines `obtain ⟨C, hC, hEK⟩ := baEKSumDecay2_holds d k … KL hKL`
```
I compared each clause of `T2498f` with `QProxy.lean:680-696` (§1). They agree. The paper's `(sum_res_2)` (`3_5:1655-1662`, sum-zero `A`,
every `σ`, `C_n` independent of `ε, D`) has no `KL`, `log L ≤ W^ε`, `W⁻¹` window or explicit `gK`. `T2498f` records those extra
hypotheses. The gap is closed.

## 1. Statements
D1 (target 1) against the check (`def` to blank line, whitespace collapsed, `T2498_` → `QProxyG_`), then compiled:
```
$ python3 -I $S/d1diff.py
T2498_KerEK4 vs QProxyG_KerEK4 : IDENTICAL 685 685
T2498_KerEK4Fam vs QProxyG_KerEK4Fam : IDENTICAL 398 398
$ cat $S/G1check.lean   # check's two defs (T2498-check.lean:213-232) copied verbatim into namespace RBM.BA, then:
example : @RBM.Ind.QProxyG_KerEK4 = @T2498_KerEK4 := rfl
example : @RBM.Ind.QProxyG_KerEK4Fam = @T2498_KerEK4Fam := rfl
example : ∀ d : ℕ, T2498_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam) :=
  RBM.Ind.qProxyG_kerEK4_band
$ lake env lean $S/G1check.lean; echo "exit $?"   ->  G1check exit 0 ; grep -c error -> 0
```
Family quantifier order: `3 ≤ d → ∀ k ≥ 2, ∀ κ ε 𝔡 KL > 0, ∃ C4 > 0, ∀ sz 𝔠 z, Flow → ∀ᶠ n`. This matches ticket D1 (`∃ C4` after
`(k, κ, ε, 𝔡, KL)`, before `(sz, z)`).
Targets 2-6: I extracted the 32 generic statements (`$S/genscan.py` → `$S/genstmts.txt`) and read them against ticket targets 2-6 and
UBA-C1. Spot reads:
- `alt_hkerQNg` (`QDriftA:596`) takes the EK-4 input through D1 `hKer : QProxyG_KerEK4 C gK k KL C4 n`. It adds R1 `hcmp`
  (`∀ m, gK² ≤ lam² ≤ A gK²`), `1 ≤ A`, `C4 ≤ Cv`, `A^k ≤ W^{(Cv-C4)ε}` and `d√A W^τ' ≤ W^ε`. Window and output stay at `sz.lam`
  (UBA-C1 rows 3-4). `ugenPairQNg_le_of_bounds` (`QProxy:1103`) has the same R1 shape, plus `GridRepTailGen_Ker` and two radii `ε₁, ε`.
- `altB4Ng_fastDecay` (`QDriftB:683`) reads per carrier `Step5KerGen_ThDecay Cm.toFlowFM gK Λg C₆`, R1 and `0 < gK n ≤ Λg`. Its
  conclusion is `∃ W₀ … ∀ sz` (band shape). There is no family premise in this part, so Amend 1 (`∃ C₆` after `κ`) applies only to row c.
- `altB45Ng_levelM` (`QLevelsA:455`) takes the fields of `B45Gen_Facts` (`B45Gen:61`) at one index: `hward`, `hker`, `him1`,
  `hrow`/`hcol` with `K₆/(1-t)`, and `Γ = κm⁻¹`. These are weaker premises than the family class, and no `|E|` appears.
- `yMomentsQUnifNg` (`QProxy:1591`): carrier classes `LoopForm`, `WalkForm`, `∀ n GridRepTailGen_Ker`, `DecayGen_Spec`. There is no
  drift or hierarchy premise.
```
$ python3 -I $S/genscan.py     # C1 / X1-C1 regex of T2498.md:92 over the 32 generic statements
HIT QDriftA 121 altB4Ng ThetaN   (x2)   -> `Step2Gen_ThetaN` (the generic Θ; `ThetaN\b` substring)
HIT QDriftA 137 dFlowQNg Lloop   (x3)   -> `KLloopOf` (Loop/KLTree.lean:149, model-free label list)
statements extracted 32 of 32          ; no band hit
$ grep -c "∀ (sz : Sizes d)" $S/genstmts.txt -> 4: QProxyG_KerEK4Fam (family row 8); altB4Ng_fastDecay, altB5Ng_fastDecay_moll,
  alt_hDclsQNg (conclusion `∃ W₀, ∀ sz`, band shape; not premises)
$ python3 -I $S/decls.py       # every declaration of the 5 in-place files, main vs t/T2498 (QProxy2 searched for moved ones)
main def/abbrev/structure in 5 files: unchanged 50 edited [] removed []
main public theorems 89 removed [qv_at_propagatorQ, azumaSubGQ_ugenN, ugenPairQN_le_of_bounds, + 4 *_instance]
header changed [('QProxy', 'azumaSubGQ_gridExitN')]
```
`azumaSubGQ_gridExitN` changed only from ` :=` (term proof) to `:= by` (tactic proof). The binders and type at `main:409-419` and
branch `:535-545` are identical. The three removed band theorems have 0 readers outside `QProxy.lean` on `main` (`git grep -l -w`). No
band `def` is edited, no `structure` is new, no pinned `∃` comes after `(sz, z)`, there is no `∀ n` drift premise, and no private name
was made public.

## 2. G1 (Part 3) and band readers
The Part-3 names in this part's files are `zVecQN`, `yVecQN`, `kappaAltQN`, `epsAltQN` (defs) and `qProxy4C_pos`, `yMomentsQUnifN`,
`startLevelQN` (theorems). `decls.py` above shows the def bodies unchanged and the theorem headers identical to `main`. The other
Part-3 names live in files this part does not touch (`git diff --name-only` below).
The band readers are rebuilt unchanged in the build of §4: `QBudgetA`, `QBudgetB`, `QEndA`, `QEndGrid`, `QEndB1`, `QtXiRoundLift`,
`Step3`, `Step4`, `MainIndOut`, `MainIndHolds`, `Main/BandTerminal`.

## 3. Compiled nonempty instances (`$S/instuse.py`: for each `*_instance`, does its proof apply the target?)
```
QProxy2:44 qProxyG_kerEK4_band_instance -> 1 | :50 martIncQNg_ae_eq -> 1 | :72 qv_at_propagatorQg -> 1 | :129 azumaSubGQ_ugenNg -> 1
QProxy2:147 azumaSubGQ_gridExitNg_instance_zero -> 1 | :223 yMomentsQUnifNg_instance_pos -> 0 | :242 yMomentsQUnifN -> 1
QProxy2:414 ugenPairQNg_le_of_bounds -> 1 | :703 qvFormQNg_le_of_bounds -> 1
QDriftA:1645 dGridQNg_eq_dFlowQNg -> 1 | :1652 dFlowQNg_sumZero -> 1 | :1668 fastDecay_of_diamInfg -> 1 | :1695 hker_altQNg -> 1
QDriftA:1732 alt_hkerQNg -> 1 | :1765 goodSetNg_A0clsQNg -> 1 | :1824 alt_hA0clsQNg -> 1
QDriftB:1485 drift13_fastDecayg -> 1 | :1505 altB4Ng_fastDecay -> 1 | :1529 altB5Ng_fastDecay_moll -> 1 | :1550 dFlowQNg_clsQNg -> 1
QDriftB:1600 alt_hDclsQNg -> 1 | :1671 qDriftB_thDecay_band_concl -> 1 | QLevelsA:863 altB45Ng_levelM -> 1 | :891 startLevelQNg -> 1
QLevelsB:520 goodSetNg_LKM_far -> 1
```
`yMomentsQUnifNg` is applied in the proof of `yMomentsQUnifN` (`QProxy:1615`; `QProxy:1628` applies `yMomentsQUnifNg
(stepDecompGen_loopForm_band …) (stepDecompGen_walkForm_band …)`). That theorem has the instance `QProxy2:242`, so every carrier
hypothesis is discharged at `bandStep2Mat sz E`. Data read in `alt_hkerQNg_instance` and `altB4Ng_fastDecay_instance`: `d = 3`,
`k = 4`, `n = 9` or `n ≥ W₀`, `W > 1` large, and windows `u_i = i/2` with `K = 1`. The tensor is `Xsz 9 ≠ 0` (sum-zero), the window is
attained (`∃ b i j, W^{1/5} ellT ≤ dist`), D1 comes from `qProxyG_kerEK4_band_at`, and the Θ-decay from `step5KerGen_thDecay_band`.
R1 is used at `A = 1`, `gK = sz.lam`. `H = 0` gives `STLKMg = STLMg(0) − K`, which is not identically zero (the same data as the band
`altB4N_fastDecay_instance` on `main`). There is no `N = 0`, empty index, collapsed window or `False` premise.

## 4. Build, axioms, diff, layering
```
$ lake build RBM3D RBM3D.Induction.QProxy2 RBM3D.Probe.T2498Pins     # Wed Oct 14 04:12:22 -> 04:15:32 UTC 2026, exit 0
info: RBM3D.lean:606:0: axiom audit: 14981 theorems, 4636 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 124 (borrowed 1, owed 57, structural 46, refuted 6, superseded 14).
Build completed successfully (4378 jobs).        ; grep -c error build.log -> 0 ; "declaration uses 'sorry'" -> 0
warnings in the 6 files + probe: longLine (41), `show` linter (3) only
$ lake env lean $S/ax.lean       # collectAxioms over every non-internal constant of the six modules
modules found 6; declarations 189; [([Classical.choice, Quot.sound, propext], 188), ([Quot.sound, propext], 1)]
$ lake env lean docs/tickets/checks/T2498-check.lean (audit worktree) -> check exit 0 ; error lines 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" <six files> RBM3D/Probe/T2498Pins.lean | wc -l  ->  0
$ grep -nE "import RBM3D.BA|STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds|withLam" <six files> | wc -l  ->  0
$ git diff --name-only main...t/T2498
RBM3D/Induction/{QDriftA,QDriftB,QLevelsA,QLevelsB,QProxy,QProxy2}.lean  RBM3D/Probe/T2498Pins.lean        (all sole writable)
$ git diff --stat main...t/T2498 -- Induction/{QEndGrid,QEndB1,QtXiRoundLift,QGridA,QGridB} 'Induction/NQ*' 'Chain/NQ*' BA RBM3D.lean Test | wc -l -> 0
$ git merge-tree --write-tree --name-only main t/T2498  ->  cef9d4db…, exit 0
$ wc -l: QProxy 1644, QProxy2 838, QDriftA 1893, QDriftB 1679, QLevelsA 914, QLevelsB 618 (all < 2,000); probe 397 (≤ 400)
$ grep -rln "import RBM3D.Induction.QProxy2" RBM3D RBM3D.lean  ->  (none; the hub adds the root import)
$ python3 -I $S/clash.py  ->  new public names 66 ; names found on main outside the six files: []
```

## 5. Paper deltas
`T2498a` covers the R1 constants and the two radii, `T2498b` the `!σ` product in `qvFormQNg`, `T2498c` the seven removed band
declarations, and `T2498d` the frozen-carrier `B45_det2g` route with `Γ = κm⁻¹`. `T2498e` covers `C₆` per carrier, with the family
order after `κ` (Amend 1, D721). `T2498f` (new) covers D1, the EK-4 class `QProxyG_KerEK4(Fam)` (§0). I found no uncovered statement
difference.

## Verdict per target
| target | statement | hyp./vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 D1 `QProxyG_KerEK4(Fam)`, band discharge | = check (rfl) | ok | ok | ok | ok (T2498f) | PASS |
| 2 `QProxy` §2-§5 vocabulary | ok | ok | ok | ok | ok (T2498b) | PASS |
| 3 `QProxy` §7-§10 | ok | ok | ok (via `yMomentsQUnifN`) | ok | ok (T2498a, f) | PASS |
| 4 `QDriftA` §1-§5 | ok | ok | ok | ok | ok (T2498a, f) | PASS |
| 5 `QDriftB` | ok | ok | ok | ok | ok (T2498e) | PASS |
| 6 `QLevelsA/B` | ok | ok | ok | ok | ok (T2498d) | PASS |
| 9 (this part) band corollaries, instances | G1 unchanged | ok | ok | ok | ok (T2498c) | PASS |

**Overall: PASS** for U3s3a, first part. U3s3a′ (targets 7, 8, the rest of 9) and rows b, c are still to come.

### Observations (no verdict change)
- O1. Four new `open private` lines: `QProxy:81` (`Chain/NQGood1Gen`), `QDriftB:43-44` (`Induction/QopDecay`, `Chain/Step5KerGen`),
  `QLevelsA:38` (`Induction/B45`). None opens one of the ten Q files, so the ticket rule (`T2498.md:22`) holds. They affect proofs
  only. Round 1's "no `open private`" was inaccurate.
- O2. `yMomentsQUnifNg_instance_pos` (`QProxy2:223`) applies the body `qProxy_yMomentsQPosg`, not the target. Report (b) lists it as
  the target's instance. The target is covered through `yMomentsQUnifN_instance` (§3).
- O3. Calibration: added − moved = 2,256 against the 1a central of 1,229, and `QDriftA` is at 1,893 lines (round 1 O1).
  The prove report is 298 lines: within CLAUDE.md §6 (300) but over the ticket's 250 (`T2498.md:107`).
- O4. At merge: do not bring in `RBM3D/Probe/T2498Pins.lean` (`t/T2498` only). Add `import RBM3D.Induction.QProxy2` to the root.
  The `Test/Axioms.lean` `GoodSetNg` owner text is deferred to row a′ (it names `hQ_altQNg`).
- O5. `docs/tickets/checks/T2194-check.lean:182, 206` `#check`s the removed `qv_at_propagatorQ`, `azumaSubGQ_ugenN` (an old check,
  never built; recorded under `T2498c`).
