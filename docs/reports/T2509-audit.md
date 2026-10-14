Auditor model: claude-opus-5-5

# T2509 audit (round 1): U3-BA (b), Steps 3-4 at the BA tuple; `Chain/Step34RGen`, `BA/Step34BA`

Audit started `Wed Oct 14 15:02:12 UTC 2026` (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2509-audit1`, detached at `t/T2509` = 0768f64d (merge base with `main` = b4147edc).
Scratch (uncommitted): `<scratchpad>/T2509/pins.lean` (the check's imports and Part 2 verbatim, `#check` lines dropped, plus 16 `example : T2509_X := <name>` and 25 `#print axioms`), `kernz.lean` (T2507-check:185-203 verbatim plus two examples).

## 1. Build (audit worktree)
```
$ lake build RBM3D.Chain.Step34RGen RBM3D.BA.Step34BA
⚠ [4181/4182] Built RBM3D.Chain.Step34RGen (11s)
⚠ [4182/4182] Built RBM3D.BA.Step34BA (5.6s)
warning: RBM3D/BA/Step34BA.lean:41:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (4182 jobs).            (exit 0; no `error` line)
```

## 2. Statements against the pins (compiled, not eyeballed)
```
$ lake env lean docs/tickets/checks/T2509-check.lean        -> exit 0, 0 lines matching "error"
$ lake env lean <scratch>/pins.lean                          -> exit 0, 0 lines matching "error"
  example : ∀ d law Flow mkM Hf Es T0, T2509_Step3RegIIIOf d law Flow mkM Hf Es T0 := stStep3RegIIIgL_of
  example : ∀ d law Flow mkM Hf Es T0, T2509_Step3RegIOf d law Flow mkM Hf Es T0 := stStep3RegIgL_of
  example : ∀ d law Flow mkM Hf Es T0, T2509_Step3IIOf d law Flow mkM Hf Es T0 := stStep3IIgL_of
  example : ∀ d R law Flow mkM Hf Es T0, T2509_Step4ROfIng d R law Flow mkM Hf Es T0 := stStep4RgL_of_ing
  example : ∀ d R R' law Flow mk T0, T2509_Step34Mono d R R' law Flow mk T0 := stStep34RgL_mono
  example (d : ℕ) : T2509_KerNZBA d := baQtNZGen_kerNZ d
  example (d : ℕ) : T2509_OeqQtBA d := baOeqQtgL'_holds d
  example (d : ℕ) : T2509_OeqQtNZBA d := baOeqQtNZgL'_holds d
  example (d : ℕ) : T2509_Step3RegIIIBA d := baStep3RegIII_holds d
  example (d : ℕ) : T2509_Step3RegIBA d := baStep3RegI_holds d
  example (d : ℕ) : T2509_Step3IIBA d := baStep3II_holds d
  example (d : ℕ) : T2509_Step4IBA d := baStep4I_holds d
  example (d : ℕ) : T2509_Step4IIBA d := baStep4II_holds d
  example (d : ℕ) : T2509_Step4RegIIIBA d := baStep4RegIII_holds d
  example (d : ℕ) : T2509_Step4RegIBA d := baStep4RegI_holds d
  example (d : ℕ) : T2509_shape_V2aRead d := ⟨⟨baStep3RegIII_holds d, baStep4RegIII_holds d⟩,
      ⟨baStep3RegI_holds d, baStep4RegI_holds d⟩, ⟨baStep3II_holds d, baStep4II_holds d⟩⟩
$ lake env lean <scratch>/kernz.lean   (T2507-check.lean:185-203 verbatim)  -> exit 0, 0 lines matching "error"
  example (d : ℕ) : T2507_KerNZBA d := baQtNZGen_kerNZ d
  example : @QtNZGen_KerNZFam = @T2507_KerNZFam := rfl
```
Every target elaborates against its `T2509_*` pin by plain term (no unfolding tactic), so hypotheses, quantifier order, the
`∃ 𝔠d` / `∃ C5` positions, regimes and windows are exactly the pinned ones. Target 6 also equals T2507's pin (`rfl` on the class).
Generic targets 1-5 take only `IterationsGen2_Fam` (Decision (8)) plus the input pins the ticket names; no `|E| < 2`, `etaT`, or `STAny` statement.

## 3. Vacuity, hidden hypotheses, cycles
```
$ grep -nE '^(noncomputable )?(def|abbrev|structure|class|instance) ' <both files> | wc -l      -> 0
$ C1 grep 'mE\b|norm_mE|\|E\||SB d|BAK_le_small|BAMB_upper_small|Mbound_AO|W\^\(-eps|BAm_im_lower_window|STGridRepNgL' <both> -> (no output)
$ grep -n withLam <both> | grep -vE 'seqP \((sz|sz0|szI|TwistStep2_szII)\.withLam 0\)'          -> (no output)
$ awk 'NR<535 && /STFlow|STflowE|etaT|bandFM|bandStep2Mat|lemT/' Chain/Step34RGen.lean
531: The band family `(seqP, STFlow, bandStep2Mat · (STflowE ·), seqHflow, STflowE, lemT)`: the bundle is ...   (module doc of §5, not code)
$ grep -c '^import RBM3D.BA' Chain/Step34RGen.lean                                                 -> 0
```
- No new structure/class; the only bundle premise is the merged `IterationsGen2_Fam`, discharged at BA by `baIterationsGen2_fam d` (`baStep3*_holds`, `baStep4I/II_holds` above) and at the band by `IterationsGen2_famBand 3` (instances). Not a `False` bundle.
- Targets 7 (a)/(b) use merged producers `stOeqQtgL'_of` / `stOeqQtNZgL'_of` with every slot a merged BA lemma or a private `Step34BA_h*` proved in-file (`Step34BA.lean:81-117`); `d < 3` is the pin's own `3 ≤ d →` (`by_cases`, absurd). Targets 8-9 chain 1-5, 7 and the merged `baSTIterations(II)gL'_holds`. Dependency order: file 1 → file 2; no cycle (file 1 imports no `BA/*`).
- `(con_st_ind)` is discharged for every produced `𝔠d > 0` by the merged limit lemma `conStInd_const` (`W_n → ∞`), not by a numeric witness (lesson 14 satisfied).

## 4. Compiled nonempty instances (in the target files; built in §1)
| target | instance (file:line) | data (d = 3) | left as hypotheses |
|---|---|---|---|
| 1 | `inst_step3RegIIIgL` Step34RGen:621 | band family, `sz0`, `z0`, `sInst,tInst`, `sz0_regIII`; `STKbound/Kward` via `stKbound/Kward_of_flow` | STLKgL, STStep1LoopgL, STStep2ConclgL |
| 2 | `inst_step3RegIgL` :638 | `szB` (`L=4, W=n+4`), `(7/8, 15/16)`, `szB_regIterI`; pins `stOeqQtgL'_band3`, `stIterationsgL'_of` | same |
| 3 | `inst_step3IIgL` :657 | `szB`, `(15/16, 31/32)`, `szB_caseII`; `stOeqQtNZgL'_band3`, `stIterationsIIgL'_of` | same |
| 4 | `inst_step4RgL` :676 | `R = STCaseI`, `sz0`, `sz0_caseI`; ingredient `stOeqQtgL'_band3` | + STLmaxUgL (Step 3 output) |
| 5 | `inst_step34Mono` :694 | `STCaseI → STReg5III`, applied to `stStep4I_holds_of_gen 3` at `sz0` | same as 4 |
| 6 | `inst_baQtNZGen_kerNZ` Step34BA:290 + `example` :301 | `k = 3`, `(κ,𝔡) = (1/2,1/10)`, `(sz0, zSeq, flow_sz0)`; concrete `n`, `v = w = 1 - 3g₀²/L²` (`0 ≤ v ≤ w < 1` proved), `σ = (+,-,+)`, `X ≡ 1` | none |
| 7a | `inst_baOeqQtgL'` :335 | datum A: `sz0`, `zSeq`, `s≡1/2 < t≡2/3 ≤ T₀` (`t0_sz0`), `STCaseI` from `Step34BAInst_regIII`; `baKbound/Kward_holds` | STLKgL, STStep2ConclgL |
| 7b | `inst_baOeqQtNZgL'` :347 | datum C: `TwistStep2_szII`, `(0, 1/2000)`, `szII_caseII` | same |
| 8 (iii)/(i)/(ii) | :359 / :372 / :385 | A / B (`szI`, `(0, 1/400)`, `szI_window`, `Step34BAInst_regI`) / C | STLKgL, Step1Loop, Step2Concl |
| 9 (i)/(ii)/(iii)/(iv) | :398 / :412 / :426 / :440 | A / C / A / B | + STLmaxUgL |
Every deterministic premise (flow, `0 ≤ s`, `s < t`, `t ≤ T₀`, regime, `STKboundgL`, `STKwardgL`, `(con_st_ind)`, window) is a term in the instance; what remains is another gate's pin (Step 1/2 conclusions, `STLKgL`, Step 3's `STLmaxUgL`). No `N = 0`, empty window or `False` premise: regimes (i), (ii) are put on data where they hold (`sz0` has none, `TwistStep2_no_caseII_sz0`), `s < t < 1` constant in each datum, `W_n → ∞`.

## 5. Axioms
```
$ #print axioms (25 declarations: the 15 targets, Step34RGenCheck.stStep3RegIII/stStep4II_holds_of_gen, 4 file-1 instances, 5 file-2 instances)
25 of 25 lines: '<name>' depends on axioms: [propext, Classical.choice, Quot.sound]   (0 other "depends on" lines)
$ grep -nE "sorry|admit|native_decide|^ *axiom " Chain/Step34RGen.lean BA/Step34BA.lean | wc -l   -> 0
```

## 6. Diff scope, G1, registry
```
$ git diff --name-only main...t/T2509
RBM3D.lean
RBM3D/BA/Step34BA.lean
RBM3D/Chain/Step34RGen.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2509 -- RBM3D/Induction RBM3D/Chain/Step34Gen.lean RBM3D/Chain/IterationsGen2.lean | wc -l   -> 0
$ git grep -nE 'import RBM3D\.(Chain\.Step34RGen|BA\.Step34BA)' t/T2509 -- RBM3D RBM3D.lean
t/T2509:RBM3D.lean:632:import RBM3D.Chain.Step34RGen
t/T2509:RBM3D.lean:633:import RBM3D.BA.Step34BA
t/T2509:RBM3D/BA/Step34BA.lean:6:import RBM3D.Chain.Step34RGen
$ wc -l   -> 739 Chain/Step34RGen.lean (stop 1250), 455 BA/Step34BA.lean (stop 800)
```
`RBM3D.lean`: +2 import lines after the last import, `#assert_rbm_axioms` stays last. `Test/Axioms.lean` (`git diff`, read): owner texts of `STLmaxUgL`, `STLKUgL`, `STXiRoundgL'` rewritten as the ticket's Registry paragraph; `STXiBootgL'` removed with a `-- T2509 ... left this list` comment, the branch the ticket pre-signs (Decision (6): "if the pre-scan already lists `STXiBootgL'` as carrying nothing"; prove report b6 pastes "before True"). No other line touched. No frozen signature changed (all merged files untouched).

## 7. Paper deltas
Prove report (d): no candidate. Lean/paper differences present: Steps 3-4 pinned per regime predicate, no general/`STAny` form (covered by **D51**, D56; DECISIONS §331 (2)); D1 in A-form `(1 − v)L² ≤ Aof κ g₀²` with `Aof κ = (κ+1)/κ` (covered by **D730** (ba), T2505; the constant is the merged `TwistStep2_lam0_sq`). Targets themselves introduce no new statement form (pins = merged `STStep3RgL`/`STStep4RgL`/`STOeqQt*gL'` at the BA tuple). Coverage complete.

## 8. Observations (no RETURN)
- O1. Against current `main` (d1839622, after T2508 merge 57178a34) `git merge-tree --write-tree main t/T2509` reports `CONFLICT (content): Merge conflict in RBM3D.lean` (both rows append imports at the same place); `Test/Axioms.lean` auto-merges. CONTROL H311 already prescribes the import union at merge.
- O2. `BA/Step34BA.lean:41` long-line warning (module doc before the `set_option`); cosmetic.
- O3. Instances of target 4/9 keep `STLmaxUgL` as a binder instead of chaining the Step 3 instance; allowed (Step 3's conclusion under other gates' pins).
- O4. Regime-(i) instances read the private `szI`/`flowI` of `BA/ZeroModeBA` through `open private` (no merged file edited); a later change of that private datum would break them (noted in prove report (d)).

## Verdict
| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `stStep3RegIIIgL_of` | = pin | ok | :621 | ok | D51 | PASS |
| 2 `stStep3RegIgL_of` | = pin | ok | :638 | ok | D51 | PASS |
| 3 `stStep3IIgL_of` | = pin | ok | :657 | ok | D51 | PASS |
| 4 `stStep4RgL_of_ing` | = pin | ok | :676 | ok | D51 | PASS |
| 5 `stStep34RgL_mono` | = pin | ok | :694 | ok | none needed | PASS |
| 6 `baQtNZGen_kerNZ` | = pin, = T2507_KerNZBA | ok | :290, :301 | ok | D730 | PASS |
| 7 `baOeqQtgL'_holds`, `baOeqQtNZgL'_holds` | = pins | ok | :335, :347 | ok | none needed | PASS |
| 8 `baStep3RegIII/RegI/II_holds` | = pins | ok | :359, :372, :385 | ok | D51 | PASS |
| 9 `baStep4I/II/RegIII/RegI_holds` | = pins | ok | :398, :412, :426, :440 | ok | D51 | PASS |
| 10 instances | — | — | all compile | ok | — | PASS |

**T2509: PASS.** No dispatcher sign-off needed.
