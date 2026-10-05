Auditor model: claude-opus-5-5

# T2220 audit (round 1) — Mon Oct  5 22:39:49 UTC 2026

Branch `t/T2220` at b6fd83b (merge-base d0d79ce); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2220-audit1` (detached). Scratch: `scratchpad/T2220/`.

## 1. Diff scope and upstream drift
```
$ git diff --numstat main...t/T2220
1	0	RBM3D/Test/Axioms.lean
1053	0	RBM3D/Universality/Step1RegularityGUE.lean
$ git diff --stat d0d79ce main -- Step1Good.lean FreeConvStability.lean Pins.lean PinsDens.lean Test/Axioms.lean   (upstream drift since base)
(empty)
$ git diff main...t/T2220 -- RBM3D/Test/Axioms.lean | grep "^[+-] " | cut -c1-120
+   `RBM.Univ.Step1LocalEventGUE, -- bulk universality: the GUE-side local event (averaged law at the `UNGUELocal` preci
```
Only the two sole writable files; `Axioms.lean`: one inserted line in `structuralProps`, nothing deleted (no owed line removed). No merged file touched.

## 2. Statements against the pin (check file sections 2.1-2.5)
```
$ python3 adiff.py   (docstrings and /-! -/ comments stripped, whitespace-normalised; `RBM.Gauss.SizesInst.sz0` -> `sz0`;
   2.1: whole `def` text; 2.2-2.5: body of `def T2220_<n> : Prop :=` vs text between `theorem <n> :` and `:=`)
2.1 vGUE EQUAL
2.1 Step1LocalEventGUE EQUAL
2.1 GUEGoodAt EQUAL
2.1 UNGUELocalEventHighProb EQUAL
2.1 UNGUEDetHalf EQUAL
2.1 UNGUEGoodHighProb EQUAL
2.x gue_window EQUAL
2.x gue_window_sharp EQUAL
2.x gue_l32_exponents EQUAL
2.x guelocalEventHighProb EQUAL
2.x gue_err_pow EQUAL
2.x guedetHalf EQUAL
2.x gueGoodHighProb_of EQUAL
2.x gueGoodHighProb EQUAL
2.x inst_sz0_size_tendsto EQUAL
2.x inst_guelocalEvent_sz0 EQUAL
2.x inst_event_nonempty_sz0 EQUAL
2.x inst_guedetHalf_sz0 EQUAL
2.x inst_gueGood_sz0 EQUAL
2.x inst_gueGood_nonempty_sz0 EQUAL
```
```
$ lake env lean scratch/audit_check.lean   (import of the new module + check imports + check lines 111-251 verbatim
   + 14 lines `example : T2220_<n> := @RBM.Univ.<n>` (8 targets, 6 pinned instances) + #print axioms of all 18 public theorems)
exit 0; error lines: 0
'RBM.Univ.gue_window' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_window_sharp' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_l32_exponents' [propext, Classical.choice, Quot.sound]
'RBM.Univ.guelocalEventHighProb' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_err_pow' [propext, Classical.choice, Quot.sound]
'RBM.Univ.guedetHalf' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gueGoodHighProb_of' [propext, Classical.choice, Quot.sound]
'RBM.Univ.gueGoodHighProb' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_sz0_size_tendsto' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_guelocalEvent_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_event_nonempty_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_guedetHalf_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_gueGood_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_gueGoodHighProb_of_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_size_zero_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_gueGood_nonempty_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_exponents_sz0' [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1RegularityGUEInst.inst_gue_err_pow_sz0' [propext, Classical.choice, Quot.sound]
```
All 20 pinned texts equal; the 14 `example`s close by the library theorems (definitional, no unfolding needed). `GUEGoodAt` against the event of `UNStep1Good'` (`PinsDens.lean:78-82`, read): same `g = N^{-1+τs/4}`, `G = N^{-min(τs/4,(1-τs)/3)}`, `t = 1 - e^{-ouTStar}`, `∃ mfc, IsFreeConv32`, `∃ ρ'` density clause at `0`, bound `N^{-3τs/8}`; substitutions `vOU→vGUE`, `ρ n→rhoSC E₀`, `∃ c C, … c C (CV₀+1) → min κ 1/960, 2, 2` (fixed constants: stronger than an `∃ c C`). `ouTStar sz τU n = size^(-1+τU)` (`Pins.lean:140`), as the ticket's `t*`. Quantifier order: fixed `κ τs E₀ D` (and `τ`) before `∀ᶠ n`; `3 ≤ d`, `size → ∞` in ℕ; no `Admissible`, no `τs ≤ 𝔠𝔡`, as the ticket design (§29 (3)).

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nwE "sorry|admit|axiom|native_decide" Step1RegularityGUE.lean | wc -l
0
$ grep -nE "set_option|implemented_by|extern|unsafe|csimp" Step1RegularityGUE.lean
36:set_option linter.style.longLine false
37:set_option linter.unusedSectionVars false
$ grep -E "^(theorem|def|structure|class|instance) " Step1RegularityGUE.lean | awk '{print $1}' | sort | uniq -c
6 def; 18 theorem;
$ sed -n 6,11p Step1RegularityGUE.lean
import RBM3D.Universality.Step1Good
import RBM3D.Universality.FreeConvStability
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
$ grep -nE "UNStep1Good|UNInfty1Row|UNStep1GoodC|UNCoreC|UNTrLocalInit|UNDensBandRow|UNDens" Step1RegularityGUE.lean | cut -c1-60
26:* S7 `gueGoodHighProb`: the composition at `τ = τs/16`, the …   (comment)
62:/-- `GUEGoodAt`: the GUE-side good event (RBM2D `:78`) in t…   (docstring)
```
No structure or class carries a hypothesis; the vocabulary is plain `def`s (2.1, equal to the pin). The only external premise is the owed pin `UNGUELocal` (`Pins.lean:489`), an explicit antecedent of `UNGUELocalEventHighProb`/`UNGUEGoodHighProb`; it is already covered by paper-delta D383 (T2162b, weak GUE local law) and the prove report (a) has the `N = 2000` GUE sample check (`max‖m_N − m_sc‖ = 0.790 ≤ 0.992` at `η = N^{-1+τs/4}`) as its limit check. Imports are merged modules only (Step1Good, FreeConvStability, Mathlib); no cycle. `gueGoodHighProb_of` (read, `:923-930`) composes S7a at `(κ/2, τs/16, D)` with S7b at `τ = τs/16` by `measure_mono`: no extra premise. No refuted pin and no `UNDensBandRow` is used.

### Registry pre-check (root library built in the audit worktree first)
```
$ lake build RBM3D   (worktree, branch content; root does not yet import the new module)
Build completed successfully (4023 jobs).
axiom audit: 6477 theorems, 2222 definitions, 0 axioms
RBM.Univ.UNGUELocal: 21
premises found by scanning: 126 (borrowed 1, owed 94, structural 25, refuted 6).
registry: 2 borrowed + 145 owed + 81 structural + 7 refuted
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Universality.Step1RegularityGUE; #assert_rbm_axioms)
exit 0
axiom audit: 6495 theorems, 2228 definitions, 0 axioms
RBM.Univ.UNGUELocal: 27
premises found by scanning: 127 (borrowed 1, owed 94, structural 26, refuted 6).
registry: 2 borrowed + 145 owed + 81 structural + 7 refuted
```
Owed count 94/145 unchanged; one new structural premise `Step1LocalEventGUE` (registered by the branch); no unregistered premise. (A first pre-check run against the stale cached `Test/Axioms` olean flagged `Step1LocalEventGUE`; after `lake build RBM3D` rebuilt it, exit 0 as above.)

## 4. Compiled nonempty instances (target 5; read `:942-1049`)
- `inst_guedetHalf_sz0`: `guedetHalf 3 le_rfl sz0 inst_sz0_size_tendsto 1 (1/60) 1 one_pos …` — every deterministic hypothesis discharged (`3 ≤ 3`, `0 < 1`, `0 < 1/60 < 1`, `|1| ≤ 2 − 1`, `0 < 1/960 < (1/60)/8`, size → ∞ from `sz0_tendsto`).
- `inst_guelocalEvent_sz0`, `inst_gueGood_sz0` (`D = 2`), `inst_gueGoodHighProb_of_sz0`: same discharge; `UNGUELocal` kept as the only hypothesis (another gate's owed pin, allowed).
- Nondegeneracy: `inst_event_nonempty_sz0`, `inst_gueGood_nonempty_sz0` (event eventually nonempty, from `P(bad) ≤ N^{-1}, N^{-2} < 1`); `inst_size_zero_sz0`: `N_0 = 2097152`, `L = 4`, `W = 32`; `inst_exponents_sz0` (targets 1a-1c at `1/60, 1/960`, sharpness at `1/480`); `inst_gue_err_pow_sz0` (target 2b at `z = i`, `c = 1`, `σ = 1/60`, on an event point). No `N = 0`, empty index, collapsed window or `False` premise. All compile (section 2 axioms output).

## 5. Build and axioms
```
$ lake build RBM3D.Universality.Step1RegularityGUE   (audit worktree)
✔ [3347/3347] Built RBM3D.Universality.Step1RegularityGUE (9.5s)
Build completed successfully (3347 jobs).
exit 0
$ grep -E "^(warning|error)" build.txt | sed -E 's/^(warning|error): ([^:]+):.*/\1 \2/' | sort | uniq -c
   3 warning RBM3D/Defs/Tail.lean
  22 warning RBM3D/Universality/InjSum.lean
```
Axioms of all 18 public theorems: `[propext, Classical.choice, Quot.sound]` (section 2).

## 6. Paper deltas
- No Lean/paper statement difference introduced: the vocabulary is the internal GUE side of Step 1; the weak GUE local law it rests on is D383 (T2162b), already in `docs/paper-deltas.md:1342`.
- Report candidates: T2220a (portmap dependency row, design only), T2220b (ticket design-table wording `Im m_sc ≥ min κ 1/480` vs the in-file `κ'/12` chain; no statement change). Coverage complete.

## 7. Observations (no verdict effect)
- The instances are eventual (`∀ᶠ n`, DECISIONS §56, the pinned shape); the report states the binding threshold `ln N ≥ 4959.7` (`n+1 ≳ 2·10^119` at `sz0`). The data are concrete and nondegenerate; no witness depends on a large constant being chosen.
- Prove report (b) shows the pre-check failing once before the registry line was added; harmless.
- Not targets (correctly left): `UNInfty1Row'`, GUE translation (UN-14), `UNGUELocal` (owed).

## Verdict
| target | verdict |
|---|---|
| 1a `gue_window`, 1b `gue_window_sharp`, 1c `gue_l32_exponents` | PASS |
| 2a `guelocalEventHighProb`, 2b `gue_err_pow` | PASS |
| 3 `guedetHalf` | PASS |
| 4a `gueGoodHighProb_of`, 4b `gueGoodHighProb` | PASS |
| 5 instances (6 pinned + 4 extra) | PASS |

**T2220: PASS.** No dispatcher sign-off needed. Merge note: union in `Test/Axioms.lean` `structuralProps`; root import added by the hub.
