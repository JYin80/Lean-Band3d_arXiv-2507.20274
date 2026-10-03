Auditor model: claude-opus-5-5
# T2066 audit, round 1 (Sat Oct  3 19:30:00 UTC 2026)
Branch `t/T2066` at 0685e06 (merge-base 65ccfb3, main 2be5aaf). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2066-audit1` (detached at 0685e06). `S` = scratchpad `T2066/audit`.
Scope: ticket items 1–5 (copy of the probe text, binding to merged names, `STStep2`, registry lines, instances).

## 1. Statement: the copied text against the pin (probe 0362cbc), by script
```
$ git show 0362cbc:RBM3D/Probe/T2039Pins.lean > probe.lean; git show t/T2066:RBM3D/Induction/Step2Defs.lean > s2d.lean
$ (sed -n 248,818p; sed -n 2274,2296p; sed -n 4101,4149p; sed -n 4995,5045p; sed -n 5077,5156p) of probe.lean > probe_ranges.lean
$ sed -n 39,861p s2d.lean > s2d_body.lean; diff -B probe_ranges.lean s2d_body.lean
13c13 / 121c121 / 201c201 / 265c265 / 445c445   (five identical hunks)
< open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
> open RBM RBM.Loop RBM.Path RBM.Gauss
557c557,560   (docstring of STStep2: four added lines naming STStep2Concl)
566,567c569
<             STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧
<               STStep2Decay sz Cd (STflowE z) s t
>             STStep2Concl sz (STflowE z) s t Cd
571a574,582 / 594a606,612 / 643a662,672 / 695a725,737 / 774a817,823
  (only: section-3 heading, `end`/`namespace RBM.Gauss.Sizes`, `open RBM RBM.Loop RBM.Path RBM.Gauss`,
   `section`/`end MatrixN|GridN`, `variable {d : ℕ} (sz : Sizes d)`, blank lines)
```
No other difference: every hypothesis, quantifier, exponent and range of the 88 declarations equals the probe's.
`STScaleOk`/`STScaleAdm` (probe 2274–2296) come from 0362cbc = "T2039: repair audit 1: STScaleAdm/STScaleOk clauses eventually in n" (the repaired form the ticket asks for).

Item 3 (`STStep2`): the only statement change is the conclusion, as ticket item 3 and DECISIONS §28 require.
```
def STStep2 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
            STStep2Concl sz (STflowE z) s t Cd
```
Constants come before the sequence (`∃ Cd 𝔠d` before `∀ sz`). `STNewKLK` (`∃ C δ₀` before `∀ sz n` in `STNewKLKAt`) and `STK2decay` (`∃ C` before `∀ sz n`) have constants that do not depend on `W`, `L` or `ilambda` (T2039 audit O4), and their hypotheses include `0 ≤ u`, `u < 1`.

Item 2 (binding): the probe's §0, §12.1 and `STeeLoop` copies are the same as the merged declarations (script `S/bind.py`):
```
$ python3 bind.py   # each `def` block of probe 1-247, 4740-4790, 4960-4970 vs main:RBM3D/Induction/{Defs,Step34Pins}.lean
29 probe §0/§12.1/STeeLoop defs; identical to main: 29 differ: [] absent on main: []
$ python3 closure.py   # probe-declared names referenced in Step2Defs lines 39-861 but not declared there
probe names referenced in Step2Defs §1-3 but not declared there: 28
  bound to merged (§0/§12.1/STeeLoop copies): 20 ['STAvgU', 'STConStInd', 'STDecay', 'STFlow', 'STGM', 'STGavLGEX', 'STGbEXP', 'STGdecayW', 'STKloop', 'STLK', 'STLocalEntryU', 'STStep1Loop', 'STStep1Weak', 'STStep2Concl', 'STWB', 'STblk', 'STeeLoop', 'STflowE', 'STgexRHS', 'STmaxLoop2']
  other (would be unresolved/rebound): [('STLI', [4911]), ('STksimLK', [4927]), ('STelklk', [4941]), ('STavgErr', [4949]), ('STegt', [4954]), ('STee', [4977]), ('STLIM_seqHflow', [5047]), ('ST_gridMart_of_repN', [5314])]
Step2Defs decls also in probe: 88 of 88
```
The 8 "other" names occur only in docstrings (`grep -n` hits are lines 712–816, all inside `/-- … -/`); the first six are merged in `Step34Pins.lean:107–159`. The only main change since the merge-base in the bound files is the `STEKNonzero` window (`Step34Pins.lean:665`), which this file does not reference (`grep -c STEKNonzero s2d.lean` → 0).
No theorem of §3–§12 was copied. The 11 theorems in the file come from probe §1/§2: `STLM_seqHflow`, `STGMM_seqHflow`, eight `*_measurable`, and `STstopIdx_isStoppingTime`.

## 2. Vacuity, hidden hypotheses, cycles
- None of the pins is a `structure`: all are `def … : Prop`, and every hypothesis is in the signature. `STPsiClass` is a 4-clause data condition, registered structural (§20).
- No cycle: the file imports only `Induction.{Defs,Step34Pins}`, `Kernel.Evolution` and `Path.{Walk,Stop}` (no `RBM3D` root, no probe). It builds without the probe (§4).
- External/owed inputs: the 16 owed pins are hypotheses of the instances, which is allowed (they are other gates' pins). §29 boundary checks were done by the preflight (section (a)(ii)). Pins that stage 1b did not instantiate at `ilambda > L` are covered by preflight arguments and numerics, which the ticket allows ("or a paper argument").

## 3. Compiled nonempty instances (file lines 862–1213; data `sz0`: `L_n = 4(n+1) ≥ 4`, `W_n = (2(n+1))^5 ≥ 32`, `lam_n = (2(n+1))^{-6}`; `z0 = 1/2 + i N^{-4/5}`, `s ≡ 0`, `t ≡ 1/16`)
| target | instance | deterministic hypotheses discharged | left as hypotheses |
|---|---|---|---|
| `STStep2` | `inst_step2` (sz0), `inst_step2_lowg` (sz1, `lam = W^{-3/2+1/10}`) | `STFlow` (`flow_z0/z1`), `0≤s`, `s≤lemT`, `s<t`, `t≤lemT`, `STConStInd` (`conStInd_inst`/`_gen`) | pin, `STLK`, `STDecay`, `STStep1Loop/Weak` |
| `STNewKLK` | `inst_newKLK` (n=0, E=1/2, u=0, D=1, ℓ=0, H=0) | `lam` bounds, `|E|≤2-κ`, Hermitian, `‖G-M‖=0≤δ₀` (`STGMM_zero`) | pin |
| `STContractPt` | `inst_contractPt` (L=3, W=2, H=0, z=i, 𝒜={0}) | Hermitian, `Im z>0`, `M` bound | pin |
| `STLWB`, `STEMn2Poly` | `inst_LWB`, `inst_EMn2Poly` (Ψ=W^{-1}, ε₀=1/20) | `STFlow`, window, `STPsiClass` (`Ψ0_class`) | pin, `STInitialGT2`, `STLWassm` |
| `STLWT`, `STEMn2Exp` | `inst_LWT`, `inst_EMn2Exp` (ℓ≡0) | `STFlow`, window, Ψ-window, ℓ-range | pin, `STInitialGT2`, `STLWassmExp` |
| `STGridMart`, `STGridRepN` | `example` (m=2), `inst_gridRepN` (m=3), `K_n=⌈N^{C_K}⌉≠0` | `STFlow`, window, `K≠0`, `N^{C_K}≤K` | pin |
| `STK2decay` | `inst_K2decay` (n=0, E=1/2, u=0, D=1) | `lam` bounds, `|E|`, `u` | pin |
| `STNetLift2` | `example` | `STFlow`, window | pin, the three `*PT` statements |
| `STScaleExists` | `inst_scaleExists` | `STFlow`, window | pin |
| `STOptL2` | `inst_optL2` | `STFlow`, window, `STConStInd` | pin, `STLK`, Step 1 |
| `STLocalAvgOfL2` | `example` | `STFlow`, window | pin, `STStep1Weak`, `STL2decayPT` |
| `STstopIdx_isStoppingTime` | `inst_stop` (grid 8, `K≡0`, D=1) | all (no hypotheses) | — |
| `STLM_seqHflow`, `STGMM_seqHflow`, `STLM/JhatM/EGtM/EEM/GMM_measurable` | `example`s at sz0, n=0 | all (no hypotheses) | — |
None of the instances uses `N = 0`, an empty index set, a collapsed window (`0 < 1/16`) or a `False` premise. All of them compile (§4).

## 4. Build, axioms, hygiene, diff scope (audit worktree)
```
$ lake build RBM3D.Induction.Step2Defs 2>&1 | tail -1; echo exit $?
Build completed successfully (3716 jobs).                                   exit 0
$ grep -E '^(warning|error)' build.log | sed 's/:[0-9]*:[0-9]*:/:/' | cut -c1-110 | sort | uniq -c   (Step2Defs lines only)
   1 warning: RBM3D/Induction/Step2Defs.lean: `if_true` has been deprecated: Use `ite_true` instead
   2 warning: RBM3D/Induction/Step2Defs.lean: `simp at hc'` is a flexible tactic modifying `hc'`. ...
   (no error lines)
$ lake build RBM3D 2>&1 | tail -1          # worktree root (Step2Defs not yet root-imported)
Build completed successfully (3782 jobs).
$ lake env lean ax.lean   # import RBM3D.Induction.Step2Defs; #print axioms for all 88 def/theorem names of the file
exit 0; lines "[propext, Classical.choice, Quot.sound]": 88; "does not depend on any axioms": 0; other lines: 0
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Induction.Step2Defs; #assert_rbm_axioms  (DECISIONS §20)
precheck exit 0
1:axiom audit: 2184 theorems, 942 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
71:premises found by scanning: 60 (borrowed 2, owed 46, structural 12).
72:registry: 5 borrowed + 59 owed + 27 structural; 31 registered premise(s) carry nothing yet: [...]
$ git diff main...t/T2066 | grep -E '^\+' | grep -cE '\bsorry\b|\badmit\b|native_decide|^\+axiom'
0
$ git diff --stat main...t/T2066
 RBM3D/Induction/Step2Defs.lean | 1213 ++++  RBM3D/Test/Axioms.lean | 19 +-   2 files changed
$ git diff main...t/T2066 -- RBM3D/Test/Axioms.lean | grep -E '^[-+]' | grep -vE '^(\+\+\+|---)' | grep -vE '^\+   `RBM\.'
-   `RBM.Gauss.Sizes.STB45Pin] -- `(y27kasdfg)` (DECISIONS §25)      # re-added with a comma; list lines only
```
The registry lines are the 16 owed names of ticket item 4 / DECISIONS §28 (`STNewKLK` … `STLWassmExp`) plus `STPsiClass` (structural). Only the two sole writable files are touched, and no merged file is modified, so frozen signatures are untouched. `Axioms.lean` on main is unchanged since the merge-base (`git diff --stat 65ccfb3 main -- RBM3D/Test/Axioms.lean` is empty).

## 5. Paper deltas
- The pins carry T2039a–j unchanged (verbatim copy). DECISIONS §28 signs them "numbered at the ST2-01 merge", and the prove report (d).2 cites them.
- New difference: `STStep2` concludes `STStep2Concl` (`STLocalEntryU ∧ STAvgU ∧ STGdecayW`) instead of the three single-charge parts. This is proposed as T2066a in prove report (d).2. Coverage is complete.

## 6. Observations (no statement, instance, build, axiom or delta effect)
- O1. `STLKM_measurable`, `STavgM_measurable` and `STEEkM_measurable` have no instance of their own. They have no hypotheses (only parameters), and they are used inside the instantiated `STJhatM_/STEGtM_/STEEM_measurable` (lines 186, 201, 218).
- O2. The instances for `STGridMart`, `STNetLift2` and `STLocalAvgOfL2` are `example`s, so the in-pin predicates `STGridMart`, `STStep2*PT` and `STL2decayPT` are not scanned premises and are not registered. The registry matches the ticket's list exactly. In the pre-check, `STNetLift2`, `STLocalAvgOfL2` and `STPsiClass` "carry nothing yet" (information only).
- O3. Preflight S2 (TTT2 ratio at `g = .05`, `x = 1`) grows with `L`: 7, 15, 55, 170, 426, 849, 1131, 1308 for `L = 3…128`. That run is not evidence that the `L`-uniform constant of `STNewKLK` holds. This is the open part of ST2-06b/ST2-07 and the DECISIONS §28 risk line; the pin text equals the signed pin.
- O4. Docstrings are not evidence, and some are stale: "`Prop5Decay` (borrowed)" in `STNewKLK`/`STK2decay` (`prop5Decay_holds` is proved; neither pin takes `Prop5Decay` as a hypothesis), and "ratio `0.39`" in `STContractPt`, whereas preflight S3 finds the `3^d` sharp. DECISIONS §28 "`Prop5Decay` borrowed" is stale as well (prove report (d).1).
- O5. The instance helpers `STGMM_zero`, `Ψ0`, `W_ge_one`, `Ψ1_window` and `ℓ0_range` are public, in namespace `RBM.Gauss.Step2DefsInst` (file stem). This follows the precedent of the merged `InductionDefsInst`, and the prove report's clash grep found 0 clashes.

## Verdict
| target | verdict |
|---|---|
| 1. copy of §1, §2, §12 pins, §12.2 vocabulary and the §3–§12 definitions | PASS |
| 2. binding of §0, §12.1 and `STeeLoop` to merged names | PASS |
| 3. `STStep2` concluding `STStep2Concl` | PASS |
| 4. registry lines (16 owed, `STPsiClass` structural), pre-check exit 0 | PASS |
| 5. compiled instances | PASS |
**T2066: PASS.** No dispatcher sign-off is needed. The hub adds `import RBM3D.Induction.Step2Defs` and runs the full build at merge.
