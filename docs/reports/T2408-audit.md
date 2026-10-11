Auditor model: claude-opus-5-5

# T2408 audit (round 2), BA-G6a `BA/GreenLocal.lean`. Sun Oct 11 06:07:13 UTC 2026

Inputs: ticket `docs/tickets/T2408.md`; `docs/reports/T2408-prove.md`; round-1 audit (RETURN, D1 only); branch `t/T2408` at
`dd10171` (merge base `1c25de0`, `main` = `1aa96d2`); detached worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2408-audit2`.
Scratch files are in the scratchpad `T2408/` (`T2408/audit2/`). `RBM3D/Probe/T2408Pins.lean` is the 1a probe (not merged). It is used
only as the audited pin text.

**Verdict: PASS** (all targets). The round-1 defect D1 is repaired. No dispatcher sign-off is needed.

## 1. Repair of D1 and diff scope
```
$ git diff 2caa2d7 dd10171 --stat                 # the repair commit only
 RBM3D/Test/Axioms.lean | 1 +
$ git diff 2caa2d7 dd10171 -- RBM3D/BA/GreenLocal.lean | wc -l
0
$ git diff --stat main...t/T2408
 RBM3D.lean                 |    1 +
 RBM3D/BA/GreenLocal.lean   | 1005 ++++
 RBM3D/Probe/T2408Pins.lean |  370 ++++       (1a probe, not merged)
$ git diff main...t/T2408 -- RBM3D/Test/Axioms.lean | wc -l
0
$ git diff main...t/T2408 -- RBM3D.lean | grep '^[+-][^+-]'
+import RBM3D.BA.GreenLocal
$ git grep -n "RBM.BA.BAGbEXPii," t/T2408 main -- RBM3D/Test/Axioms.lean | cut -c1-80
t/T2408:RBM3D/Test/Axioms.lean:193:   `RBM.BA.BAGbEXPii, -- `lem_GbEXP_BA` `(GiiGEX)` event form `1
main:RBM3D/Test/Axioms.lean:193:   `RBM.BA.BAGbEXPii, -- `lem_GbEXP_BA` `(GiiGEX)` event form `1
```
- The owed line `BAGbEXPii` is back (1a-audit F1; supervisor 2254 Q2). The three-dot diff no longer touches `Test/Axioms.lean`.
  So rule (A) step 3 does not bring the file in, and T2401's `BAFAav` line on `main` is safe.
  (`git diff main t/T2408 -- Test/Axioms.lean` shows 2 deletions. These are only `main`'s newer lines and are not part of the branch's change.)
- Every touched file is a sole writable file. No frozen signature is touched. `Step1Boot.lean`, `GreenCore`, `GreenOff` and `GreenStab` are not in the diff.
- `GreenLocal.lean` is byte-identical to round 1 (`2caa2d7`), so the round-1 statement analysis carries over. It is re-checked by script below.

## 2. Statements (probe pin text against the branch theorems; compiled)
`pin.lean` imports `RBM3D.BA.GreenLocal` and copies the probe's pin block (`T2408Pins.lean:41-114`) verbatim into
`namespace AuditT2408`. It then elaborates `example : <X>_pin := <theorem>` for GL1-GL6:
```
example : GreenLocal_floor_sample_pin := fun {d L W} _ _ {G M Mb m κ δ} h1 h2 h3 h4 h5 h6 a => RBM.BA.GreenLocal_floor_sample h1 h2 h3 h4 h5 h6 a
example : baGbEXPii_holds_pin := fun d hd => RBM.BA.baGbEXPii_holds d hd
example : greenLocal_localLaw_pin := fun d hd => RBM.BA.greenLocal_localLaw d hd
example : greenLocal_floor_pin := fun d hd => RBM.BA.greenLocal_floor d hd
example : greenLocal_omega_pin := fun d => RBM.BA.greenLocal_omega d
example : greenLocal_gav_of_fa_pin := fun d hd => RBM.BA.greenLocal_gav_of_fa d hd
$ lake env lean T2408/audit2/pin.lean; echo "pin exit $?"
pin exit 0
$ # GreenLocal_FAav (branch :744-756) vs BAFAav (main GreenMinor3.lean:858-869), name replaced, whitespace-normalised
$ cmp a b && echo "GreenLocal_FAav body == main BAFAav body (whitespace-normalised)"
GreenLocal_FAav body == main BAFAav body (whitespace-normalised)
```
Against the ticket and the paper (`7_8_light_weight.tex:1916-1933`, `lem_GbEXP_BA` (a), `(GiiGEX_BA)`):
- **GL1** `GreenLocal_floor_sample`: deterministic. `M` is block-Kronecker with `M_aa = m`, `κ ≤ ‖m‖`, `δ ≤ κ/2` and `‖G-M‖_max ≤ δ`.
  It gives `W^{-d} ≤ (4/κ²)𝓛_aa`, which is the BA form of the ticket's item (iii) (band `inv_Wd_le_maxLoopPM`). **PASS**
- **GL2** `baGbEXPii_holds (hd : 2 ≤ d) : BAGbEXPii d`. The merged pin `Step1Boot.lean:108` is unchanged. `2 ≤ d` is weaker than the paper's `d ≥ 3` (`T2408b`). **PASS**
- **GL3** `greenLocal_localLaw`: `(initialGT2)` (`STInitialGT2gL`, `Carrier.lean:140`) gives `‖G_t-M‖_max ≺ Ψ`.
  This is the first display of `(GiiGEX_BA)`. The window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` is weakened to `∀ᶠ n, 0 ≤ Ψ n`, so the result is stronger (`T2408a`).
  The fixed parameters come before `∀ᶠ n`. **PASS**
- **GL4** `greenLocal_floor`: `∀ ν>0, ∀ᶠ n, W^{-d} ≤ 4/κ² N^ν Ψ²`. It is the twin of `LoopFloorThm` (constant `T2408d`). **PASS**
- **GL5** `greenLocal_omega`: for `0<ζ≤𝔠ε₀/2`, eventually `N^ζW^{-ε₀} ≤ κ/2`, and `HighProbAt{‖Δ‖_max ≤ N^ζW^{-ε₀}}`.
  This is the `ε₀` handling of T2401 Amend 1 D1. **PASS**
- **GL6** `greenLocal_gav_of_fa`: the FA conclusion `‖W^{-d}Σ_oΣ_{b'}M_{ab'}𝒦‖ ≺ Ψ²` gives `‖L^{(1)}_a - m‖ ≺ Ψ²`.
  It is a conditional wiring, stated as one, with FA as a hypothesis (as target 3 asks). **PASS**
- **Bridges** (target 3). Each is **PASS**.
  - `greenLocal_gii_of_le` gives `BAGiiGEX` at every `0<ε₁≤ε₀`. In particular this is `BAFAav`'s premise at `ε₀/2`.
  - `greenLocal_ibp_premises` gives `GreenLocal_IBPPrem`: hll ∧ `N^ζW^{-ε₀}≤κ/2` eventually ∧ `HighProbAt`, the G5c premises.
  - `greenLocal_gbEXPav_of_fa : GreenLocal_FAav d → BAGbEXPav d`. `GreenLocal_FAav` is textually `main`'s `BAFAav` (above).

Hidden hypotheses, vacuity, cycles:
- No `structure`/`class`/`instance` is declared (the declaration list of `GreenLocal.lean` has only `def`/`theorem`/`example`/private helpers).
- The only conditional premise is `GreenLocal_FAav` (owed by G5b; `BAFAav` is an owed line on `main`). It is visible in `GreenLocal_Wiring`.
- No cycle: the imports are `BA.GreenOff`, `BA.GreenCore`, `BA.GreenStab` and `BA.Step1Boot`, all merged.

## 3. Compiled nonempty instances (`namespace GreenLocalInst`, `:806-1003`)
Data: `d = 3`, `sz0`, `zSeq`, `flow_sz0` (`κ=1/2, ε=1/10, 𝔡=1/10, 𝔠=1/6`), `ε₀ = 1/10`, `Ψ0 = W^{-1}`, `δ0 = N^{1/120}W^{-1/10}`.
- `:816` and `:821`: GL2 and `greenLocal_gii_of_le` at `t ≡ 1/2` (`half_lt_t0`). No hypothesis is left.
- `:826-873`: GL3, GL4, GL5, GL6, the wiring and the G5c bridge at `t ≡ 1/2`. Every deterministic hypothesis is discharged.
  What stays is only `STInitialGT2gL` (the induction's output, another gate's pin) and `hFA` (`BAFAav`, owed by G5b).
- `:879-1002`: one `example` at `t ≡ 0`. It applies GL1 (`:991`), GL3, GL4, GL5 (both parts) and GL6 (`:993-1002`, by script grep) with every hypothesis discharged:
  - `X = 0`, so `G_0 = M` and `hinit0 : STInitialGT2gL … (fun _ => 0) (1/10) Ψ0` is proved;
  - `𝒦 = 0` (`hK0`) discharges the FA premise of GL6;
  - GL1 is applied at `δ = 0` with `κ = 1/2 ≤ ‖m‖`.
- Not degenerate: `N > 0`; the index sets are nonempty; the window `W^{-3/2} ≤ W^{-1} ≤ W^{-1/10}` is nonempty; there is no `False` premise and no astronomically large witness.
**PASS**

## 4. Build and axioms (audit worktree, HEAD `dd10171`)
```
$ lake build RBM3D.BA.GreenLocal; echo "mod exit $?"
✔ [3791/3791] Built RBM3D.BA.GreenLocal (15s)
Build completed successfully (3791 jobs).
mod exit 0
$ lake build RBM3D; echo "full exit $?"          # registry pre-check (#assert_rbm_axioms)
✔ [4213/4216] Built RBM3D.Test.Axioms (3.1s)
info: RBM3D.lean:448:0: axiom audit: 11417 theorems, 3441 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4216 jobs).
full exit 0
$ grep -cE "^(warning|error).*BA/GreenLocal" build_full.out
0
$ lake env lean T2408/audit2/ax.lean
'RBM.BA.GreenLocal_floor_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGbEXPii_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.greenLocal_localLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.greenLocal_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.greenLocal_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.greenLocal_gav_of_fa' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.greenLocal_gii_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.greenLocal_ibp_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.greenLocal_gbEXPav_of_fa' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom| axiom " RBM3D/BA/GreenLocal.lean | wc -l
0
$ lake env lean docs/tickets/checks/T2408-check.lean; echo "check file exit $?"
check file exit 0
$ wc -l < RBM3D/BA/GreenLocal.lean
1005
```
The file is under the 2000-line stop line, so no `GreenLocal2` split is needed.

## 5. Paper deltas
Coverage is complete: every Lean/paper difference has a candidate in the prove report (d)/(d′).
- `T2408a`: GL3 has no window.
- `T2408b`: the `2 ≤ d` guard.
- `T2408c`: the per-sequence `PrecL` form. The second display of `(GiiGEX_BA)` is `BAGavLGEX`, reached through GL6 and the wiring under FA.
- `T2408d`: the floor constant `4/κ²`.
GL1 and GL5 are internal lemmas.

## 6. Observations (no verdict effect)
- O1. The prove report is 298 lines: within CLAUDE.md §6's 300, but above the ticket's ≤ 250. This is report-only.
- O2. Prove report `:130` (section (a), stage 1a) still says "one line retired". This is superseded by `:284`, `:295` and `:298` (the repair, F1). Text only.
- O3. `main` has moved past the merge base. `RBM3D.lean` differs only at the import line, which rule (A) step 4 handles. `Test/Axioms.lean` is not in the three-dot diff.
