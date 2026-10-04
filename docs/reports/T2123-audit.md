Auditor model: claude-opus-5-5

# T2123 audit (round 1): S1-28 `Green/FlucThreshold` — `date -u`: Sun Oct  4 09:45:16 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2123-audit1`, detached at `58b18a1` (= `t/T2123`); `main` = `45ca385`.
The ticket's check file (`docs/tickets/checks/T2123-check.lean`) only has `#check` lines, with no pinned statement text. The statements are therefore checked against the RBM2D source at `c9a24cf` (ST1-COMMON item 6) and against the ticket's mathematics (the floor `W^{-d/2}`, the debt `hsmall`, and D192 `c = W^{-d}`).

## 1. Build, scope, hygiene
```
$ lake build RBM3D.Green.FlucThreshold ; echo exit $?
Build completed successfully (3343 jobs).
exit 0
$ grep -cE "FlucThreshold.lean.*(error|warning)" build.txt
0
$ git diff --name-only main...t/T2123
RBM3D/Green/FlucThreshold.lean
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Green/FlucThreshold.lean | grep -v "axiom scan"
(no output)
```
The diff touches only a sole writable file (`Test/Axioms.lean` is unchanged, which the ticket allows). No frozen signature is touched: the branch adds one new file.

## 2. Axioms and the registry pre-check (scratch `scratchpad/T2123/audit.lean`: `import RBM3D`, `import RBM3D.Green.FlucThreshold`, `#print axioms`, `#assert_rbm_axioms`)
```
$ lake env lean audit.lean ; exit 0
'RBM.Green.hsmall_of_highProb' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.flucGain_of_localLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.highProbAt_detFlucDelta_of_localLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.measureReal_compl_le_of_polyLo' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.detFlucDelta_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.detFlucDelta_moment_small' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 3873 theorems, 1350 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
```
There is no "premise that no theorem proves" error, so no registry line is needed.

## 3. Statements: script diff against RBM2D `c9a24cf` after renaming R1–R3 (`scratchpad/T2123/sd.py`)
```
$ python3 sd.py
== hsmall_of_highProb identical
== flucGain_of_localLaw DIFF
   replace RBM2D: ℝ))⁻¹ | RBM3D: ℕ) : ℝ) ^ (-(d : ℝ) / 2)
   replace RBM2D: ((sz.W n : ℝ))⁻¹ ^ 2 | RBM3D: (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
```
This matches the prover's whole-file diff (b.5): 36 of 37 public statements are identical after renaming, and 0 RBM2D public declarations were dropped. I found no clash of public names on `main`. For each of the 37 public names I grepped `git grep -nwF <name> main -- 'RBM3D/*.lean'` for a `theorem|def` declaration, and none exists.

The two differences are checked against the ticket:
- **Floor.** `hΨlo : ∀ᶠ n, W^{-d/2} ≤ Ψ n` has exactly the form, and the cast, of the merged pin `FixedTimeFAThm` at `LocalLaw.lean:180` (`((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n`). This is the floor of D213 / `3_5:27`. It is a weaker premise than RBM2D's `W⁻¹ ≤ Ψ` when `W ≥ 1`. No statement in the file needs `W⁻¹`, so the ticket's stop rule is not triggered.
- **Weight conjunct.** The conjunct is `(W^d)⁻¹ ≤ (2(2δ))²`. This is the `hcρ : c ≤ ρ^2` of the merged `integral_norm_flucAvg_pow_le_iter_budget` (`FlucIterGain.lean:827`) at the D192/§30 bounded weight `c = W^{-d}`, which is rule R3 (`W⁻²` → `W^{-d}`). The literal RBM2D form is false at `d = 3` on `sz0`. The file compiles `flucThreshold_literal_false` at `n = 3`.
- **`hsmall_of_highProb`.** Its conclusion is token-equal to the `hsmall` premise of the merged `flucGainUpTo'_goodEvent` (`MinorDiffCond.lean:913-917`) at `ε = condEps (E n) (t n) M (2δ n)`. It holds for every `M K` and eventually in `n`. So the debt of S1-26 is discharged and is not carried as a hypothesis of the endpoint.
- **`hB1`.** `flucGain_of_localLaw` gets `hB1` from `detFlucDelta_moment_small` inside the proof. The endpoint has no premise `hB1` or `hsmall`, and its only random premise is `LocalLawDetSeq`.
- **Quantifier order.** The fixed parameters `sz, E, t, Ψ, a, Kη, θ` come first, then `M K`, then `∀ᶠ n`. `|E n| < 2` and `t n < 1` are stated `∀ n`, as in the RBM2D source and the merged pins.
- **`detFlucControl_floor` / `detFlucDelta_floor_le`.** These use the regularising `(N+4)^{-2}`, which is not a floor on `Ψ`, and they are identical to RBM2D. They are checked at `W^{-d/2}` by the compiled private `flucThreshold_control_eq_psi` (line 733).

## 4. Hidden hypotheses, vacuity, cycles
- `LocalLawDetSeq` (`LocalLaw.lean:104`) is a `def` (`PrecPT` = `PerTimeDomAt`) and appears as an explicit premise. `HighProbAt` (`StochDomAt.lean:82`) is `∀ D > 0, ∀ᶠ l, P(Ξᶜ) ≤ size^{-D}`.
- `PolyLo` and `PolyHi` are `∃ C > 0, ∃ D, ∀ᶠ …` defs and appear as explicit premises of `hsmall_of_highProb`. The endpoint discharges them through `detFlucDelta_polyLo` and `flucThreshold_etaPolyHi_of_lower`.
- No structure fields are added.
- Imports are `Green/{MinorDiffCond,LocalLaw,FlucIterGain}`, all merged. There is no import of `RBM3D` and no cycle.
- The external premise `LocalLawDetSeq` (the output of the merged `localLawDetThm`, owed upstream) has the concrete limit check in prove report (a), at lines 67-68. It is the paper's per-entry local law at `Ψ = W^{-d/2}`. At `n = 0`, `N^{1/64}Ψ` is about 2.4 times the measured rms entry.

## 5. Compiled nonempty instances (in the file; compiled by the build in §1)
```
FlucThreshold.lean:1137  private theorem flucThreshold_inst_flucGain_half
    (hll : LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) flucThresholdPsi) : … :=
  flucGain_of_localLaw sz0 (E := fun _ => 0) (t := fun _ => 1 / 2) (Ψ := flucThresholdPsi)
    (a := 1 / 4) (Kη := 1) (θ := detFlucTheta (1 / 4) 1) sz0_tendsto flucThreshold_inst_hE
    (fun _ => by norm_num) (by norm_num) zero_le_one flucThreshold_inst_theta.1
    flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_eta_half
    flucThreshold_inst_floor flucThreshold_inst_ceiling hll 1 2
FlucThreshold.lean:1094  private theorem flucThreshold_inst_hsmall_half (hll : …) : … :=
  hsmall_of_highProb sz0 … sz0_tendsto flucThreshold_inst_hE (fun _ => by norm_num)
    (detFlucDelta_pos …) flucThreshold_inst_polyLo flucThreshold_inst_polyHi_half
    (flucThreshold_inst_highProb_half hll) 1 2
```
The data are `sz0 : Sizes 3` with `L = 4(n+1)` and `W = (2(n+1))^5` (`N = 2097152` at `n = 0`), `E ≡ 0`, `t ≡ 1/2` (so `η = 1/2`, a positive time where the flow does not collapse), `Ψ = W^{-3/2}` (the floor, with equality), `a = 1/4`, `θ = 1/32`, `M = 1` and `K = 2`.
- Every deterministic hypothesis is discharged by a compiled lemma: the floor, the ceiling `N ≤ W^6`, the `η` input, `θ`, `|E| < 2` and `t < 1`.
- The only kept hypothesis is `LocalLawDetSeq`, the owed pin of another gate, which §4 allows.
- The complementary instances `_flucGain_zero` and `_hsmall_zero` are at `t ≡ 0` with no hypothesis left. They are collapsed (`G = m`), and the file says so.
- `flucThreshold_inst_slice3` compiles `8·1·δ ≤ 1 ∧ 2C_1(2δ)+2δ ≤ 1` at `n = 3`.

## 6. Paper deltas
`T2123a` (prove report (d).6) covers the only two Lean/RBM2D differences: the floor `W^{-d/2}`, which continues D213/T2108a, and the bounded weight `c = W^{-d}`, which continues §30/T2061a. `PolyLo`, `PolyHi`, `detFlucDelta` and `hsmall` are Lean's internal passage from `Ω(t,c)` to the moment bound and change no paper statement. Coverage is complete.

## 7. Observations (no effect on verdict)
- O1. `flucThreshold_literal_false` is compiled only at the slice `n = 3`, as stated in (d).2.
- O2. Prove report (a) uses `a = 1/3` and the Lean instance uses `a = 1/4`. Both are inside the constraint of row 2, and (b.10).6 records the difference.
- O3. The values of `hB1` at `M = 2` (`n ≥ 5476` on `sz0`) are numerical only, as stated in (d).3. No statement depends on them.

## Verdict per target
| target | statement | vacuity / hidden hyp. | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `hsmall_of_highProb` | = RBM2D, = `hsmall` of S1-26 | none | `_hsmall_half` (hll kept), `_hsmall_zero` | ok | n/a | **PASS** |
| `flucGain_of_localLaw` | RBM2D + floor `W^{-d/2}`, weight `W^{-d}` | none | `_flucGain_half` (hll kept), `_flucGain_zero` | ok | T2123a | **PASS** |
| `PolyLo/PolyHi` + closure, `measureReal_compl_le_of_polyLo`, `detFluc*`, `highProbAt_detFlucDelta_of_localLaw` | = RBM2D | none | table (b.6), compiled | ok | n/a | **PASS** |

**Overall: PASS.** No dispatcher sign-off is needed.
