Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 16:53:57 UTC 2026

Sources: probe `git show 7b2b789:RBM3D/Probe/T2134Pins.lean` (line numbers below are probe lines); merged `RBM3D/Induction/Step5Pins.lean`
(`Step5Pins`), `Defs/Params.lean` (`Bparam`, `ellT`), `Induction/Defs.lean` (`STWB`, `STConStInd`), `Induction/Step34Pins.lean` (`szB`, `zB`, `lemT_zB`).

### (i) Exponent table (constants the copied declarations depend on)

| item (probe line) | value | constraint it must satisfy | slack |
|---|---|---|---|
| `st5_prec_mono` (489): `ζ₁ ≤ c ζ₂ ⇒ ξ ≺ ζ₂` | `N^{τ/2}·N^{τ/2} = N^τ` | `c ≤ N^{τ/2}` eventually (`SizeTendsto`) | any fixed `c`: holds once `N ≥ c^{2/τ}` |
| `st5_prec_cover` (507) | two index sets cover `U n` | `Prec` on both pieces gives `Prec` on the union, same `τ` | none needed (exponent `τ` unchanged) |
| `ST_step5_assembly` (523) | endpoint `u = t` of `TimeIcc s t n` | `s n ≤ t n`; strong-estimate index `lam² ≤ 1 - t` carried unchanged | exact (precomposition) |
| `st5_Bctl_ge` (564) | `W^{-d}B_{u,0} ≥ (2A)^{-1}`, `A = ilambda² W^d` | `u < 1`, `1-u ≤ ilambda²` (`(ilambda²+1-u)^{-1} ≥ (2ilambda²)^{-1}`) | factor 2 is sharp at `1-u = ilambda²` |
| `st5_compare_I` (659) loss constant | `4` | `2·A^{-1/5} ≤ 2·2^{1/5}·Bctl^{1/5}` (from `A^{-1} ≤ 2 Bctl`) and `A ≥ 1` | `2·2^{1/5} = 2.2974 ≤ 4`; slack factor `2^{4/5} = 1.74` |
| `st5_compare_I`, profile split (593) | `STprof ≤ STWB·exp(-(r/ℓ_u)^{1/2}) + W^{-d-D}` at `ℓ = L`, `r = zdistInf ≤ L` | `r ≤ L` (so `min r ℓ = r`); `max a b ≤ a + b` for `a,b ≥ 0` | exact |
| `st5_compare_IV` (896) loss constant | `6` | `Bctl ≤ 2(W^d)^{-1}(L^d(1-u))^{-1} ≤ 2·STWB` (uses `1-u ≤ ilambda²/L^d`); `Bctl ≤ 1`; `exp(-1) ≤ exp(-(r/ℓ_u)^{1/2})` with `ℓ_u = L`, `r ≤ L`; `Bctl² ≤ Bctl^{1/5}·Bctl`; `e < 3` | `2e = 5.4366 ≤ 6` (slack 0.563) |
| `st5_Bctl_le_one` (814) | `Bctl ≤ 1` eventually, `u ≤ t_n ≤ lemT z_n` | `(ilambda² W^d)^{-1} ≤ W^{-2𝔡}` (`WO`), `(N(1-u))^{-1} ≤ 16 N^{-ε}` (`1-u ≥ N^{-1+ε}/16`) | eventual in `n`; `W^{2𝔡} ≥ 2`, `N^ε ≥ 32` |
| `ST_step5_caseI_of_pins` (744): `𝔠_d` | `min(c₁, min(c₂, c₃))` | `0 < 𝔠_d ≤ 1/100` (each `c_i ≤ 1/100`) | `min ≤ c₁ ≤ 1/100` |
| `st5_conStInd_mono` (545): `STConStInd` monotone in `𝔠_d` | exponent `c' ≥ min` | `Bctl < 1` and `(Bctl)^{c} ≤ (1-t)/(1-s) < 1` give `Bctl^{c'} ≤ Bctl^{c}` for `c ≤ c'` | `Bctl < 1` from `Bctl^{c} < 1`, `c > 0` |
| `stStep5IV_holds` (1001): `𝔠_d` | `1/100` | `0 < 1/100 ≤ 1/100` | 0 (equality, allowed by `≤ 1/100`) |
| `st5_reg5I_mid` (probe 732-739) | NOT copied | merged `Step5Pins.lean` already has it, same signature (`{sz} (hd : 2 ≤ d)`), same call form `st5_reg5I_mid (by omega) hR` (`3 ≤ d`) | n/a |
| Regime ranges (`Step5Pins` 44-66) | cases (i) `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²`; (iv) `1-t ≤ 1-s ≤ ilambda²/L^d` | `L^2 ≤ L^d` for `L ≥ 1`, `d ≥ 2` (used by `st5_reg5I_mid`, `compare_IV`) | `d = 3`: `L^2 = 16 ≤ 64 = L^3` at `L = 4` |

Copied declarations (probe line, content), all inside `477-1039`:
`st5_prec_mono` 489, `st5_prec_cover` 507, `ST_step5_assembly` 523 (STStep5Concl ⇒ STDecay ∧ STDecayStrong at `t`),
`st5_zeroModeSet_empty` 540, `st5_conStInd_mono` 545, `st5_Bctl_ge` 564, `st5_zdistInf_le` 588, `st5_STprof_le` 593,
`st5_STprof_nonneg` 626, `st5_STAI_nonneg` 631, `st5_t_lt_one` 636, `st5_eventually_A_ge_one` 644, `st5_compare_I` 659,
`st5_prec_of_isEmpty` 724, [`st5_reg5I_mid` 732-739 excluded], `ST_step5_caseI_of_pins` 744, `st5_mE_im_le_one` 803,
`st5_Bctl_le_one` 814, `st5_exp_one_lt_three` 888, `st5_compare_IV` 896, `stStep5IV_holds` 1001.
Instances: `inst_step5I/II/III/IV/IV_proved/inst_step5/inst_assembly` 1819-1855, `inst_skeletonI` 2259-2263.
The probe's `namespace RBM.Gauss.Sizes` is opened at 482 and the range 477-1039 contains no closing `end`; the stage-1b file must close it.
Probe line 470 (`STStep5IV` def) is outside the range and is merged (`Step5Pins` 458).

### (ii) Concrete nondegenerate instance (d = 3, all data of the merged `Step5Pins`/`Step34Pins`)

Data: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `szB`: `L = 4`, `W_n = n+4`, `ilambda = 1`, `zB = 1/2 + i/64`; `szG`: `szB` with `ilambda = 5`;
`sz0`: `L_n = 4(n+1)`, `ilambda_n = (2(n+1))^{-6}`, `(s,t) = (0, 1/16)`. Targets and regimes:
(i) `szB`, `(7/8, 15/16)`; (ii) `szB`, `(15/16, 31/32)`; (iii) `sz0`, `(0, 1/16)`; (iv) `szG`, `(5/8, 3/4)`; `inst_assembly` at (iii) data, `inst_skeletonI` at (i) data.
External hypotheses (`t ≤ lemT z`, `WO`) are checked by the concrete computation below (`lemT z = ‖msc z‖²`, `msc z` the root of `m²+zm+1 = 0`
with `Im m > 0`). The profile comparisons are checked numerically with the exact formulas of `Bparam`, `ellT`, `tailT`, `tailW`, `STprof`, `STWB`
(`ellT = min(max(g/√|1-t|, 1), L)`; `Bparam = (g²+|1-t|)^{-1}(K+1)^{-(d-2)} + (L^d|1-t|)^{-1}`; `r = 0..2`, the range of `zdistInf` on `Z_4^3`).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2143/inst.py`
Output (verbatim):
```
szB (7/8,15/16) {'I': True, 'II': False, 'III': False, 'IV': False, 's_lt_t': True, 't_lt_1': True, 's_ge_0': True}
szB (15/16,31/32) {'I': False, 'II': True, 'III': False, 'IV': False, 's_lt_t': True, 't_lt_1': True, 's_ge_0': True}
szG (5/8,3/4) {'I': False, 'II': False, 'III': False, 'IV': True, 's_lt_t': True, 't_lt_1': True, 's_ge_0': True}
sz0 n=0..9 (0,1/16) III: [True, True, True, True, True, True, True, True, True, True]
lemT(zB)=|m|^2 = 0.9839922868819404 >= 31/32 = 0.96875 True  t values 15/16,31/32,3/4 <= lemT: True
WO szG: True
compare_I  szB n=0..199, u in {7/8,29/32,15/16}, D=1,3: all ok, worst ratio lhs/rhs: (True, 0.5009174594197366) True
compare_IV szG n=0..199, u in {5/8,11/16,3/4}, D=1,3: all ok, worst: (True, 2.687238327703789e-05) True
2^(1/5)=1.1487<=2 ; 2*2^(1/5)=2.2974<=4 ; e=2.7183<3 ; 2e=5.4366<=6
Bctl szG u=3/4, W=4 : 0.001595374381188119  <=1; B_{u,0}W^d>=(2A)^-1: True
```
Reading: case (i) `1/16 ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`; (ii) `1/64 ≤ 1/32 ≤ 1/16 ≤ 1/16`; (iv) `1-t = 1/4 ≤ 1-s = 3/8 ≤ 25/64 = ilambda²/L³`;
(iii) `ilambda_n² ≤ 15/16 = 1-t`. `WO` at `szG`: `W^{-3/2+1/10} ≤ 5 ≤ 𝔡⁻¹ = 10`. `lemT(zB) = 0.98399 ≥ 31/32`, so `t ∈ {3/4, 15/16, 31/32}` are admissible
(`t ≤ lemT z`). Every regime has `N = (WL)^3 ≥ 4096` with `L = 4`, no empty index, `s < t`, `t < 1`.
Case (iv) is a theorem and needs no pin: the instance `inst_step5IV_proved` takes `stStep5IV_holds 3` and only `Cd > 0`.

### Verdicts

- Target 1 (copy of probe 477-1039 minus `st5_reg5I_mid`, `Step5Kit.lean`): PASS. Every constant closes (table), the one needed lemma `st5_reg5I_mid` exists in `Step5Pins` with the same call form,
  and none of the 20 copied names nor the 8 instance names exists in `RBM3D/` outside the probe (grep: count 0 each; `st5_reg5I_mid` count 1 = the merged one).
- Target 2 (instances 1819-1855, `inst_skeletonI`): PASS. The four regimes, `lemT zB ≥ 31/32`, `WO` for `szG`, and the comparisons hold at the concrete data (output above); `inst_ing5*`, `szG`, `szG_reg4`, `szB_reg5I/II`, `sz0_reg5III` are merged in `Step5Pins` (lines 495-588).
- The script diff of the copied text against `7b2b789` is a stage-1b obligation (the file `Step5Kit.lean` does not exist in `/Users/junyin/Lean_proof/RBM3D-wt/T2143` at this time; this stage writes no Lean).

Overall verdict: PASS

## (b) Script output (stage 1b) -- Sun Oct  4 16:58 UTC 2026 (date -u)

Commit `5ac1418` on `t/T2143`; files `RBM3D/Induction/Step5Kit.lean` (new, 640 lines), `RBM3D/Test/Axioms.lean` (+2/-1, registry line only).
Source: T2134 probe `7b2b789` (`RBM3D/Probe/T2134Pins.lean`), no port from RBM1D/RBM2D (no diff-stat).

```
$ lake build RBM3D.Induction.Step5Kit | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3775 jobs).
$ lake env lean RBM3D/Induction/Step5Kit.lean      # no output: no warning, no error
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/Step5Kit.lean    # no output
$ git diff --name-only main...t/T2143
RBM3D/Induction/Step5Kit.lean
RBM3D/Test/Axioms.lean
```

Full build with the root import `import RBM3D.Induction.Step5Kit` added temporarily after the last import line of `RBM3D.lean` (restored afterwards; `git status`: only the two writable files differ). First run, before the registry line:
`error: RBM3D.lean:189:0: axiom audit: 1 premise(s) ... [RBM.Gauss.Sizes.STStep5Concl]`. After the registry line:
```
$ lake build | grep -E "axiom audit|registry:|premises found|Build completed|error|sorry"
info: RBM3D.lean:189:0: axiom audit: 4460 theorems, 1575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 92 (borrowed 0, owed 72, structural 20).
registry: 1 borrowed + 92 owed + 49 structural; 50 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (3890 jobs).
```

Copied text against the probe (script diff, `$P` = `git show 7b2b789:RBM3D/Probe/T2134Pins.lean`; `git show 7b2b789:... | sed -n 477,1039p` equals the local copy of the probe: SAME_AS_GIT):
```
$ diff <(sed -n "33,587p" Step5Kit.lean) <(sed -n '477,731p;740,1039p' $P) && echo EMPTY
EMPTY
$ diff <(sed -n '477,1039p' $P) <(sed -n "33,587p" Step5Kit.lean)
256,263d255   [= probe 732-739: st5_reg5I_mid and the blank line; the only difference]
$ diff <(sed -n "595,630p" Step5Kit.lean) <(sed -n 1819,1854p $P) && echo EMPTY      # instances 1819-1854
EMPTY
$ diff <(sed -n "632,638p" Step5Kit.lean) <(sed -n 2255,2261p $P) && echo EMPTY    # inst_skeletonI
EMPTY
```
The namespace changes `RBM.Gauss.T2134Inst` -> `RBM.Gauss.Step5Inst` and the file header (imports, module docstring, `end`s, namespace/open lines) are the other differences; the probe's `namespace`/`open`/`variable` lines of section 7 are inside the copied range.

Axioms (`#print axioms` of every theorem of the file; namespace prefix `RBM.Gauss.` dropped):
```
'Sizes.st5_prec_mono' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_prec_cover' : [propext, Classical.choice, Quot.sound]
'Sizes.ST_step5_assembly' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_zeroModeSet_empty' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_conStInd_mono' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_Bctl_ge' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_zdistInf_le' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_STprof_le' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_STprof_nonneg' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_STAI_nonneg' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_t_lt_one' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_eventually_A_ge_one' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_compare_I' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_prec_of_isEmpty' : [propext, Classical.choice, Quot.sound]
'Sizes.ST_step5_caseI_of_pins' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_mE_im_le_one' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_Bctl_le_one' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_exp_one_lt_three' : [propext, Classical.choice, Quot.sound]
'Sizes.st5_compare_IV' : [propext, Classical.choice, Quot.sound]
'Sizes.stStep5IV_holds' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_step5I' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_step5II' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_step5III' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_step5IV' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_step5IV_proved' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_step5' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_assembly' : [propext, Classical.choice, Quot.sound]
'Step5Inst.inst_skeletonI' : [propext, Classical.choice, Quot.sound]
```

Statements of the targets, extracted from the file by script (the other `st5_*` comparisons are in the file at lines 96-436):
```
-- Step5Kit.lean:63
theorem st5_prec_cover (hsz : sz.SizeTendsto) {U V₁ V₂ : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (φ₁ : ∀ n, V₁ n → U n) (φ₂ : ∀ n, V₂ n → U n)
    (hcov : ∀ n u, (∃ v, φ₁ n v = u) ∨ (∃ v, φ₂ n v = u))
    (h₁ : sz.Prec (fun n v ω => ξ n (φ₁ n v) ω) (fun n v ω => ζ n (φ₁ n v) ω))
    (h₂ : sz.Prec (fun n v ω => ξ n (φ₂ n v) ω) (fun n v ω => ζ n (φ₂ n v) ω)) : sz.Prec ξ ζ := by
-- Step5Kit.lean:79
theorem ST_step5_assembly {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STStep5Concl sz E s t) :
    STDecay sz E t ∧ STDecayStrong sz E t := by
-- Step5Kit.lean:292
theorem ST_step5_caseI_of_pins (hE : STEtermsMid d) (hD : STDuhamelI d) (hI : STIniTermI d) : STStep5I d := by
-- Step5Kit.lean:549
theorem stStep5IV_holds (d : ℕ) : STStep5IV d := by
-- Step5Kit.lean:598
theorem inst_step5I (h : STStep5I 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
-- Step5Kit.lean:618
theorem inst_step5IV_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) Cd :=
-- Step5Kit.lean:628
theorem inst_assembly (h : STStep5Concl sz0 (STflowE z0) sInst tInst) :
    STDecay sz0 (STflowE z0) tInst ∧ STDecayStrong sz0 (STflowE z0) tInst :=
-- Step5Kit.lean:636
theorem inst_skeletonI (hE : STEtermsMid 3) (hD : STDuhamelI 3) (hI : STIniTermI 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
```

Compiled nonempty instances (all in the file, namespace `RBM.Gauss.Step5Inst`, `d = 3`, the data of the merged `Step5Pins`/`Step34Pins`: `szB`, `szG`, `sz0`, `zB`, `z0`, regimes as in (a)):
`inst_step5IV_proved` = `stStep5IV_holds 3` at `(szG, zB, 5/8, 3/4)`: no pin hypothesis, only `Cd > 0`.
`inst_skeletonI` = `ST_step5_caseI_of_pins` at `(szB, zB, 7/8, 15/16)` (hypotheses: the three ingredient pins `STEtermsMid 3`, `STDuhamelI 3`, `STIniTermI 3`, owed by other gates).
`inst_assembly` = `ST_step5_assembly` at `(sz0, z0, 0, 1/16)` (hypothesis: `STStep5Concl`, the Step-5 conclusion, an unproved pin; `hst : s <= t` discharged by `sz0_hst`).
`inst_step5I/II/III/IV/inst_step5` apply the Step-5 pins at their regimes (pins stay hypotheses, T2138 audit O1).
The deterministic comparisons `st5_*` are exercised by `stStep5IV_holds` and `ST_step5_caseI_of_pins`; the numerical check of (a) covers `st5_compare_I/IV` at the concrete data.

Name-clash grep (script: for each of the 28 theorem names, `git grep -n -w "theorem N\|def N\|lemma N" main -- RBM3D`, outside `Step5Kit.lean`):
```
st5_prec_mono 0; st5_prec_cover 0; ST_step5_assembly 0; st5_zeroModeSet_empty 0; st5_conStInd_mono 0; st5_Bctl_ge 0; st5_zdistInf_le 0;
st5_STprof_le 0; st5_STprof_nonneg 0; st5_STAI_nonneg 0; st5_t_lt_one 0; st5_eventually_A_ge_one 0; st5_compare_I 0; st5_prec_of_isEmpty 0;
ST_step5_caseI_of_pins 0; st5_mE_im_le_one 0; st5_Bctl_le_one 0; st5_exp_one_lt_three 0; st5_compare_IV 0; stStep5IV_holds 0;
inst_step5I 0; inst_step5II 0; inst_step5III 0; inst_step5IV 0; inst_step5IV_proved 0; inst_step5 0; inst_assembly 0; inst_skeletonI 0
```
`st5_reg5I_mid` is not redeclared: `Step5Pins.lean:464` (merged, same signature) is used by `ST_step5_caseI_of_pins` (the copy compiled unchanged).

Narrative:
* The copy is verbatim (empty script diff above), so no statement changed to compile against `main`; all 28 theorems built on the first attempt.
* Registry: `STStep5IV` is proved (`stStep5IV_holds`), not registered; `STStep5I` stays owed (already registered). The registry pre-check (full build with the temporary root import) required one new line: `STStep5Concl` is the hypothesis of `inst_assembly` and was in none of the three lists; it is registered as owed (the uniform Step-5 conclusion, as `STStep2Concl`, DECISIONS §40 class owed). The edit changed the closing `]` of `owedProps` to a `,` on the previous line (a one-line change besides the append).
* The module docstring lines were wrapped; the copied text keeps `set_option linter.style.longLine false` as in `Step5Pins.lean`.

## (c) Verified Mathlib names

No new Mathlib names: the copied text was compiled unchanged against the pinned Mathlib (`lake build` above).

## (d) Open issues and paper-delta candidates

* Class for `STStep5Concl` (owed) is proposed here; the dispatcher may reclassify. Not in the ticket's list (ticket: "append only"): flagged.
* Paper-delta candidates: none new; D315-D324 (DECISIONS §40) cover `tailTD`, the sharp `STNewKLKL` and the registry classes.
* `inst_skeletonII/III` go to S5-03 (ticket).
