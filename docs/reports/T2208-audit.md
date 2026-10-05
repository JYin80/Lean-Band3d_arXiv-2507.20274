Auditor model: claude-opus-5-5

# T2208 audit (UN-12, `RBM3D/Universality/Step1Good.lean`): round 1

Mon Oct  5 20:07:50 UTC 2026 (`date -u`). Worktree `RBM3D-wt/T2208-audit1` at `48637c5` (= `t/T2208`); `$SP` = scratchpad `T2208/`.

## 1. Diff scope (sole writable files) and frozen files
```
$ git diff --stat main...t/T2208
 RBM3D/Test/Axioms.lean            |   1 -
 RBM3D/Universality/Step1Good.lean | 862 ++++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2208 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Univ.UNStep1Good', -- bulk universality pin, primed successor of the refuted UNStep1Good (T2201, UN-01c: owed; UN-12)
$ git diff --name-only main...t/T2208 -- RBM3D/Universality/PinsDens.lean RBM3D/Universality/Pins.lean \
    RBM3D/Universality/FreeConvRegular.lean RBM3D.lean | wc -l
0
```
Only the two sole writable files; the `Axioms.lean` diff is the one pinned deleted line; the pin text of
`UNStep1Good'` (`PinsDens.lean:73`) is untouched. The new file defines no `def`/`structure`/`class`/`instance`
(declaration grep: only `theorem`/`private theorem`), so no new Prop and no hidden structure field.

## 2. Statements against the ticket's pins (check file section 2)
Text diff (script `$SP/sdiff.py`: body of `def T2208_<name> : Prop :=` vs. `theorem <name> :` up to `:=`;
whitespace collapsed, `Type*` -> `Type`):
```
$ python3 $SP/sdiff.py
identical 12 of 12 : stieltjesN_eq_mV mV_vOU mV_eta_mul_im_mono mV_im_le_inv un_admissible_c_mul_lt_one
  un_admissible_d_le_half un_admissible_cd_lt_half step1Good'_det step1Good' inst_step1Good'_band
  inst_step1Good'_det_band inst_admissible_sz0
different: []
```
Elaboration check `$SP/audit_check.lean`: `import RBM3D.Universality.Step1Good`, check file `:105-224` verbatim,
`example : T2208_<name> := @<name>` (12), `example : UNStep1Good' := RBM.Univ.step1Good'`, 4 auditor examples (§3).
```
$ lake env lean $SP/audit_check.lean 2>&1 | grep -v "depends on axioms"; echo "exit=${pipestatus[1]}"
exit=0
```
Mathematics (ticket "Targets", design table, §29 checklist), read off the pinned text now in the file:
- 3a `step1Good'_det`: fixed `d ≥ 3, 𝔠, 𝔡, sz, Admissible, M, m, E, ρ, δ, UNDens', CV₀ ≥ 0, 0 < τs < 1, τs ≤ 𝔠𝔡`
  before `∃ c C, 0 < c ∧ ∀ᶠ n, ∀ ω` (constants before `∀ᶠ n`, item (6)); `ω`-hypotheses = local law at
  `(ε, τ) = (τs/8, τs/8)` on `|Re z − E| ≤ δ`, `N^{-1+τs/8} ≤ Im z ≤ 1`, and `|λ_i| ≤ N^{CV₀}`; conclusion
  `IsRegular32 … (N^{-1+τs/4}) (N^{-min(τs/4,(1−τs)/3)}) c C (CV₀+1)`, `IsFreeConv32 … (1 − e^{-t*})`, rate
  `N^{-3τs/8}` against `ρ n`: matches the ticket (item (7), "CV = CV₀ + 1", "(2.3)" row). PASS.
- 3b `step1Good'`: type is exactly `UNStep1Good'` (example above; unchanged pin; `∀ τs D`, bad set `≤ N^{-D}`). PASS.
- 1a-1d, 2a-2c identical to pins; 2a-2c give `τs ≤ 𝔠𝔡 < 1/2 < 8/11`, used in 3a (file `:679`). PASS.
- Instances (target 4): identical to pins (section 3). PASS.

## 3. Compiled nonempty instances
In the file (`namespace RBM.Univ.Step1GoodInst`, `:807-858`, read by the auditor):
- `inst_step1Good'_band`: `step1Good'` applied at `d = 3`, `sz0`, `𝔠 = 1/6`, `𝔡 = 1/10`, `sz0_adm`, `UNModel.band sz0`,
  `m = fun _ => msc`, `E = 0`, `ρ = fun _ => rhoSC 0`, `δ = 1/2`, `un_dens'_msc_zero` (merged theorem), the local
  law `rT hLoc 3 le_rfl … 1 one_pos 0 (by norm_num) (1/2) (by norm_num) (by norm_num)` (κ = 1, |0| ≤ 1, δ ≤ κ/2),
  `τs = 1/60`, `D = 1`, all numeric side conditions by `norm_num`. Remaining hypotheses: `UNLocAvgBand`,
  `UNTrLocalBandRow`, `UNNormBandRow` = other gates' owed pins (registry lines below). Nondegenerate. PASS.
- `inst_step1Good'_det_band`: `step1Good'_det` at the same data, `CV₀ = 1`; the `ω`-hypotheses stay (they are the
  event; allowed by ticket). Nondegenerate (`N_n = 2097152(n+1)^18`, window `|Re z| ≤ 1/2`). PASS.
- `inst_admissible_sz0`: 2a-2c applied at `sz0`, `sz0_adm`, `0 < 3`. PASS.
```
$ git grep -n "UNLocAvgBand\|UNTrLocalBandRow\|UNNormBandRow" main -- RBM3D/Test/Axioms.lean | cut -c1-105
RBM3D/Test/Axioms.lean:193:   `RBM.Univ.UNLocAvgBand, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
RBM3D/Test/Axioms.lean:201:   `RBM.Univ.UNNormBandRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
RBM3D/Test/Axioms.lean:202:   `RBM.Univ.UNTrLocalBandRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
```
(not in `refutedProps`; its only `UNStep1Good` entry is the unprimed refuted pin, `:339`).
Auditor examples (compiled in `$SP/audit_check.lean`, exit 0 above) applying 1a-1d at concrete data:
`stieltjesN_eq_mV` at `H = 1 : Matrix (Fin 2) (Fin 2) ℂ`, `z = I`; `mV_eta_mul_im_mono` at `v = ![0,1]`, `x = 0`,
`η = 1 ≤ η' = 2`; `mV_im_le_inv` at `v = ![0,1]`, `x = 0`, `η = 1`; `mV_vOU` at `sz0`, band model, `n = 0`,
`τs = 1/60`, `E = 0`, `w = I`.

## 4. Vacuity, hidden hypotheses, cycles, dependencies
- No new `Prop`/structure; `step1Good'` proves the merged owed pin, it does not assume it (no `UNStep1Good'` in any
  hypothesis; axioms below). Dependencies used, all merged on main: `freeConv_stable_lip` (file `:675`),
  `isFreeConv51_freeConvST`/`freeConvST` (`:644-645`), `un_Bctl_le`/`un_step1_floor` (`:299`), `un_dc_lt_one`
  (`:213`), `tendsto_nhds_unique` (`:643`, `ρ₀ = ρ n`). Targets 1b-1d feed 3a (`Step1Good_mV_affine` `:412`,
  `mV_eta_mul_im_mono` `:531`, `mV_im_le_inv` `:541`).
- The private assembly lemma `Step1Good_at_n` (`:600`) carries `[Nonempty ι]` and the size conditions (E1)-(E9) as
  hypotheses; they are discharged inside `step1Good'_det` (compiled), so no hypothesis leaks to a public statement.
- No new external hypothesis (the pin's hypotheses `UNDens'`, `UNTrLocal`, `UNNormBound` are merged pins); the
  band-form instance discharges `UNDens'` by a merged theorem. Finding T2208b concerns `UNTrLocalInit` (C form),
  not used here: `grep -nE "UNTrLocalInit|ouInit|vOUC" Step1Good.lean` gives no output.
- Helpers: `grep -c "^private theorem"` = 21; of these, not prefixed `Step1Good_`: 0.
Name-clash grep of the 13 public names on `main` (`git grep -nF … main -- RBM3D RBM3D.lean | grep -v Probe | wc -l`):
```
stieltjesN_eq_mV: 0  mV_vOU: 0  mV_eta_mul_im_mono: 0  mV_im_le_inv: 0  un_admissible_c_mul_lt_one: 0
un_admissible_d_le_half: 0  un_admissible_cd_lt_half: 0  step1Good'_det: 0  step1Good': 0  Step1GoodInst: 0
inst_step1Good'_band: 0  inst_step1Good'_det_band: 0  inst_admissible_sz0: 0   prefix Step1Good_ (excl. UNStep1Good_): 0
```

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.Step1Good > $SP/build.log 2>&1; echo "exit=$?"
$ grep -n "Step1Good" $SP/build.log; tail -2 $SP/build.log
93:✔ [3342/3342] Built RBM3D.Universality.Step1Good (11s)
Build completed successfully (3342 jobs).
exit=0
$ grep -nE 'sorry|admit|native_decide|^axiom|maxHeartbeats' RBM3D/Universality/Step1Good.lean; echo "exit=$?"
exit=1
$ lake env lean $SP/audit_check.lean 2>&1 | grep "depends on axioms"
'RBM.Univ.stieltjesN_eq_mV' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mV_vOU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mV_eta_mul_im_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mV_im_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_admissible_c_mul_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_admissible_d_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_admissible_cd_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.step1Good'_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.step1Good'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1GoodInst.inst_step1Good'_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1GoodInst.inst_step1Good'_det_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1GoodInst.inst_admissible_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check (temporary `$SP/precheck.lean` = `import RBM3D`, `import RBM3D.Universality.Step1Good`,
`#assert_rbm_axioms`):
```
$ lake env lean $SP/precheck.lean > $SP/precheck.out 2>&1; echo "exit=$?"
exit=0
$ grep -E "^axiom audit|^premises found|^registry" $SP/precheck.out | cut -c1-120
axiom audit: 6179 theorems, 2166 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 129 (borrowed 1, owed 100, structural 24, refuted 4).
registry: 2 borrowed + 143 owed + 79 structural + 4 refuted; 99 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -c "UNStep1Good'[^C]" $SP/precheck.out
0
```
(The full `lake build` is the hub's at merge.)

## 6. Paper deltas
The 12 statements are the dispatcher's pins verbatim (section 2); `step1Good'` is the merged Lean pin
`UNStep1Good'`, so this ticket introduces no new Lean/paper statement difference. Candidates on record:
T2208a, T2208b (C-form pin defects; ticket "Scope decision", for the supervisor; not targets), T2208c (the
`τ_s < 8/11` constraint, from `Admissible`; proposed in prove report (d)). `grep -n T2208 docs/paper-deltas.md`:
no hits yet (dispatcher appends). Coverage complete.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. Targets 1a-1d have no `example` in the file; the ticket's instance list ("Instances to compile", target 4)
  names only the three instances, and 1a-1d are lemmas consumed by 3a (section 4) whose hypotheses are
  `0 < Im z` / `0 < η ≤ η'`. Auditor examples (section 3) compile at concrete data. Not a RETURN.
- O2. Pre-check theorem count 6179 vs report b.5 6106 (cache copied from main, which has later merges); registry counts agree.
- O3. Report (a) writes `a⁻¹ ≤ √2`, the file uses `a⁻¹ ≤ 2` (recorded in (a′)); statements unaffected.

## Verdict
| target | verdict |
|---|---|
| 1a `stieltjesN_eq_mV`, 1b `mV_vOU`, 1c `mV_eta_mul_im_mono`, 1d `mV_im_le_inv` | PASS |
| 2a `un_admissible_c_mul_lt_one`, 2b `un_admissible_d_le_half`, 2c `un_admissible_cd_lt_half` | PASS |
| 3a `step1Good'_det` | PASS |
| 3b `step1Good'` (`: UNStep1Good'`) | PASS |
| 4 `inst_step1Good'_band`, `inst_step1Good'_det_band`, `inst_admissible_sz0` | PASS |

Overall: **PASS**; no dispatcher sign-off needed (T2208a/b are outside scope, per ticket). Merge note (§20 (3)):
on an `Axioms.lean` list conflict take the union, `UNStep1Good'` staying deleted.
