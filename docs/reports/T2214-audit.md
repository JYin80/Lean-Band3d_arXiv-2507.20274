Auditor model: claude-opus-5-5

# T2214 audit (round 1) — UN-13 `Universality/Step1Band`, branch t/T2214 @ f04dcb7 (merge-base 0bc4633)
Written Mon Oct  5 21:29:16 UTC 2026 (`date -u`). Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2214-audit1` (detached at f04dcb7).

## 1. Diff scope, forbidden tokens
```
$ git diff --stat main...t/T2214
 RBM3D/Universality/Step1Band.lean | 1240 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1240 insertions(+)
$ git diff main...t/T2214 -- RBM3D/Test/Axioms.lean | wc -l
       0
$ grep -nE 'sorry|admit|native_decide|^axiom|@\[implemented_by|extern' RBM3D/Universality/Step1Band.lean
(no output; the only `set_option`s are linter.style.longLine / linter.unusedSectionVars)
$ grep -n '^import' RBM3D/Universality/Step1Band.lean
6:import RBM3D.Universality.Step1Good
7:import RBM3D.Universality.Step1Cond
```
Only the sole writable new file is touched; `Test/Axioms.lean` unchanged (ticket: "no registry line" expected). No merged file or frozen signature touched. Imports as the ticket requires (no `import RBM3D`).

## 2. Build
```
$ lake build RBM3D.Universality.Step1Band      (audit worktree)
... (warnings only, all in upstream files EigenMeasurable/Step1Cond: linter)
Build completed successfully (3362 jobs).
```

## 3. Statements vs the pin (check file section 2), by script
`diff.py`: extracts each `def T2214_<name> : Prop := <body>` from `docs/tickets/checks/T2214-check.lean` and the
`theorem <name> : <body> :=` from the library file, whitespace-normalised, string compare.
```
$ python3 diff.py
step1Band_abs_integral_kPoint_le IDENTICAL
step1Band_kPoint_shift IDENTICAL
step1Band_eventually_forall IDENTICAL
step1Band_gue_count IDENTICAL
step1Band_integral_ouP IDENTICAL
step1Band IDENTICAL
step1Band_row IDENTICAL
inst_step1Band_band IDENTICAL
inst_step1Band_band_one IDENTICAL
inst_rhoSC_one_lt_zero IDENTICAL
```
Elaborated check (scratch `audit.lean` = the check file + `import RBM3D.Universality.Step1Band` + the lines below
+ `#print axioms` + `#assert_rbm_axioms`, run with `lake env lean` in the audit worktree):
```
example : T2214_<name> := <name>    -- one line for each of the 10 pinned names (the Step1BandInst ones qualified)
-- consumer: the owed UN-14 pin UNInfty1Row' (PinsDens.lean:88) specialises to target 3b at E' = 0
example : UNInfty1Row' → T2214_step1Band_row := by
  intro h; unfold T2214_step1Band_row; intro h32 hG d hd c dd sz hA M m E ρ δ hD hT hN k O hO
  obtain ⟨τ₁, h1, h2⟩ := h h32 hG d hd c dd sz hA M m E ρ δ hD hT hN 0 (by norm_num) k O hO
  exact ⟨τ₁, h1, h2⟩
$ lake env lean audit.lean; echo exit=$?
exit=0
```
Reading of 3a against the ticket and `UNInfty1` (`Pins.lean:552`):
- conclusion `UNInfty1 sz M ρ E 0 k O τU` = `Tendsto (∫ kPoint k (O(ρ n •·)) E λ(𝐇_{t*}) d ouP − ∫ kPoint k (O(ρ_sc(0)•·)) 0 λ(GUE) d gueP) → 0`:
  model side at energy `E` dilated by `ρ_n`, GUE side at `E' = 0` dilated by `ρ_sc(0)` — as the ticket's design (`E' = 0`; the translation `0 → E'` is UN-14).
- hypotheses: `UNL32` (borrowed), `UNGUELocal` (owed pin), `3 ≤ d`, `Admissible 𝔠 𝔡`, `UNDens'` (primed, never `UNDens`), `UNTrLocal`,
  `∃ CV₀ ≥ 0, UNNormBound`; `∀ k O, IsTestFun O`; `∀ τU, 0 < τU ≤ 𝔠𝔡`. Quantifier order: fixed data → `k, O` → `τU`, `n` only inside `Tendsto`.
  No `|E| ≤ 2 − κ` (ticket: dropped, density range from `UNDens`). Binders are those of `UNInfty1Row'` minus `∀ E', |E'| < 2` (consumer example above).
- target 3b: `∃ τ₁ > 0` before `∀ τU ≤ τ₁`, proof gives `τ₁ = 𝔠 * 𝔡` (`mul_pos hA.1 hA.2.1`, file `:1129`).
- targets 1a–1d, 2: carrier-free/model-generic as pinned; 1c is stated for a dependent carrier `α : ℕ → Type` as required; 1d has `τs < 1`, `0 ≤ Q`, rate `N^{−3τs/8}`.
Statement verdict: all 10 pinned statements identical to the pin; no strengthening/weakening; no special case passed off as the general target.

## 4. Hidden hypotheses, vacuity, cycles, dependencies
```
$ grep -nE '^(private )?(def|structure|class|instance|abbrev)' RBM3D/Universality/Step1Band.lean
656:private def Step1Band_F ...      (a real-valued function: the conditional GUE functional)
703:private def Step1Band_good ...   (a Set: the event of UNStep1Good', IsRegular32 ∧ ∃ mfc, IsFreeConv32 ∧ ∃ ρ', ...)
```
- No new structure, class or `Prop`-valued def. `UNModel` (`Pins.lean:104`, merged): fields `μ, prob, H, herm, meas` only, no analytic assumption.
- Dependencies (all merged on main): `step1Good'` (`Step1Good.lean:757`, a proved theorem `: UNStep1Good'`, called once at `D = k+1`, file `:1024`),
  `integral_kPoint_ouMat_cond`, `Step1Cond_*`, `un_L32_arith`, `un_admissible_cd_lt_half`, `unDensBandRow'_of_row`, `un_dens'_msc_zero`.
  No cycle: the file imports only `Step1Good`, `Step1Cond`; nothing on main imports it.
- No refuted name is consumed (registry `refutedProps`: `UNStep1Good`, `UNInfty1Row`, `UNStep1GoodC`, `UNCoreC`):
```
$ grep -cE "UNStep1Good[^']|UNInfty1Row[^']|UNStep1GoodC|UNCoreC|UNTrLocalInit|UNModelC|vOUC" RBM3D/Universality/Step1Band.lean
0
```
- External hypothesis `UNL32`: registered borrowed (`Test/Axioms.lean:87`, LSY Thm 2.2, DECISIONS §5). Limit check: the six arithmetic premises
  are discharged in Lean by `un_L32_arith` (needs only `N^{τ/2} ≥ 2`, eventually true); the prove report's (a)(ii) script shows them True at
  `sz0`, `τ = 1/60` from `n = 45` (`ln N = 83.47`); the regularity premises are the `step1Good'` event. Accepted.
- Registry pre-check (same scratch run, `#assert_rbm_axioms` after `import RBM3D` + the new module):
```
axiom audit: 6408 theorems, 2227 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 96, structural 25, refuted 4).
registry: 2 borrowed + 148 owed + 79 structural + 4 refuted; ...
exit=0
```
  Premise and registry counts equal those the prove report gives for the base 0bc4633 (126; 2+148+79+4): no unregistered premise.
- Instance premises kept as hypotheses are all registered, none refuted:
```
UNL32: 87 (borrowed)   UNGUELocal: 183   UNLocAvgBand: 193   UNNormBandRow: 201   UNTrLocalBandRow: 202   UNDensBandRow: 203   (owed)
```

## 5. Compiled nonempty instances (file `:1142-1236`, namespace `RBM.Univ.Step1BandInst`)
| endpoint | instance | data | deterministic hypotheses discharged |
|---|---|---|---|
| `step1Band` (3a) | `inst_step1Band_band` `:1149` | `sz0` (d=3, n=0: N = 2097152), `𝔠=1/6, 𝔡=1/10`, band model, `msc`, `E=0`, `ρ=rhoSC 0`, `δ=1/2`, `k=1`, `bump`, `τU=1/60` | `le_rfl : 3≤3`, `sz0_adm`, `un_dens'_msc_zero`, `rT … 1 one_pos 0 (|0|≤2−1) (1/2) (0<1/2) (1/2≤1/2)`, `bump_testFun`, `0<1/60`, `1/60 ≤ 1/6·1/10` |
| `step1Band` (3a), E ≠ 0 | `inst_step1Band_band_one` `:1163` | as above, `E=1`, `κ=1/2`, `ρ=rhoSC 1`, `δ` from `unDensBandRow'_of_row` | `0<δ` (`hD.1.1`), `δ≤1/4`, `|1|≤2−1/2`, rest as above |
| nondegeneracy | `inst_rhoSC_one_lt_zero` `:1176` | `rhoSC 1 < rhoSC 0` | proved (no hypothesis) |
| `step1Band_row` (3b) | `inst_step1Band_row_band` `:1182` | data of `_band` | same |
| 1a | `inst_step1Band_abs_integral_kPoint_le` `:1195` | GUE on `Idx 3 3 1` (N=27), `k=1`, `bump`, `B=1` | `|bump x| ≤ 1` proved |
| 1b | `inst_step1Band_kPoint_shift` `:1203` | `Fin 2`, `A=1`, `B=0`, `c=1` | `0 = 1 − 1•1` by `simp` |
| 1c | `inst_step1Band_eventually_forall` `:1210` | carrier `Fin (n+1)`, `b n = 0` | both premises proved |
| 1d | `inst_step1Band_gue_count` `:1217` | `sz0`, `τs=1/60`, `k=1`, `bump` | size→∞ from `sz0_adm`, `0<1/60<1`, `bump ≥ 0`; `UNGUELocal` hypothesis |
| 2 | `inst_step1Band_integral_ouP` `:1226` | `sz0`, `n=0`, band model, `τU=1/60`, `E=0`, `k=1`, `bump` | `bump_testFun` |
None uses `N = 0`, an empty index, a collapsed window, a `False` premise or a concrete astronomically large `n` (the 3a/3b conclusions are
eventual `Tendsto` statements; no witness threshold is used). Remaining hypotheses are only `UNL32`, `UNGUELocal` and the band rows (other gates'
pins / the authorized external input), as allowed by CLAUDE.md §4 step 2 and the ticket's "Instances" paragraph. All compile (build §2).

## 6. Axioms
```
$ (in audit.lean) #print axioms <each public declaration>
'RBM.Univ.step1Band_abs_integral_kPoint_le' depends on axioms: [propext, Classical.choice, Quot.sound]
... (identical line for each of step1Band_kPoint_shift, step1Band_eventually_forall, step1Band_gue_count, step1Band_integral_ouP,
     step1Band, step1Band_row, and Step1BandInst.inst_step1Band_band/_band_one/inst_rhoSC_one_lt_zero/_row_band/_gue_count/_integral_ouP)
$ grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' audit.out ; grep 'depends on axioms' audit.out | grep -vc '\[propext, Classical.choice, Quot.sound\]'
13
0
```

## 7. Names (on main, non-Probe)
```
$ for n in …; do grep -rnF "$n" RBM3D RBM3D.lean | grep -v '^RBM3D/Probe/' | wc -l; done
step1Band_abs_integral_kPoint_le=0 step1Band_kPoint_shift=0 step1Band_eventually_forall=0 step1Band_gue_count=0
step1Band_integral_ouP=0 step1Band_row=0 Step1BandInst=0 Step1Band_=0 ;  grep -rnw step1Band … = 0
```
Unpinned helpers are `private` and prefixed `Step1Band_` (§3 (E)); the six extra `inst_*` instances live in `Step1BandInst`.

## 8. Paper deltas
- The paper (`1_2_Intro_model_result.tex:566-581`) proves `Thm: B_Univ` by citing DYYY25 with changed parameters; Step 1 is not stated in it.
  The Lean/paper shape of `(1infyuniv)` (model-side `ρ_n`, abstract `UNModel`, `UNDens'`) is that of the merged pins `UNInfty1`/`UNInfty1Row'`
  (UN-01, UN-01c; DECISIONS §66, D512), not introduced here. This ticket's own differences are proposed in the prove report (d):
  T2214a (UN-11 dependency correction), T2214b (`∃ c C` after `D`; one call at `D = k+1`), T2214d (route: no `ρ_sc(E)` normalisation).
  The `E' = 0` restriction of 3a/3b against `UNInfty1Row'` is the ticket's pinned design (translation is UN-14), stated in the ticket and the
  docstring. Coverage adequate.

## Verdict
| 1a `step1Band_abs_integral_kPoint_le` | PASS |
| 1b `step1Band_kPoint_shift` | PASS |
| 1c `step1Band_eventually_forall` | PASS |
| 1d `step1Band_gue_count` | PASS |
| 2 `step1Band_integral_ouP` | PASS |
| 3a `step1Band` | PASS |
| 3b `step1Band_row` | PASS |
| 4 `inst_step1Band_band`, `inst_step1Band_band_one`, `inst_rhoSC_one_lt_zero` | PASS |
**T2214: PASS.** No dispatcher sign-off needed. Merge note for the hub: `Test/Axioms.lean` unchanged; root import `RBM3D.Universality.Step1Band` to add.
