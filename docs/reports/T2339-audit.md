Auditor model: claude-opus-5-5

# T2339 audit (round 1): S5-26 `Induction/DuhamelII`, Thu Oct  8 16:43:34 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2339-audit1`, detached at `t/T2339` = `9457596`. Scratch files are in the scratchpad `T2339/` and are not committed.

## 1. Statement against the pin

```
$ sed -n 327,329p RBM3D/Induction/Step5Pins.lean          (merged pin)
def STDuhamelII (d : ℕ) : Prop :=
  STIngR5 d STReg5II (fun sz E s t => STEtermsMidConcl sz E s t →
    STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t)
$ grep -n "def T2339_stDuhamelII_holds" docs/tickets/checks/T2339-check.lean
44:def T2339_stDuhamelII_holds : Prop := ∀ d : ℕ, STDuhamelII d
$ (DuhamelII.lean:923)
theorem stDuhamelII_holds (d : ℕ) : STDuhamelII d := by
```
Check-file equality, run in the audit worktree. The scratch file is the check file's four imports, plus `import RBM3D.Induction.DuhamelII`, plus check sections 1-2, plus the line `example : RBM.Gauss.Sizes.T2339Check.T2339_stDuhamelII_holds := RBM.Gauss.Sizes.stDuhamelII_holds`, plus `#print axioms`:
```
$ lake env lean aud_check.lean 2>&1 | grep -E "axioms|error"; echo exit
'RBM.Gauss.Sizes.stDuhamelII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDuhamelConcl_engineQ1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.duhamelII_path_rem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_duhamelII_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
- **Target 1, `stDuhamelII_holds`.** Its type is the pinned `Prop` itself, checked by definitional equality against the check file. Hypotheses, quantifier order, the regime `STReg5II` (`g²/L^d ≤ 1-t`, `1-s ≤ g²/L²`, `3_5:1939`), `Q = {0}` for mixed signs, `Q = ∅` for equal signs, and the loss `A^{-1/5}·STprof + W^{-D}` (`(zYU2)`) are all the pin's, which is merged on `main`. The prover cannot weaken anything here. The proof picks `𝔠_d = 1/100`, which satisfies the `∃`: `0 < 1/100 ≤ 1/100`.
- **Target 2, `stDuhamelConcl_engineQ1`** (`:863`; the ticket asks only for "shape reported"). Its hypotheses are `hd`, `hκ`, `hε`, `h𝔡`, `STFlow`, `0 ≤ s`, `s < t`, `t ≤ lemT z`, `hReg : STReg5II`, `hCon : STConStInd sz (1/100)`, and `hE`, which is the body of `STEtermsMidConcl` written out (prove report (b), stmts.py listing; checked against the file). Its conclusion is `STDuhamelConcl sz {0} P (STflowE z) s t` for an arbitrary sign class `P`. This is stronger than the mixed conjunct the pin needs. The specialisation used is `P := STSigMixed` (`:927`).
- **Equal-sign conjunct.** This is the merged `stDuhamelConcl_engine` with `STReg5Mid` taken from `STReg5II` (`duhamelII_reg5II_mid`, private) and `hTTT := Or.inr (hReg n).2`, as the ticket's mathematics (1) prescribes.
- **Verdict on statements:** match for both targets.

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|open private|^import|^structure|^class" RBM3D/Induction/DuhamelII.lean
6:import RBM3D.Induction.DuhamelI
7:import RBM3D.Induction.WardII
8:import RBM3D.Induction.IniTermII
25:(`duhamelII_prof_avg`).  The private helpers of `DuhamelI.lean` are reached with `open private`
37:set_option linter.style.longLine false
39:open private duhamelI_drift duhamelI_mart duhamelI_grid duhamelI_tailW_eq duhamelI_rpow_quarter
42:open private emn2Exp2_exists_CR from RBM3D.Induction.EMn2Exp2
209:set_option maxHeartbeats 1000000 in
```
- The file defines no new `structure` or `class` and no `def` that carries a hypothesis. The only premise of the conclusion that is not deterministic is `STEtermsMidConcl` (or `hE`). It is a pin of the pin itself, owed via `STLWT`, and it is not hidden.
- The nine Step 1-4 premises of `STIngR5` are discarded (`_`). That makes the proved statement stronger, not vacuous. `STReg5II` is satisfiable: `szB_reg5II`, and the interior data below.
- No cycle. The imports are merged modules only (`DuhamelI`, `WardII`, `IniTermII`). No target uses `stDuhamelII_holds` or `STDuhamelII`, apart from the final application and the registry.
- No new external hypothesis is introduced, so no limit check is required. The preflight's limit computation for `STConStInd` (W^{-3}B → 0 while (1-t)/(1-s) stays fixed) is in the prove report (a)(ii).

## 3. Compiled nonempty instances

The instances are at `DuhamelII.lean:942-976`, namespace `RBM.Gauss.Step5Inst`. All of them compiled in the build of §4.

| endpoint | instance | data | deterministic hypotheses |
|---|---|---|---|
| `stDuhamelII_holds` | `inst_duhamelII_proved` (`:942`) = `inst_duhamelII (stDuhamelII_holds 3)` | `szB`, `zB`, `s = 15/16`, `t = 31/32`, `d = 3` | `inst_ing5_II` discharges flow, `0≤s<t≤lemT`, `szB_reg5II` and `conStInd_const` |
| `stDuhamelII_holds` | `example` (`:967`) via `inst_ing5` | `s = 19/20`, `t = 31/32`: `1/64 ≤ 1/32 ≤ 1/20 < 1/16` (strictly interior) | all of them discharged by `norm_num`, `simp [szB]`, `conStInd_const` |
| `stDuhamelConcl_engineQ1` | `example` (`:950`) | as in the first row, `P = STSigMixed` | all discharged; `hE` (another gate's pin) stays a hypothesis |
| `stDuhamelConcl_engineQ1` | `example` (`:959`) | interior data `19/20`, `31/32` | all discharged; `hE` stays a hypothesis |

- `InstIng5Concl` (`Step5Pins.lean:539`) keeps only the Step 1-4 pins (`STKbound` … `STLKU`) as premises. These are other gates' pins and are allowed by CLAUDE.md §4 step 2.
- The instance data are not degenerate: `L = 4`, `N > 0`, a nonempty index set, `s < t`, an open window, and `A` with ρ finite.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Induction.DuhamelII 2>&1 | grep -E "^error|warning:.*DuhamelII|Build completed|DuhamelII.lean"
Build completed successfully (3892 jobs).
exit 0
```
Axioms are printed in §1: only `propext`, `Classical.choice`, `Quot.sound`. The grep in §2 finds no `sorry`, `admit`, `native_decide` or `axiom`.

Registry pre-check: a scratch copy of the worktree's `RBM3D.lean` with `import RBM3D.Induction.DuhamelII` inserted after its last `import` line.
```
$ lake env lean aud_registry.lean 2>&1 | head -4
axiom audit: 10228 theorems, 3037 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
exit 0
$ git diff main...t/T2339 --stat
 RBM3D/Induction/DuhamelII.lean | 976 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |   1 -
$ git diff main...t/T2339 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STDuhamelII, -- integrated hierarchy with `Q^{(1)}`, case (ii); S5-01 (T2138, DECISIONS §40: owed)
```
- Only the two sole writable files are touched, and the registry change is exactly the `STDuhamelII` line.
- No merged file or frozen signature is changed. `Step5Pins.lean` and `DuhamelI.lean` are not in the diff.
- File length is 976 lines, under the stop rule of 1900.

## 5. Paper deltas

- **The statement is unchanged from the pin.** The pin's shape (`Q^{(1)}` for mixed signs, no `Q` for equal signs) is already covered: `docs/paper-deltas.md:1279`, D321 (T2134g).
- **Proposed in the prove report (d):**
  - `T2339a` (route): `Q^{(1)}` is applied to the pathwise remainder and averaged. The paper instead uses `(ThetaBcirc_infint)` and `(uwp2-92kj00)`, `3_5:2263-2277`. The conclusion is the same.
  - `T2339b`: `stDuhamelConcl_engineQ1` holds for every sign class, while the paper uses it only for mixed signs. It is a stronger by-product.
  - `T2339c`: the pin carries unused Step 1-4 premises (as T2333c).
- These cover every difference between the Lean and paper statements that this audit found.

## 6. Observations (not RETURN)

1. The ticket says to copy `DuhamelI`'s private helpers under `duhamelII_`. Instead, the file reaches ten of them, plus `emn2Exp2_exists_CR`, with `open private` (`:39-42`). This changes no statement, instance, build or axiom result. The prove report (a′) item 2 and (b) item 5 record the deviation.
2. The `WardII` and `IniTermII` imports are unused. They are kept because the ticket says imports go "exactly as the check". This is harmless.
3. There is one `set_option maxHeartbeats 1000000 in` (`:209`). Precedent: `DuhamelI.lean` has two.
4. `duhamelII_path_rem` is a public helper that the ticket does not pin. Its prefix is the file stem, so it satisfies §3 (E).
5. The branch base is `3f750b6`, and `main` has since gained T2336, which touches only `RBM3D.lean` and other files. The hub adds the root import at merge; the full `lake build` is the hub's job.

## Verdict

- `stDuhamelII_holds`: **PASS**.
- `stDuhamelConcl_engineQ1`: **PASS**.
- Ticket T2339: **PASS**. No dispatcher sign-off is needed.
