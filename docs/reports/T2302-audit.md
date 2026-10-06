Auditor model: claude-opus-5-5

# T2302 audit (S3-18a2, `Induction/QEndGrid`, `altGridEndQN`), round 1
`date -u`: Tue Oct  6 15:17:51 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2302-audit1`, detached at `t/T2302` = `67d3d42` (base `2cf288c`; `main` = `4686e08`).
Scratch: `<scratchpad>/T2302/` (`build.out`, `pin.txt`, `file.txt`, `stmt.lean`, `reg_before/after.lean`).

## 1. Scope (`git diff main...t/T2302`)
```
$ git diff --stat main...t/T2302
 RBM3D/Induction/QEndGrid.lean | 2158 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2158 insertions(+)
$ git diff --stat main...t/T2302 -- RBM3D/Test/Axioms.lean RBM3D.lean
(empty)
```
Only the sole writable file; no merged file, no frozen signature, no registry line touched. Imports: `QEndA`, `QBudgetB`, `QGridB`, `NQBudget`, `GridAssemblyN`, `Loop/KLFinal` (all merged; none of `RBM3D`, `NQEndLin`, `NQEndFlow*`, `QtNonzero*`).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.QEndGrid   ; exit 0
⚠ [3865/3865] Built RBM3D.Induction.QEndGrid (22s)        (fresh: olean absent from main's cache)
info: RBM3D/Induction/QEndGrid.lean:2147:0: 'RBM.Ind.altGridEndQN' depends on axioms: [propext, Classical.choice, Quot.sound]
  ... (lines 2148-2158: agCaseI, agWt, window_nondegenerate, window_collapsed, altGrid_instance,
       altGrid_instance_collapsed, lam_patch_instance, lam_patch_values, levels_small/big/crude_instance:
       all [propext, Classical.choice, Quot.sound])
Build completed successfully (3865 jobs).
warnings: only linter.style.longLine (lines 16-30 docstring), no other class
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats|set_option" RBM3D/Induction/QEndGrid.lean
44:set_option linter.style.longLine false
45:set_option linter.unusedSectionVars false
46:set_option linter.unusedVariables false
```
Registry pre-check (`import RBM3D` [+ `import RBM3D.Induction.QEndGrid`] + `#assert_rbm_axioms`, `lake env lean`):
```
before exit 0 ; axiom audit: 8646 theorems, 2828 definitions, 0 axioms in `RBM`
after  exit 0 ; axiom audit: 8669 theorems, 2835 definitions, 0 axioms in `RBM`
$ diff reg_before.out reg_after.out   -> only line 1 differs (no new premise line)
```
(Absolute counts differ from the prove report's 8627/8650 because the copied cache's `RBM3D.olean` is from `main` 4686e08; the delta +23/+7 is identical.)

## 3. Target 3 `altGridEndQN`: statement vs pin
```
$ sed -n '155,190p' docs/tickets/checks/T2302-check.lean | sed 's/^ *//' > pin.txt
$ awk '/^theorem altGridEndQN :/{f=1;next} f&&/:= by$/{sub(/ := by$/,"");print;exit} f' QEndGrid.lean | sed 's/^ *//' > file.txt
$ diff pin.txt file.txt
36d35
<                  (trailing blank line of the check-file block only)
```
Statement script (dispatcher's check file verbatim + `import RBM3D.Induction.QEndGrid` +
`example : RBM.Ind.T2302Check.T2302_altGridEndQN := @RBM.Ind.altGridEndQN` + `#print axioms`):
```
$ lake env lean stmt.lean ; echo $?
'RBM.Ind.altGridEndQN' depends on axioms: [propext, Classical.choice, Quot.sound]
exit: 0      (0 error lines)
```
Hypotheses, quantifier order (fixed data → `m` → levels → `v` → `ε₀`, `D₁` → `∃ ε₁ τ' D' C_K` → `∀ Φc K` → `∀ᶠ n`), the alternating constraint `σ (Fin.last (m+1)) = !σ 0`, the length `k = m+1+1`, the `hY` set at length `m+1` with level `N^{ε₁}X`, the initial hypothesis on `𝒬_s(𝓛−𝒦)_s`, and the right side `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃+X)B_v^k` are the pin verbatim. Not a special case: general `d ≥ 3`, `m ≥ 1`, all `s ≤ v ≤ t`, including the collapsed window (handled in the proof, case (ii)).

Constant dependence (proof lines 1371-1419): `ε₁ = e₂/40`, `τ' = min(ε/4, e₂/(40dm))`, `D' = D''+2` depend on `(d, m, 𝔠, 𝔡, κ, ε₀)` only; `C_K = D₁ + 2Cmax + 8k + 20 + D''` also on `Cmax` from `altGrid_yMomentsMax` (`κ, E, s, v, τ`). The pin places `∃ … C_K` after all of these, and the merged format model does the same (`NQEndLin.lean:1134`, `C_K = D₁ + 2*Cmax + 6*k + 20 + D''`). Consistent with the pin.

## 4. Hidden hypotheses, vacuity, cycles
- The signature has no structure-bundled premise: the good-walk sets (`GoodSetN`, `GoodLinN`, `altYSetN`) and `STQop`, `STLKM`, `Bctl` are merged definitions; `altYSetN` resolves to the merged `RBM.Ind.altYSetN` (statement script above elaborates against the dispatcher's check file).
- Private `structure AltGridArith … : Prop` (`:1188`) is an internal bookkeeping bundle produced by `altGrid_arith` inside the proof (`hA := altGrid_arith …`, `:1415`), not a premise of `altGridEndQN`. Private `altGrid_small` (`:1317`) is the per-`n` case predicate of the level split, decided in the proof.
- `STKbound E` is produced in the proof by `stKbound_holds` (`:1384`), not assumed.
- External/owed inputs: none added; the good-walk and projected-initial hypotheses are antecedents inside the conclusion (S3-18b1's, as the ticket states); the prove report gives a limit check (`H = 0, u = 0`: `0 ≤ N^{ε₁}B_0^k`, report line 49). Registry unchanged (§2).
- Cycle: the new module imports only merged modules; no merged module imports it (`git grep QEndGrid main -- RBM3D RBM3D.lean`: 0 hits).

## 5. Compiled nonempty instances (namespace `RBM.Ind.QEndGridInst`, all compiled in the build of §2)
| ticket item | declaration | data / discharge |
|---|---|---|
| (3) non-collapsed | `altGrid_instance` (`:1958`), `example`s at `m = 1, 2, 3` (`:2027-2033`) | `sz0`, `d = 3`, `κ = 1`, `𝔠 = 1/6`, `τ = 1/2`, `𝔡 = 1/10`, `E ≡ 0`, `s ≡ 0`, `t ≡ v ≡ 1/2`, levels and `Φc ≡ 1`, `ε₀ = 1/10`, `D₁ = 1`, grid `agK C_K = max 1 ⌈N^{C_K}⌉₊`; every premise discharged by a term: `sz0_tendsto`, `sz0_bandwidth`, `sz0_WO`, `agCaseI` (`λ²/L² ≤ 1/16 ≤ 1/2`), `rangeCond_half`, `agWt` (`W ≥ 32`), `agK_ne_zero/low/up`; no hypothesis left |
| (4) collapsed | `altGrid_instance_collapsed` (`:1993`), `example` at `m = 2` | same with `v ≡ 0 = s` (`window_collapsed`: `Δ = 0`) |
| non-degeneracy | `window_nondegenerate` | `s_n = 0 < 1/2 = v_n`, `0 < gridStep` |
| (1) `lam` patch | `lam_patch_instance`, `lam_patch_values` | `STMollifierProps` at `n = 4` for `sz0` (`lam > 0`) and `sz0.withLam 0` (`lam = 0`); delta family `= 1` on a constant label, `= 0` on a non-constant one; equals `QopAlgebra_mollifier` when `lam > 0` |
| (2) level split | `levels_small_instance`, `levels_big_instance`, `levels_crude_instance` | `n = 4` (`N = 8·10^18`), `k = 4`, `u = v = 1/2`: `hMee`, `dDriftLinN ≤ N^{8k+7}`; `N^{k+2} ≤ N^{1/10}N^{2k+2}B_v^k`; crude `‖(𝓛−𝒦)^{(4)}(0)‖ ≤ N^{k+2}` (with `STKbound` from `stKbound_holds`) |
| (5) statement | `example : T2302_altGridEndQN := @altGridEndQN` (`:1947`, private copy) + the auditor's script against the check file (§3) | exit 0 |

The instance unfolds the eventual conclusion at one size index (`Filter.Eventually.exists`) with `P(Gᶜ) ≤ N^{-1}`; `N`, `W`, `L`, `λ` are the moderate `sz0` values, and the only large number is `K ≈ N^{C_K}`, which the pin itself requires. The good-walk and initial antecedents stay inside the conclusion, as the ticket allows ("made non-vacuous in S3-18b1"). Not degenerate.

## 6. Paper deltas
Lean/paper differences of this target and their coverage:
- right side carries `X = XLK(n_−1)` additively → candidate `T2302a`;
- level-free crude fallback for levels `≥ N^{2k+2}` → `T2302b`;
- mollifier family defined at every size index (the `lam` patch) → `T2302c`;
- budget at `ε₀/2`, `N^{ε₀/2} ≥ 3`, shift `D' = D''+2` → `T2302d`;
- the pin's shape (the `hY` set at length `n_−1` as a separate event, C1b `N^{−D_t}`, projected initial hypothesis) → already `D608` (T2294a etc.) and `D604` in `docs/paper-deltas.md`.
All covered.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. Size 2158 lines vs the ticket's hi estimate 1650. The preset cut ("central > 1500: stop at 1a") was not triggered because section (a) gives no size estimate. The prove report discloses this in (b) narrative 5 and (d) open issue (1). This is a process point for the dispatcher. It is not a defect of the deliverable.
- O2. Internal deviations from Design (b)/(d) are disclosed in (b) narrative 3: `ν = N^{ε₁}`, `C₀ = (8k+8)/𝔠`, `C_K` coefficient `8k` (F5), `B_u ≤ 2N` (F6). All are internal and the pin is unchanged.
- O3. Registry counts in the prove report (8627 → 8650) differ in absolute value from this audit's (8646 → 8669) because the `RBM3D.olean` caches differ. The deltas agree.

## 8. Verdict
| target | verdict |
|---|---|
| 1. private helpers §0–§4 (incl. `lam` patch, level split) | PASS (compiled; used by target 3; instances (1), (2)) |
| 2. `altGrid_assembly` (private) | PASS (compiled; exercised through `altGridEndQN`) |
| 3. `altGridEndQN` | PASS: statement = pin (script diff, check-file `example` exit 0); no hidden hypothesis; instances (3)–(5) compiled and nondegenerate; build exit 0; axioms standard; scope = sole writable file; deltas `T2302a–d` proposed |

**Ticket T2302: PASS.** No dispatcher sign-off needed.
