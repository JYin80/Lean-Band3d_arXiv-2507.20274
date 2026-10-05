Auditor model: claude-opus-5-5

# T2190 audit (round 1) — Mon Oct  5 16:05:58 UTC 2026

Branch `t/T2190` at `75aa08e`, audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2190-audit1` (detached). Ticket `docs/tickets/T2190.md`, pins `docs/tickets/checks/T2190-check.lean` §2.

## 1. Scope of the diff
```
$ git diff --name-status main...t/T2190 ; git log --oneline main..t/T2190
A	RBM3D/Universality/FreeConvRegular.lean
75aa08e T2190: UN-07 Universality/FreeConvRegular (free convolution against a regular reference)
$ grep -nE "sorry|admit|native_decide|^axiom| axiom " RBM3D/Universality/FreeConvRegular.lean | wc -l
0
$ grep -n "^import" RBM3D/Universality/FreeConvRegular.lean
6:import RBM3D.Universality.FreeConvStability
7:import Mathlib.Algebra.Order.Chebyshev
```
Only the sole writable file is added (new module; no existing file, no frozen signature touched; `Test/Axioms.lean` untouched, none expected). Imports: `FreeConvStability` (merged) + Mathlib; no cycle.

## 2. Statements against the pins (script diff, whitespace-normalised)
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2190/diff.py   # each `theorem X :` body vs `def X_stmt : Prop :=` body of the check file
freeConvST_sub_le IDENTICAL modulo Type*->Type | Type* occurrences: 1
freeConvST_norm_sq_le IDENTICAL modulo Type*->Type | Type* occurrences: 1
unDens_freeConvST IDENTICAL modulo Type*->Type | Type* occurrences: 1
freeConv_stable_lip IDENTICAL modulo Type*->Type | Type* occurrences: 1
freeConv_stable_freeConvST IDENTICAL modulo Type*->Type | Type* occurrences: 2
unDens_not_eta_determined IDENTICAL | Type* occurrences: 0
```
Elaboration check (`AuditCheck.lean` = `import RBM3D` + `import RBM3D.Universality.FreeConvRegular` + check-file §2 verbatim + the lines below + `#assert_rbm_axioms`):
```
example : RBM.Univ.T2190Check.freeConvST_sub_le_stmt := RBM.Univ.freeConvST_sub_le
example : RBM.Univ.T2190Check.freeConvST_norm_sq_le_stmt := RBM.Univ.freeConvST_norm_sq_le
example : RBM.Univ.T2190Check.unDens_freeConvST_stmt := RBM.Univ.unDens_freeConvST
example : RBM.Univ.T2190Check.freeConv_stable_lip_stmt := RBM.Univ.freeConv_stable_lip
example : RBM.Univ.T2190Check.freeConv_stable_freeConvST_stmt := RBM.Univ.freeConv_stable_freeConvST
example : RBM.Univ.T2190Check.unDens_not_eta_determined_stmt := RBM.Univ.unDens_not_eta_determined
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2190/AuditCheck.lean ; echo exit $?
exit 0      # (error lines: 0)
```
All six pinned bodies are inhabited by the library theorems (only `Type` → `Type*`, which the ticket allows). The targets are stated outside the `section`s whose `variable` lines (`:74`, `:555`) could add binders; the six theorems have no binder before `:`. No structure-valued hypothesis in any target (the private `FreeConvRegular_Par` structure is internal to the proof, built from the explicit hypotheses at `:1216-1218`).

## 3. Build and axioms
```
$ lake build RBM3D.Universality.FreeConvRegular
✔ [3336/3336] Built RBM3D.Universality.FreeConvRegular (16s)
Build completed successfully (3336 jobs).
exit 0
$ grep -c 'FreeConvRegular.lean.*warning' build.log
0
$ #print axioms … (from AuditCheck.lean)
'RBM.Univ.freeConvST_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.freeConvST_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDens_freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.freeConv_stable_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.freeConv_stable_freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDens_not_eta_determined' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvRegularInst.stable_lip_msc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvRegularInst.stable_freeConvST_uI' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvRegularInst.uI_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
$ #assert_rbm_axioms (registry pre-check, DECISIONS §20 (2))
axiom audit: 5628 theorems, 2026 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
premises found by scanning: 109 (borrowed 1, owed 85, structural 23).
non-vacuity certificates: 0 of 127 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
```
Registry: the file defines no public `Prop`; `#assert_rbm_axioms` with the module imported passes (exit 0 above). No registry line needed, none added.

## 4. Compiled nonempty instances (namespace `RBM.Univ.FreeConvRegularInst`)
```
$ grep -nE "^(example|theorem|def)" RBM3D/Universality/FreeConvRegular.lean | sed -n "/1307/,\$p"
1311:theorem freeConvST_zero_eq_msc {ι : Type*} [Fintype ι] [Nonempty ι] {z : ℂ} (hz : 0 < z.im) :
1328:example : (∀ z : ℂ, 0 < z.im → freeConvST (fun _ : Fin 1 => (0 : ℝ)) 1 z = msc z) ∧
1333:example :
1343:example : (1 / 2 : ℝ) * ‖freeConvST (![-1, 0, 1] : Fin 3 → ℝ) (1 / 2) (Complex.I / 10)‖ ^ 2 ≤ 1 :=
1348:def uI : Fin 2 → ℝ := ![-1 / 10000, 1 / 10000]
1353:theorem uI_lower {z : ℂ} (hre : |z.re| ≤ 1 / 2) (hz : 0 < z.im) (hz10 : z.im ≤ 10) :
1380:example : ∃ ρ : ℕ → ℝ, UNDens (fun _ : ℕ => freeConvST uI 1) 0 ρ (1 / 2) ∧
1394:theorem stable_lip_msc : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧
1424:example : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧ 0 < C₀ ∧
1441:theorem stable_freeConvST_uI : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧
1461:example : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧ 0 < C₀ ∧
1478:example : ∃ (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ), UNDens m 0 ρ (1 / 2) ∧
```
| Target | Instance (line) | Data | Deterministic hypotheses discharged |
|---|---|---|---|
| bridge | `freeConvST_zero_eq_msc` 1311, example 1328 | `Fin 1`, `Fin 2`, `u ≡ 0`, `s = 1` | `0 < Im z` kept as the quantified premise |
| T1 | example 1333 | `Fin 2`, `![-1,1]`, `![-1,1/2]`, `r = 1/2`, `s = 1`, `z = i`, `z' = 1+i` | `0<s`, `|u i - u' i| ≤ r` (`fin_cases`), `Im > 0` |
| T2 | example 1343 | `Fin 3`, `![-1,0,1]`, `s = 1/2`, `z = i/10` | all |
| T3 | example 1380 (+ `uI_lower` 1353) | `u n = uI = ![-1e-4, 1e-4]`, `E = 0`, `δ = 1/2`, `c = 1/20` | `0<δ`, `0<c`, the eventual lower bound `c ≤ Im m` on `|x| ≤ 1/2, 0<η≤10` (proved from T1 vs the zero vector + `un_msc_im_ge`) |
| T4 | `stable_lip_msc` 1394, example 1424 (`Fin 3`) | `mref = msc`, `E₀ = 0`, `A = 0`, `δ = 1/2`, `c = 9/100`, `K = 1`, `Lp = 62`; `t = c₀ > 0`, `ε = c₀/2`, `s = 1 - c₀` | box bounds (`un_msc_im_ge`, `norm_msc_lt_one`), Lipschitz (T1 via bridge, `1/(2c²) ≤ 62`), `|E₀| ≤ A`, `t ≤ c₀`, `ε ≤ c₀`, `s = 1-t` |
| T5 | `stable_freeConvST_uI` 1441, example 1461 (`Fin 3`) | `u = uI`, `E₀ = 0`, `A = 0`, `δ = 1/2`, `c = 1/20`; `t = c₀`, `ε = c₀/2` | box lower bound (`uI_lower`), `|E₀| ≤ A`, `t, ε ≤ c₀`, `s = 1-t` |
| T6 | example 1478 | `h n = 1/(n+1)`, with `un_dens_msc_zero` | `0 < h n`; conclusion `ρ 0 ≠ rhoSC 0` proved |

Not degenerate: nonempty index types (`Fin 1/2/3`), windows `δ = 1/2`, `t = c₀ > 0`, `ε = c₀/2 > 0`, `c > 0`. The only hypothesis left open in the T4/T5 instances is the strip closeness `‖mV v w − σ mref(σ(w+E₀))‖ ≤ ε`, the downstream local-law input that the ticket explicitly allows to stay a hypothesis (DECISIONS §56). Its limit check (TEAM §8 lesson 14) is the prove report (a)(ii-b): sup over 592 strip points `9.68e-10 ≤ c₀ = 7.66e-3` at `N = 2·10^6` quantiles of `μ_u ⊞ sc_1`, failing for `N ≤ 2·10^5` (numerical, not a proof; as the ticket requires, d.1 states that the compiled instance's smaller `c₀` needs larger `N`).

## 5. Paper deltas
- T2190a (finding: merged `UNDens` does not tie `ρ_n` to `m_n` at the local-law heights; target 6 compiled, the inconsistency of `UNStep1Good`/`UNCore` with the band rows explicitly marked "NOT compiled or examined here"): proposed in prove report (d) d.2.
- T2190b (BA Step 1 against `m(·,λ)` carries `C₀(ε + t)`, paper `7_8_light_weight.tex:1835` says "as consequences"): proposed in d.3.
- Targets 1–6 are new mathematics with no paper statement; no other Lean/paper statement difference. Coverage complete.

## 6. Per-target verdicts
| # | Target | Statement = pin | Hidden hyp / vacuity / cycle | Instance | Axioms | Verdict |
|---|---|---|---|---|---|---|
| 1 | `freeConvST_sub_le` | yes (`Type*`) | none | ex. 1333 | std | PASS |
| 2 | `freeConvST_norm_sq_le` | yes (`Type*`) | none | ex. 1343 | std | PASS |
| 3 | `unDens_freeConvST` | yes (`Type*`) | none | ex. 1380 | std | PASS |
| 4 | `freeConv_stable_lip` | yes (`Type*`) | none; closeness hyp. is the pinned external input | `stable_lip_msc`, ex. 1424 | std | PASS |
| 5 | `freeConv_stable_freeConvST` | yes (`Type*`) | as 4 | `stable_freeConvST_uI`, ex. 1461 | std | PASS |
| 6 | `unDens_not_eta_determined` | identical | none | ex. 1478 | std | PASS |

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The constants in prove report (a) Verdicts (`c₁ = min(δ/(4(1+A)), 1/4)`, `c₀ … c₁/(4(K+1))`) differ from the file's (`FreeConvRegular_c₁ = min(…, 1/8)`, `c₀ … c₁/(8(K+1))`, `:1149-1153`); they are existential witnesses, the pinned statements are unchanged. Same for the ticket's suggested `c₀` list (report (a)(ii-c) notes it).
- O2. In the band case `u ≡ 0`, targets 4–5 give `C₀(ε + t)`, weaker than the merged `freeConv_stable_local` (`2ε`); this is the ticket's stated price (T2190b), not a defect.
- O3. Constants of the instances are small (`c₀ ≈ 9.07e-5` at T4, `1.56e-5` at T5, report (a)(ii-c)), so the strip closeness needs very large `N`; it is a hypothesis of the instance, as the ticket prescribes.

## Verdict
T2190: **PASS** (all six targets). No dispatcher sign-off needed for the merge; the D-item T2190a (primed successors of `UNDens`, `UNStep1Good`, `UNCore`) is outside this ticket, as the ticket says.

